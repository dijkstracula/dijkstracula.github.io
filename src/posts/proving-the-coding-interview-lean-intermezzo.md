---
layout: post.njk
title: "Leaning into the Coding Interview: proving equality of different implementations"
date: 2026-01-30T00:00:00-05:00
tags: [post, lean, verification, provingthecodinginterview]
excerpt: "There are lots of different ways to implement Fizzbuzz - how robust is our specification to different implementations (of varying degrees of correctness)?"
draft: true
---

::: tip
_This is part of an ongoing introduction to Lean 4 series_: 
  * [Part one - theorem-proving basics](/posts/proving-the-coding-interview-lean)
  * [Part two - static bounds checks and dependent types](/posts/proving-the-coding-interview-lean-2)
  * [Part three - completing the spec with tactic combinators](/posts/proving-the-coding-interview-lean-3)
  * [Intermezzo - contrasting different implementations](/posts/proving-the-coding-interview-lean-intermezzo]
  * [Part four - proof-carrying code](/posts/proving-the-coding-interview-lean-4)

All previous Proving The Coding Interview posts can be found
[here](/tags/provingthecodinginterview/).
:::

We started this series with a particular implementation of Fizzbuzz, and wrote
our specification around that implementation.  Having a tight coupling made it
easy to relate the two, but a good specification is robust to different
implementations of the same problem.  It wouldn't be good if there wasn't a way
to say, for example, "even though this implementation uses functional idioms
and this other one uses mutable state, they're ultimately always doing the same
thing".

In this lagniappe of a post, I wanted to experiment with different
implementations of Fizzbuzz, with different features of Lean's language and
type system.  By the end of the post, we'll hopefully have an opinion on
whether our specification is appropriately general to the problem!

## What if we'd gotten the implementation wrong?

It's all fine and well if we prove something about an implementation we already
knew was correct.  Let's introduce a bug into `fb_one` and see how our proof
goes awry:

```lean4
def fb_one (i : Nat) :=
    if i % 5 = 0 then FB.Buzz else       -- NEW: This line and the line below
    if i % 15 = 0 then FB.FizzBuzz else  -- it were flipped!
    if i % 3 = 0 then FB.Fizz else
    FB.Num i
...
```

Hopefully you can see what goes wrong here: we'll never print out `FizzBuzz`
because the earlier `i % 5 = 0` check will satisfy cases where `i` is also
divisible by 15.

So what goes wrong when we try and prove our earlier theorem with a broken
implementation?  We'll hit a snag when it comes time to split on all the nested
`if`s:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split
  · 

1 goal
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
⊢ FB.Buzz = FB.FizzBuzz
```

We could, as before, apply `simp` to turn that obviously-false equality into
`False`, and then seeing about doing another proof by contradiction.  The
problem is: we don't have anything in our context that leads to a
contradiction, and so we're stuck!  We simply cannot proceed with proving
this proof.  This makes sense when you consider that the statement we're trying
to prove is fundamentally unsolvable.

You might remember that when we broke our Dafny implementation in a similar way
we got a lovely counterexample back from the solver.  Here we're not so lucky;
we don't get an _error_, per se, so much as just a partial proof that's
impossible to prove.  Just like with pen and paper proofs, you have to think
really hard about whether you've missed a strategy to prove something that's
actually correct, or if you've exhausted all the options proving something
that's ultimately wrong.

## Proving two implementations are equal

You and I might well have arrived at different implementations of our `fb_one`
functions.  Stephen Diehl's superb [From Zero To
One](https://sdiehl.github.io/zero-to-qed/07_control_flow.html#fizzbuzz) page
has a different but probably-equivalent implementation to ours:

```lean4
def fb_one_sdiehl (n : Nat) : String :=
  match n % 3 == 0, n % 5 == 0 with
  | true,  true  => "FizzBuzz"
  | true,  false => "Fizz"
  | false, true  => "Buzz"
  | false, false => toString n

def fb_one_ntaylor (i : Nat) : String :=
  if i % 3 = 0 ∧ i % 5 = 0 then "Fizzbuzz" else
  if i % 5 = 0 then "Buzz" else
  if i % 3 = 0 then "Fizz" else
  Nat.repr i
```

::: margin-note
I'm going back to our original version that returned a String rather than a
`FB`, to simplify the proof and to make the (spoiler alert!) counterexample we
get back more obvious, though you can certainly write your own version that
proves that `toString (fb_one i) = fb_one_sdiehl i`.
:::
It doesn't look all that different to ours - at a quick glance, it uses a
`match` statement instead of our `if`-ladder, and calls `Nat.repr` instead of
using the `ToString` typeclass, but we should be somewhat convinced that no
matter what `Nat` we give it, we'll get the same String returned to us.

In most languages, it doesn't even make sense to ask what two functions being
"equal" means - in C, we could certainly compare a _function pointer_ for
referential equality, but that's as good as we can do statically.  Conceptually
we'd have to "run the functions on all inputs" and manually validate that the
returned values are the same.  (The "two functions are the same if you get the
same output for the same input" is called _function extensionality_, or
sometimes _pointwise equality_.  This notion should be familiar to you if you've
studied how functions are defined in set theory.) But, in the presence of global
mutable state, we'd have to also make sure that those C functions' _side
effects_ are also "equal" (whatever that means??)

Even if we considered non-local mutation out of scope, most languages don't
give us much more robust mechanisms than property-based testing to
(probabilistically) validate statements of equivalence like this.

::: margin-note
It _does_ have the State monad, though.  Stay tuned.
:::
Lean, of course, doesn't have side effects in the way that C does.  And, we've
seen the power that one gains by having a theorem prover write statements about
programs.  It turns out that function extensionality _is_ a notion Lean is
familiar with, and we can write proofs to that effect!

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i --NEW

1 goal
i : ℕ
⊢ fb_one_ntaylor i = fb_one_sdiehl i
```

::: margin-note
Technically I did think of applying
[funext](https://lean-lang.org/doc/reference/latest/The-Type-System/Functions/#funext),
but let's pretend I don't know about that one.
:::
We've heard this song before.  I can't think of anything else to do but
`unfold` our two implementations.

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor --NEW
  unfold fb_one_sdiehl  --NEW

1 goal
i : ℕ
⊢ (if i % 3 = 0 ∧ i % 5 = 0 then "Fizzbuzz" else 
   if i % 5 = 0 then "Buzz" else 
   if i % 3 = 0 then "Fizz" else 
   i.repr) =
  match i % 3 == 0, i % 5 == 0 with
  | true, true => "FizzBuzz"
  | true, false => "Fizz"
  | false, true => "Buzz"
  | false, false => toString i
```

Now's a good time to handle one of our differences: `fb_one_sdiehl` converts
`i` to a string by `Nat.repr` whereas we used `Nat.toString`.  Luckily,
even though those functions are not nominally the same, it's a simple matter
to `have` a theorem that states they are, and `rfl` is enough to prove it.
Then we can rewrite `toString` away using that theorem.

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor
  unfold fb_one_sdiehl
  have repr_eq : toString i = Nat.repr i := by rfl -- NEW
  rw [repr_eq] --NEW

1 goal
i : ℕ
repr_eq : toString i = i.repr
⊢ (if i % 3 = 0 ∧ i % 5 = 0 then "Fizzbuzz" else 
   if i % 5 = 0 then "Buzz" else 
   if i % 3 = 0 then "Fizz" else 
   i.repr) =
  match i % 3 == 0, i % 5 == 0 with
  | true, true => "FizzBuzz"
  | true, false => "Fizz"
  | false, true => "Buzz"
  | false, false => i.repr
```

### `repeat` reapplies a tactic until the goal stops changing

Remember from last time that `split` decomposed the goal into different paths
that the progrma could go down; we used this while proving `mod_15_is_fizzbuzz`.
Our goal here is to keep `split`ting the `if` ladder until we've decomposed all
the code paths into subgoals.  `repeat` is a tactical that will do this for us:
it takes as argument a tactic, and keeps applying it until it reaches a _fixpoint_
(in other words, the goal stops changing.)

This expands out to, after trivial auto-simplification, six subgoals:

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor
  unfold fb_one_sdiehl
  have repr_eq : toString i = Nat.repr i := by rfl
  rw [repr_eq]
  repeat split -- NEW

6 goals
...
case isFalse.isFalse.isTrue
i : ℕ
repr_eq : toString i = i.repr
h✝² : ¬(i % 3 = 0 ∧ i % 5 = 0)
h✝¹ : ¬i % 5 = 0
h✝ : i % 3 = 0
⊢ "Fizz" =
  match i % 3 == 0, i % 5 == 0 with
  | true, true => "FizzBuzz"
  | true, false => "Fizz"
  | false, true => "Buzz"
  | false, false => i.repr

case isFalse.isFalse.isFalse
i : ℕ
repr_eq : toString i = i.repr
h✝² : ¬(i % 3 = 0 ∧ i % 5 = 0)
h✝¹ : ¬i % 5 = 0
h✝ : ¬i % 3 = 0
⊢ i.repr =
  match i % 3 == 0, i % 5 == 0 with
  | true, true => "FizzBuzz"
  | true, false => "Fizz"
  | false, true => "Buzz"
  | false, false => i.repr
```

So far that looks good: we have banished the `if` ladder from our goal, at the
expense of having a bunch of subgoals to prove individually.  Now we need to,
for every subgoal, `repeat split` the _match_ expression away (and, again,
discharging goals that are trivially provable). Recall the `<;>` "xargs"
tactical that will do this for us:

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor
  unfold fb_one_sdiehl
  have repr_eq : toString i = Nat.repr i := by rfl
  rw [repr_eq]
  repeat split <;> repeat split --NEW

20 goals
...
case h_3
i : ℕ
repr_eq : toString i = i.repr
h✝² : ¬(i % 3 = 0 ∧ i % 5 = 0)
h✝¹ : ¬i % 5 = 0
h✝ : ¬i % 3 = 0
x✝¹ x✝ : Bool
heq✝¹ : (i % 3 == 0) = false
heq✝ : (i % 5 == 0) = true
⊢ i.repr = "Buzz"

case h_4
i : ℕ
repr_eq : toString i = i.repr
h✝² : ¬(i % 3 = 0 ∧ i % 5 = 0)
h✝¹ : ¬i % 5 = 0
h✝ : ¬i % 3 = 0
x✝¹ x✝ : Bool
heq✝¹ : (i % 3 == 0) = false
heq✝ : (i % 5 == 0) = false
⊢ i.repr = i.repr
```

Great!  Looks like we have either trivial goals (like in `h_4`) or obvious
contradictions (like in `h_3`) involving modular arithmetic in our proof
context.  We know `lia` can handle both of those situations, so that tactic
should let us prove all our subgoals!  Let's try that and declare victory:

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor
  unfold fb_one_sdiehl
  have repr_eq : toString i = Nat.repr i := by rfl
  rw [repr_eq]
  repeat split <;> repeat split <;> lia --NEW 

unsolved goals
case h_1
i : ℕ
repr_eq : toString i = i.repr
h✝ : i % 3 = 0 ∧ i % 5 = 0
x✝¹ x✝ : Bool
heq✝¹ : (i % 3 == 0) = true
heq✝ : (i % 5 == 0) = true
⊢ "Fizzbuzz" = "FizzBuzz"
```

Wait, why didn't all our goals discharge...?

::: margin-note
If you spotted this difference already, well, good for you.
:::
D'oh!!!  Stephen spelled his string "FizzBuzz", whereas I used a lowercase 'b!

Not a bad reason to model your domain more abstractly (as we did with the `FB`
datatype), to avoid silly irrelevant string differences like this!  Yet another
reason why as an interview problem this is a clasically-bad one.  Does our
choice of capitalisation _really_ matter that much?

(By making this correction in either function, we get to see the final goal
solved and enjoy the "No goals" message in our editor.)

::: note
Interestingly, it seems like Dafny does _not_ support the notion of function
extensionality, so making the equivalent statement in Dafny wouldn't be
possible.  Given that we're free to mutate state in Dafny programs, maybe this
shouldn't come as a surprise to us.  There could well be other factors that
limit extensionality -- maybe there's some aspect of how Dafny's solver models
functions? -- but I'm not sure.  Again, interesting tradeoff between the two
languages, the style of programming they allow, and the second-order effects
of those design choices.
:::


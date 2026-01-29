---
layout: post.njk
title: "Leaning into the Coding Interview: proving equality of different Fuzzbuzzes"
date: 2026-01-30T00:00:00-05:00
tags: [post, lean, verification, provingthecodinginterview]
excerpt: "There are lots of different ways to implement Fizzbuzz but this one is mine - how can we prove different implementations are actually the same, and what does it look like when they're actually not?"
draft: true
---

::: tip
_This is part of an ongoing introduction to Lean 4 series_: 
  * [Part one - theorem-proving basics](/posts/proving-the-coding-interview-lean)
  * [Part two - static bounds checks and dependent types](/posts/proving-the-coding-interview-lean-2)
  * [Part three - completing the spec with tactic combinators](/posts/proving-the-coding-interview-lean-3)
  * [Intermezzo - equality proofs between different Fizzbuzzes](/posts/proving-the-coding-interview-lean-intermezzo)
  * Part four - proof-carrying code

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
theorem fb_one_eq : fb_one_ntaylor = fb_one_sdiehl := by

1 goal
⊢ fb_one_ntaylor = fb_one_sdiehl
```

::: margin-note
In this case, this is equivalent to proving the theorem
` ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i` by `intro i`ing.
:::
Normally we would `intro` any arguments or universally-quantified variables,
but we don't have any here! The `funext` tactic lets us exploit the property of
functional extensionality: giving `funext` the argument `i` introduces `i` as
the argument to the two function calls:
```lean4
theorem fb_one_eq : fb_one_ntaylor = fb_one_sdiehl := by
  funext i -- NEW

1 goal
i : ℕ
⊢ fb_one_ntaylor i = fb_one_sdiehl i 
```

We've heard this song before.  I can't think of anything else to do but
`unfold` our two implementations.

```lean4
theorem fb_one_eq : fb_one_ntaylor = fb_one_sdiehl := by
  funext i
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
theorem fb_one_eq : fb_one_ntaylor = fb_one_sdiehl := by
  funext i
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
theorem fb_one_eq : fb_one_ntaylor = fb_one_sdiehl := by
  funext i
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

::: margin-note
In the next proof, we'll see an arguably superior way of unfolding all `if`s
than chaining together `repeat split`s.
:::
```lean4
theorem fb_one_eq : fb_one_ntaylor = fb_one_sdiehl := by
  funext i
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
theorem fb_one_eq : fb_one_ntaylor = fb_one_sdiehl := by
  funext i
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
D'oh!!!  Stephen spelled his string "Fizzbuzz", whereas I used an uppercase
'B`!

Not a bad reason to model your domain more abstractly (as we did with the `FB`
datatype), to avoid silly irrelevant string differences like this!  Yet another
reason why as an interview problem this is a clasically-bad one.  Does our
choice of capitalisation _really_ matter that much?

(By making this correction in either function, we get to see the final goal
solved and enjoy the "No goals" message in our editor.)

I don't know about you but it feels so amazing to be able to see
`fb_one_ntaylor = fb_one_sdiehl`, a statement over _functions_, successfully
proved!

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

## What about an imperative version?

Back when we were programming in Dafny, we contrasted verifying a traditional
`if`-ladder implementation against one that incrementally builds up the string
to be returned (see [this post](posts/proving-the-coding-interview/), under "A
A verifiable “optimisation”".)  Using Lean's support for monadic stateful
computation, we can write a similar such implementation!

### `do`-notation lets us mimic imperative programming, functionally

If you've read upwards of 20,000 words about a theorem prover, either you 
already know what the State monad is, or you are actively uninterested in
knowing what the State monad is.  If you're in the first camp, you can
skip this subsection, and if you're in the second camp, don't worry, I will
lean on intuition to the point of not explaining what a monad is.

::: margin-note
If you would like to learn how monads _actually_ work, the relevant chapter
in [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/monads.html) does a pretty good job of it.
:::
The point of monads as a datatype is to encode something side-effectful (like
propagating an exception-like error, or performing file IO, or, indeed,
handling mutable state) in a pure language, where normally these things
would be impossible.  The most important way to operate on a monad is by chaining
operations together in a sequence: for a piece of mutable state, those
operations are probably going to involve sequencing modifications to that piece
of mutable state.  (For IO, it might be "read the contents of a file" and
"write out the contents to another file" or something.)

::: margin-note
We'll see shortly that the monad laws are logical propositions that typically
can't be captured in most type systems.  Many libraries in other languages that
define monads use [random
testing](https://chrisphelps.github.io/scala/2016/11/30/Cats-Law-Checking-With-Discipline/)
to make sure their implementations adhere to the monad laws.  But, we have a
proof assistant in Lean!  This means we can write the monad laws down formally
and prove them for all the monads we have in the standard library, or new ones
that we choose to design.
:::
The reason why functional programmers get jazzed about monads is that they
use the same underlying primitive to implement wildly different kinds of
effects.  One wouldn't think that an API for external IO would be shaped the
same way as one for, say, mimicing exceptions, but turns out it is, so long as
your monads all behave properly in a fairly common-sense way (we say a correct
implementation "follows the [monad
laws](https://wiki.haskell.org/index.php?title=Monad_laws)").

Ordinarily, each operation on a monad would be written as a function passed
into the monad. (This is the famous `bind` or `>>=` function, but Elm and
Rust's choice to call it
[`and_then`](https://doc.rust-lang.org/rust-by-example/error/option_unwrap/and_then.html)
instead is in my opinion a way more intuitive description of what's going on).
This can get unwieldy pretty fast if we are easily overwhemed; `do`-notation is
syntactic sugar that lets us forget that all this monad stuff is happening
under the hood, which is exactly the thing we want if you don't want to learn
what a monad actually is.

### Our monadic `fb_one`

OK, here's how I used `do`-notation:  As before, I'll show you the new syntax
first and then explain it.

```lean4
def fb_one_monadic (i : Nat) := Id.run do 
 let mut ret := ""
 if i % 3 = 0 then
   ret := ret ++ "Fizz"
 if i % 5 = 0 then
   ret := ret ++ "Buzz"
 if String.length ret = 0 then
   return Nat.repr i
 return ret

def fb n := Vector.range' 1 n |>.map fb_one_monadic
```

(This was the secret _other_ reason I went back to producing `String`s
directly: we can implicitly build up `FizzBuzz` from overwriting `ret`
twice in a way that we really can't with `FB`s.)

There's a bunch of new syntax here:  

`let mut` is a pretty surprising one for a pure functional language!  This is
syntacic sugar for "please initialize a State monad with the initial value
`""`, and make that value visible in the `do` block under the variable name
`ret`.  (This means that `let mut` isn't syntacially valid outside a `do`
block, sort of how like tactics aren't syntacically valid outside a `by` block.
The big take-home lesson is that if you see a `let mut` in Lean, it better
appear inside a `do` block, and that a State monad is being constructed under
the hood.

Next, of course, `val := expr` "mutates" the value of `val`.  For the purposes
of the State monad, mutations are the operation that gets sequenced, so you can
think of our function is saying is: "start with `ret` being defined as `""`;
_and then_ do the `i % 3` check with conditional mutation; _and then_ do the `i
% 5` check with conditional mutation, _and then_ return the final value
depending on the length of `ret`".

`return` is also a bit of a funny one - we've seen that like good functional
languages, Lean is _expression-based_, so since every expression reduces to
some value, even bodies of functions, it doesn't really make sense to think
about "returning" anything.  Think of it instead as returning the value "out of
the `do` block" instead.  Notice that we can have early `return`s, just like
in a non-functional language.

Lastly, `Id` is the specific monad that we're using to sequence our mutable
computations.  It's not exactly the State monad, but we get the `let mut` and
`return` syntax from it, so we'll use it here instead of the more traditional
State monad (which has more of a getter/setter-like API.  Not bad, just
different, and I wanted to show off `let mut` specifically here.)

### Proving equality, once more

Hopefully you are fairly convinced that this is a very differently-shaped
`fb_one` than either the one we wrote or the one from sdiehl's website.  After
all, we have all these monadic operations hidden behind `do`-notation; is
it realistic to try to prove anything about this implementation and the
original one?

Well, we're gonna try, that's for sure:

```lean4
theorem fb_one_eq : fb_one_ntaylor = fb_one_monadic := by -- TODO

1 goal
⊢ ∀ (i : ℕ), fb_one_ntaylor = fb_one_monadic
```

Let's do the usual thing: `funext` to introduce our arguments, and unfold both
functions:

```lean4
theorem fb_one_eq : fb_one_ntaylor = fb_one_monadic := by
  funext i
  unfold fb_one_ntaylor
  unfold fb_one_monadic
  
1 goal
i : ℕ
⊢ (if i % 3 = 0 ∧ i % 5 = 0 then "FizzBuzz" else 
   if i % 5 = 0 then "Buzz" else 
   if i % 3 = 0 then "Fizz" else 
   i.repr) 
  =
  (have ret := "";
    have __do_jp := fun ret y ↦
      have __do_jp := fun ret y ↦
        have __do_jp := fun y ↦ pure ret;
        if ret.length = 0 then pure i.repr
        else do
          let y ← pure PUnit.unit
          __do_jp y;
      if i % 5 = 0 then
        have ret := ret ++ "Buzz";
        do
        let y ← pure PUnit.unit
        __do_jp ret y
      else do
        let y ← pure PUnit.unit
        __do_jp ret y;
    if i % 3 = 0 then
      have ret := ret ++ "Fizz";
      do
      let y ← pure PUnit.unit
      __do_jp ret y
    else do
      let y ← pure PUnit.unit
      __do_jp ret y).run
```

Oh lord, this is a scary looking goal.  Luckily, this is where well-behaved
monads following the monad laws comes into play: they've been [proven for
us](https://github.com/leanprover/lean4/blob/0e28043ec6749ab227d84b690fbb10375dcf714c/src/Init/Control/Lawful/Basic.lean#L114-L144), and critically, those theorems
have been marked `@[simp]`, so simplifying monadic code _automatically takes
advantage of the monad laws_:

```lean4
theorem fb_one_eq : fb_one_ntaylor = fb_one_monadic := by
  funext i
  unfold fb_one_ntaylor
  unfold fb_one_monadic
  simp --NEW

1 goal
i : ℕ
⊢ (if i % 3 = 0 ∧ i % 5 = 0 then "FizzBuzz" else 
   if i % 5 = 0 then "Buzz" else 
   if i % 3 = 0 then "Fizz" else 
   i.repr) =
  (if i % 3 = 0 then
      if i % 5 = 0 then 
        if "FizzBuzz".length = 0 then pure i.repr else 
        pure "FizzBuzz"
      else if "Fizz".length = 0 then pure i.repr else 
      pure "Fizz" else 
   if i % 5 = 0 then if "Buzz".length = 0 then pure i.repr else pure "Buzz" else 
   pure i.repr).run
```

OK, that looks _a lot_ more reasonable.  There's still a bunch of `pure` and
`.run` calls which we haven't defined but are probably related to monads somehow,
but we've got the body of each function on either side of an equality, which was
all but the home stretch last time we proved functional equality.

### A quick diversion into a proof about the empty string

Before we go down this road, though, I want to write one quick lemma that
will be useful to us:  We have a lot of `"...".length = 0` checks owing to the 
potential "should we return `i.repr`" branch.  We know that those have to be false
because only the empty string has length zero, and none of those do.  Let's write
a lemma to help Lean simplify this down further:

```lean4
@[simp]
lemma s_empty_len : ∀ (s : String), s.length = 0 ↔ s = "" := by --TODO

1 goal
⊢ ∀ (s : String), s.length = 0 ↔ s = ""
```

Remember way back in the first Lean post, we unfolded the definition of
`List.length` and saw that it was recursively defined.  Let's do the same here
with `String.length`:

```lean4
@[simp]
lemma s_empty_len : ∀ (s : String), s.length = 0 ↔ s = "" := by
  intros s --NEW
  unfold String.length --NEW

1 goal
s : String
⊢ s.toList.length = 0 ↔ s = ""
```

Hm, so `String.length` is implemented _in terms of `List.length`.  I'm not
convinced that's the choice _I_ would have made, but that's fine - in fact,
reducing the problem to stating "only the empty `List` has length 0" might
actually be good for us!  Indeed, we just needed to do some cheeky rewrites
and we're good to go.

```lean4
@[simp]
lemma s_empty_len : ∀ (s : String), s.length = 0 ↔ s = "" := by
  intros s
  unfold String.length 
  rw [List.length_eq_zero_iff, String.toList_eq_nil_iff] --NEW

Goals accomplished!
```

Since we've marked this lemma as `@[simp]`, once we've proven it, we can see
that Lean automatically makes use of it in our main theorem:

```lean4
theorem fb_one_eq : fb_one_ntaylor = fb_one_monadic := by
  funext i
  unfold fb_one_ntaylor
  unfold fb_one_monadic
  simp

1 goal
i : ℕ
⊢ (if i % 3 = 0 ∧ i % 5 = 0 then "FizzBuzz" else 
   if i % 5 = 0 then "Buzz" else 
   if i % 3 = 0 then "Fizz" else 
   i.repr) 
  =
  (if i % 3 = 0 then 
    if i % 5 = 0 then pure "FizzBuzz" else pure "Fizz" else 
   if i % 5 = 0 then pure "Buzz" else 
   pure i.repr).run
```

Fantastic!  We've banished all those unnecessary `if "...".length = 0 then
i.repr` checks with a carefully-chosen lemma which we taught `simp` about.

### The home stretch towards discharging the proof

We'll proceed the same way we did before: we'll repeatedly unfold the left and
right-hand side's `if` expressions into subgoals, throwing away the ones that
are trivially solvable (or obviously contradictory).

In the last proof, we composed multiple `repeat split` with the `<;>` tactical.
Some of you asked why we needed `repeat split <;> repeat split` - after all,
shouldn't one occurrence keep splitting until we reach a fixpoint?  The reason
is that `split` only operates on the _current subgoal_, so we keep splitting
until we reach a fixpoint for the first subgoal, but all the subsequent ones
may still have `if`s to split up.

Really, the thing we want to do is "keep splitting on every subgoal until every
subgoal reaches a fixpoint".  `repeat all_goals split` will do just this for us!

```lean4
theorem fb_one_eq : fb_one_ntaylor = fb_one_monadic := by
  funext i
  unfold fb_one_ntaylor
  unfold fb_one_monadic
  simp
  repeat all_goals split

8 goals

case h.isTrue.isTrue.isTrue
i : Nat
h✝² : i % 3 = 0 ∧ i % 5 = 0
h✝¹ : i % 3 = 0
h✝ : i % 5 = 0
⊢ "FizzBuzz" = (pure "FizzBuzz").run

case h.isTrue.isTrue.isFalse
i : Nat
h✝² : i % 3 = 0 ∧ i % 5 = 0
h✝¹ : i % 3 = 0
h✝ : ¬i % 5 = 0
⊢ "FizzBuzz" = (pure "Fizz").run
...
```

The left hand side of these equalities is the returned value from our plain vanilla `if`,
and the right hand side is from the monadic one.  

I intentionally did not want to have to explain what the monad laws guarantee,
but you can think of `pure` as "puts a value into the monad" and `run` is
"extracts a value out from the monad".  It shouldn't surprise us that "putting
a value and then taking it right out again leaves us the original value. And
there's a
[proof](https://github.com/leanprover/lean4/blob/5b0b365406a713fba68b5e817c9f852174ad0b18/src/Init/Control/Lawful/Basic.lean#L253)
of that!

::: note
An optional diversion for the mathematically-curious:

`pure : α → M α` is the monadic _unit_, the neutral operation that just embeds
a value without transforming it.  The type signature for the Monad typeclass
guarantees that this function will exist for every monad, and the monad laws
constrain its behaviour so that `pure` is "nicely-behaved".  An example of a
"badly-behaved" monad whose `pure` typechecks, but violates the monad laws,
would be a `Option` whose `pure` just discards the value and always produces a
`None`, rather than a `Some x`.  (We'd say that this unit violates the _left
identity_ law.)

By contrast, `run` is the _interpreter_ or sometimes the _eliminator_ of the
monad.  It isn't actually defined in terms of the monad laws because its type
signature really depends on what monad we're talking about: 

"running" an IO monad means asking the language runtime and the operating
system to read a file or whatever, so we might have the type signature `IO.run
: IO α → α`.  Running the State monad by comparison would return the final
computation (of type `α`) along with the final value of the piece of state (of
type `s`), so we'd have a pair of values returned in `State.run : State s α → s
→ (α × s)`.

It also doesn't make sense for every monad to have a "run" - what should some
hypothetical `List.run : List α → α` return?  An empty list has no `α` to
return at all, and a list with more than one element has a _choice_ of which
one to return...
:::

```
theorem fb_one_eq : fb_one_ntaylor = fb_one_monadic := by
  funext i
  unfold fb_one_ntaylor
  unfold fb_one_monadic
  simp
  repeat all_goals split
  all_goals rw [Id.run_pure] --NEW

4 goals
case h.isTrue.isTrue.isFalse
i : Nat
h✝² : i % 3 = 0 ∧ i % 5 = 0
h✝¹ : i % 3 = 0
h✝ : ¬i % 5 = 0
⊢ "FizzBuzz" = "Fizz"

case h.isTrue.isFalse.isTrue
i : Nat
h✝² : i % 3 = 0 ∧ i % 5 = 0
h✝¹ : ¬i % 3 = 0
h✝ : i % 5 = 0
⊢ "FizzBuzz" = "Buzz"
```

::: margin-note
If we wanted to use `<;>` on the same line as the `repeat`, we'd have to wrap
the latter in parentheses to ensure correct order of operations, e.g. `(repeat
all_goals split) <;> rw [Id.run_pure]`.
:::
Rewriting with this theorem transforms, say, `"FizzBuzz" = (pure "FizzBuzz").run`,
into `"FizzBuzz" = "FizzBuzz"` and then immediately discharges it, leaving us only
with the contradictory goals.  We know `lia` will do the job there.

```
theorem fb_one_eq : fb_one_ntaylor = fb_one_monadic := by
  funext i
  unfold fb_one_ntaylor
  unfold fb_one_monadic
  simp
  repeat all_goals split
  all_goals rw [Id.run_pure] <;> lia -- NEW

0 goals
Goals accomplished!
```

As cool as `fb_one_ntaylor = fb_one_sdiehl` was, this one feels even cooler.
(Your turn: given the two proofs we wrote today, prove that `fb_one_sdiehl` is
equal to the monadic version - the proof should be super-short.)

## Next time...

OK, so we're going to return next time to our original implementation, which
returns our `FB` custom datatype and the specification we wrote with our custom
tactic.

We found our specification ended up being pretty tedious, though, because we
had a bunch of work to verify that, in essence, we were constructing valid `FB`
values in the right setting.  Next time, we're going to learn a bunch more
about implemeting our own _dependently-typed_ `FB` and see how leaning on the
type system in the _implementation_ makes the _specification_ less difficult to
write.  See you then.

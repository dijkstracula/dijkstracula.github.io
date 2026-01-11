---
layout: post.njk
title: "Leaning into the Coding Interview 3: completing our spec with tacticals"
date: 2026-01-30T00:00:00-05:00
tags: [post, lean, verification, provingthecodinginterview]
excerpt: "Time to actually write our end-to-end specification!"
draft: true
---

::: tip
_This is part of an ongoing introduction to Lean 4 series_: 
  * [Part one - theorem-proving basics](/posts/proving-the-coding-interview-lean)
  * [Part two - static bounds checks and dependent types](/posts/proving-the-coding-interview-lean-2)
  * [Part three - completing the spec with tactics combinators](/posts/proving-the-coding-interview-lean-3).
  * Part four - certified programming with proof carrying code

All previous Proving The Coding Interview posts can be found
[here](http://localhost:8080/tags/provingthecodinginterview/).
:::

## Welcome back!

Last time, we got our dependently-typed `fizzbuzz` implementation to a point
where we felt ready to prove our problem specifications:

```lean4
import Mathlib.Data.Nat.Basic

-- implementation

inductive FB : Type where
  | Fizz
  | Buzz
  | FizzBuzz
  | Num (i : Nat)

instance : ToString FB where
  toString fb := match fb with
    | .Fizz => "Fizz"
    | .Buzz => "Buzz"
    | .FizzBuzz => "Fizzbuzz"
    | .Num i => toString i

def fb_one (i : Nat) :=
    if i % 15 = 0 then FB.FizzBuzz else
    if i % 5 = 0 then FB.Buzz else
    if i % 3 = 0 then FB.Fizz else
    FB.Num i

def fb_vec (n : Nat) : Vector FB n :=
  Vector.range' 1 n |> Vector.map fb_one

-- specification

theorem fb_one_to_fb_vec :
    ∀ (i n : Nat), (h : i < n) → (fb_vec n)[i]'h = fb_one (i + 1) := by
  intros i n h
  unfold fb_vec; simp
  rw [Nat.add_comm]

theorem thm1 : ∀ (i n : Nat) (H : i < n), 
    (i + 1) % 3 = 0 → (i + 1) % 5 ≠ 0 → 
    (fb_vec n)[i]'H = FB.Fizz := by sorry

theorem thm2 : ∀ (i n : Nat) (H : i < n), 
    (i + 1) % 3 ≠ 0 → (i + 1) % 5 = 0 → 
    (fb_vec n)[i]'H = FB.Buzz := by sorry

theorem thm3 : ∀ (i n : Nat) (H : i < n), 
    (i + 1) % 3 = 0 → (i + 1) % 5 = 0 → 
    (fb_vec n)[i]'H = FB.FizzBuzz := by sorry

theorem thm4 : ∀ (i n : Nat) (H : i < n), 
    (i + 1) % 3 ≠ 0 → (i + 1) % 5 ≠ 0 → 
    (fb_vec n)[i]'H = FB.Num (i + 1) := by sorry
```

::: note
In this post, we'll attempt to prove one of our core theorems, draw some
conclusions about what was easy and difficult about writing the proof,
and refine our implementation one last time.
:::

## At last, a real specification for Fizzbuzz

Let's try writing one a proof of one of our actual Fizzbuzz specifications -
following the design of our "program", we'll first prove that the call
to the helper function `fb_one i`, when `i` is appropriately-chosen, is
`Fizzbuzz`.  We will then extrapolate that to `vb_vec[i]` under the same
constraint for `i` using the `fb_one_to_fb_vec` theorem we proved last time.

::: margin-note
Note that I've deliberately written this theorem slightly differently than how
it appears in the implementation: here this theorem states a hypothesis about
`i % 3 = 0` and `i % 5 = 0`, whereas `fb_one` does a single check that `i % 15
= 0`.  Dafny had no trouble distinguishing without us explaining why that these
are saying the same thing because linear arithmetic is intrinsically part of
its solver, whereas Lean's type system needs, as we've seen, explicit theorems
applied by us to prove equivalent statements.
:::
```lean4
theorem fb_one_i_mod_15_is_fizzbuzz:
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by

1 goal
⊢ ∀ (i : ℕ), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz
```

### Intro and unfold, like usual

As usual, our first tactic involves introducing statements into our context
and unfolding some basic definitions.  You've seen this a bunch before so
we'll move quickly at the beginning.

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 -- NEW 
  unfold fb_one -- NEW

1 goal
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
⊢ (if i % 15 = 0 then FB.FizzBuzz else 
   if i % 5 = 0 then FB.Buzz else 
   if i % 3 = 0 then FB.Fizz else 
   FB.Num i) = FB.FizzBuzz
```

In which cases does the left-hand side of the goal equality match the right?
There's clearly one situation that makes sense here: the left-hand side only
matches the right-hand side when `i % 15 = 0`.  

More subtly, though, it also needs to be the case that if `i % 15 ≠ 0` (that is,
if we were to fall through the first `if...then`), it better not be the case
that `i % 3 = 0` and `i % 5 = 0` also hold.  (Given that those are the two
hypotheses `H3` and `H5` that we've introduced, this is kind of like saying
"any other case than `i % 15 = 0` is a contradiction and impossible".  We'll
have a lot to say about contradictions shortly.)

::: margin-note
Yes, you can extend Lean with custom tactics if you're so inclined!  They're
typically written as a macro that expands into operations over the Tactics
Monad.  (Since Lean's a pure functional language, maybe you surmised that we
would need something like the State Monad in order to remember and modify
the goal and its context.)  We'll soon be introduced to the `lia` tactic,
which is a custom tactic from the Mathlib library.
:::

When we have control flow like an `if...then` or `match` expression that
we want to handle the different cases for, using the `split` tactic will 
decompose the goal into the different paths that the program could go

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split

2 goals
case isTrue
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
h✝ : i % 15 = 0
⊢ FB.FizzBuzz = FB.FizzBuzz
case isFalse
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
h✝ : ¬i % 15 = 0
⊢ FB.Buzz = FB.FizzBuzz
```

::: margin-note
There's actually a shorter path to proving this theorem, by simply applying
`ite_cond_eq_true`, which reduces the goal to `(i % 15 = 0) = true`.

Doing it the way we're doing, with manual case-splitting, is taking
a slightly longer path, but: it'll introduce some important new tactics, help
generalise the proof to the other three core theorems, and keep the proof
working for later on when we refactor our `FB` data definition.
:::
You might expect to see _four_ goals here because we have four branches in
`fb_one`'s nested-if.  It turns out that this tactic will automatically
simplify down and eliminate branches that it knows are logically impossible
given the assumptions `H3` and `H5`.  You can play around with handing the full
if/else ladder manually by _generalizing_ the proof: don't introduce `H3` and
`H5` right off the bat but wait until after you've started splitting each `if`;
you'll see goals with both, for instance, `i % 5 = 0` and `i % 5 ≠ 0`; these
are the ones that have been pruned away for us automatically here.

### Focus in on subgoals with the `·` dot operator

This is, I think, our first example of a _structured_ proof, where a tactic
has broken our goal down into multiple subgoals for us to prove individually.

We can focus on the first goal with the `·` "bullet" operator - this will take
our context, which currently has two goals to prove, and "zooms in" on the
first one in the list.  (This should remind you of proving a lemma that you've
defined inline with `have`.)

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split
  · --NEW

1 goal
case pos
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : i % 15 = 0
⊢ FB.FizzBuzz = FB.FizzBuzz
```

This is the "then" side of the `if` expression: when the conditional `i % 15 =
0` is true, then `fb_one` produces `FB.FizzBuzz`, which is exactly the
expression our theorem states it should.  A `rfl` or `simp` is enough here.

### Proving `false` means hunting for a contradiction

The second subgoal, the "else" side of the conditional, is more complicated to
solve, and introduces a really interesting concept about what falsity means:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs with H15
  · rfl 
  · --NEW

1 goal
case isFalse
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
h✝ : ¬i % 15 = 0
⊢ FB.Buzz = FB.FizzBuzz
```

Our goal, `FB.Buzz = FB.FizzBuzz`, should feel problematic to you: an axiom
of inductive datatypes like `FB` is that they're _disjoint_ - every element
of a given type can only be constructed in one way, so there's no way for
two different constructors of `FB` to produce "an equivalent" value.  We should
believe that the statement in the goal is false, and by `simp`lifying our goal,
we can see that Lean agrees with us.

::: margin-note
The `simp` isn't strictly necessary for Lean to understand what's going on,
but as a good rule of thumb it's helpful for _us_ to understand what's going on.
:::
```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split
  · rfl 
  · simp --NEW

1 goal
case isFalse
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
h✝ : ¬i % 15 = 0
⊢ False
```

Ooooook.

Our goal is to prove that the proposition `False` is true.  That seems...
actually impossible to do.  This whole time we've been crunching the goal down
until it's something that Lean can reduce to `True`, after all!

::: margin-note
It's not a coincidence that we encountered the principle of explosion right
about when we first encountered the _negation_ of a statement.  In Lean (as
well as Rocq and other similar languages), `Not x` is
[defined](https://github.com/leanprover/lean4/blob/2234c9116310b4c954ae42178e1f5d8e9795c682/src/Init/Prelude.lean#L223)
as the implication `x -> False`.  In other words, "not x" means "it is a
contradiction to be able to prove x"!
:::
There's an escape hatch of sorts here: by the logical principle known,
spectacularly, as both the [principle of
explosion](https://en.wikipedia.org/wiki/Principle_of_explosion) and _ex falso
quodlibet_.  It states that any goal, no matter how absurd it seems, can be
proven if you assume a contradiction.

Less philosophically-speaking: the purpose of this goal _actually_ is to show
that there's a contradition somewhere in our _context_.  It's hard not to see
where the contradiction is: we have both `i % 3 = 0` and `i % 5 = 0`, but also
`¬i % 15 = 0`.  If we can massage H3 and H5 into `i % 15 = 0`, then we've got
our two contradictory statements.

Well, let's do that, then: let's state that, actually, `i % 15 = 0`:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split
  · rfl 
  · simp
    have H15: i % 15 = 0 := by

1 goal
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
h✝ : ¬i % 15 = 0
⊢ i % 15 = 0
```

Notice that the goal has changed, because we've stated something with `have`
that we are now going to prove.

I'll admit that it's been long enough since my undergrad math classes that I
wasn't entirely sure how to actually prove this!  I knew it had something to do
with 3 and 5 being coprime, and so probably falls out of the Fundamental Theorem
of Arithmetic or something.  I struggled for quite a while until I wondered
whether, like Rocq, if Lean happens to have the `lia` tactic.  Turns out it
does!

`lia` is another automated tactic that comes with Mathlib, that specifically
solves goals involving linear arithmetic, which is exactly what we've got on
our hands here.  The docs say it's ["inspired by modern SMT
solvers"](https://github.com/leanprover/lean4/blob/2fcce7258eeb6e324366bc25f9058293b04b7547/src/Init/Grind/Tactics.lean#L16)
and uses cool research like
[e-matching](https://leodemoura.github.io/files/ematching.pdf).  Automated
tactics like `lia` bridge the gap between writing Lean proofs entirely by hand
as we've been doing here, and handing off the entire proof burden to an
automated solver, like we did with Dafny.

All right, with our lemma proven, the trap's set:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split
  · rfl 
  · simp
    have H15 : i % 15 = 0 := by lia -- NEW

1 goal
case neg
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
h✝ : ¬i % 15 = 0
H15 : i % 15 = 0
⊢ False
``` 

::: margin-note
In Dafny, you can also prove things by contradiction: you'd write a lemma
that ends up with an `assert false`.  I like this because the computational
equivalent, of a function that ends up firing an assert, feels a lot more
natural than the principle of explosion.
:::
Our contradiction is clear: certainly hypotheses `H_15` and `H+` can't
_both_ be true, since one's the negation of the other.  So, we have two statements
that contradict in our context!  The only thing left to us is to close out the
subgoal by marking it as a proof by contradiction:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split
  · rfl 
  · simp 
    have H15 : i % 15 = 0 := by lia
    contradiction --NEW 

Goals accomplished!
```

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

## Simplifying our proofs with tactics combinators

Before proceeding, you should try and write the equivalent theorems
for the other `FB` constructors.

This is what I got:

```lean4
theorem mod_15_is_fizzbuzz :
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split 
  · rfl
  · simp
    have H15 : i % 15 = 0 := by lia
    contradiction


theorem mod_5_is_buzz : 
  ∀ (i : Nat), i % 3 ≠ 0 → i % 5 = 0 → fb_one i = FB.Buzz := by
  intros i H3 H5
  unfold fb_one 
  split 
  · simp
    have H3' : i % 3 = 0 := by lia
    contradiction
  · rfl 
  
theorem mod_3_is_fizz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 ≠ 0 → fb_one i = FB.Fizz := by
  intros i H3 H5
  unfold fb_one 
  split 
  · simp
    have H5' : i % 5 = 0 := by lia
    contradiction
  · rfl 

theorem else_is_num : 
  ∀ (i : Nat), i % 3 ≠ 0 → i % 5 ≠ 0 → fb_one i = FB.Num i := by
  intros i H3 H5
  unfold fb_one 
  split 
  · simp
    have H5' : i % 5 = 0 := by lia
    contradiction
  · simp
```

Just from a quick visual inspection you can see how similar the shape of these
proofs look: Up until the `split` they're identical, and the two subgoals
involve a proof by contradiction and a straightforward "simplify and refl".
What differs between the proofs is which subgoal is trivally-solvable
and which requires a proof by contradiction, and which requires introducing
an additional hypothesis to direct the contradiction.

We can structure these four proofs around their commonalities by using _tactics
combinators_ (also called _tacticals_).  Just like how a function combinator in
functional programming is a higher-order function that combines, manipulates,
or produces functions, a tactical lets us compose multiple tactics into new
ones.

### `all_goals`, `any_goals`, and `;` apply a tactic to all the open subgoals

Here's a useful observation: For the contradictory subgoal, we always start by
applying `simp`, and while we use `rfl` for the trivial subgoal, `simp` is
smart enough to complete a proof that we have been using `rfl` for.  This means
that if we could tell Lean "run `split`, and then `simp` all the subgoals", our
proof becomes a lot shorter!  We wouldn't even have to manually prove the
trivial subgoal, and we'd be able to skip manually `simp`ing the contradictory
goal.

The `all_goals` tactical can do this for us: it takes as argument the name of
a tactic to apply on all open subgoals.  Let's try this:

```lean4
theorem mod_15_is_fizzbuzz :
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split
  all_goals simp

1 goal
case isFalse
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
h✝ : ¬i % 15 = 0
⊢ False
```

::: margin-note
It's common enough in proofs to "create a bunch of subgoals, and then apply the
same tactics to all the goals" that there's a nice shorthand for this: `t1 <;>
t2` first performs `t1`, and then for however many subgoals exist afterwards,
`t2` is applied to those.  (`<;>`'s a bit like `xargs(1)` in that sense.)
:::
As we expected, the trivial goal has been eliminated completely, and we see the
result of the simplification on the remaining contradictory goal.  (This tactic
is called `all_goals` because it will fail if, say, `simp` failed to apply in
any of the goaisl.  There's also an `any_goals t` that applies `t` to all
subgoals, but only fails if _all_ subgoals rejected `t`.)

This works for all our theorems here: the only thing that changes between them
is which particular hypothesis we introduce to force the proof by contradiction:

```lean4
theorem mod_15_is_fizzbuzz :
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split <;> simp
  have H15 : i % 15 = 0 := by lia
  contradiction

theorem mod_5_is_buzz : 
  ∀ (i : Nat), i % 3 ≠ 0 → i % 5 = 0 → fb_one i = FB.Buzz := by
  intros i H3 H5
  unfold fb_one
  split <;> simp
  have H3' : i % 3 = 0 := by lia
  contradiction
  
theorem mod_3_is_fizz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 ≠ 0 → fb_one i = FB.Fizz := by
  intros i H3 H5
  unfold fb_one 
  split <;> simp
  have H5' : i % 5 = 0 := by lia
  contradiction

theorem else_is_num : 
  ∀ (i : Nat), i % 3 ≠ 0 → i % 5 ≠ 0 → fb_one i = FB.Num i := by
  intros i H3 H5
  unfold fb_one 
  split <;> simp
  have H5' : i % 5 = 0 := by lia
  contradiction
```

The amount of repetition here might now be driving you to distraction (though
in many cases it's [okay to repeat yourself,
actually](https://programmingisterrible.com/post/176657481103/repeat-yourself-do-more-than-one-thing-and)).

## Your turn: Connecting it back to `fb_vec`

OK, let's see if we can quickly connect the proof we just wrote to one about
`fb_vec`.   Actually, you know what -- by now you've seen enough proofs that I
think _you_ should give it a try before continuing! 

Here's the scaffholding to get you started:

```lean4
theorem thm3 : 
  ∀ (i n : Nat) (H : i < n), 
    (i + 1) % 3 = 0 → (i + 1) % 5 = 0 → (fb_vec n)[i]'H = FB.FizzBuzz := by
```

This will involve both rewriting the goal based on `fb_one_to_fb_vec` and
applying `mod_15_is_fizzbuzz`, the theorem we just proved.

(You might benefit from knowing about the
[exact](https://lean-lang.org/doc/reference/4.26.0/Tactic-Proofs/Tactic-Reference/#exact)
tactic: `exact p` completes the proof if `p` is a proof of the goal.  Don't
forget that a proof can take _arguments_.)

OK, here's what _I_ wrote:

```lean4
theorem thm3 : 
  ∀ (i n : Nat) (H : i < n), 
    (i + 1) % 3 = 0 → (i + 1) % 5 = 0 → (fb_vec n)[i]'H = FB.FizzBuzz := by
    intros i n H H3 H5
    rw [fb_one_to_fb_vec]
    exact mod_15_is_fizzbuzz (i + 1) H3 H5
```

Completing the remaining three theorems is as simple as swapping out the
appropriate final theorem to apply (e.g. `mod_5_is_buzz` for `thm2`, etc).

## Next time...

This was actually a pretty productive session!  We wrote our Fizzbuzz
specification and our implementation successfully checks against it.



---
layout: post.njk
title: "Leaning into the Coding Interview: Lean vs Dafny round three"
date: 2026-01-30T00:00:00-05:00
tags: [post, lean, verification, provingthecodinginterview]
excerpt: "Time to actually prove our specification!"
draft: true
---

## Welcome back!

TODO

## At last, a real specification for Fizzbuzz

Let's try writing one a proof of one of our actual Fizzbuzz specifications -
following the design of our "program", we'll first prove that `fb_one i`, when
`i` is appropriately-chosen, is `Fizzbuzz`, and then extrapolate that to
`vb_vec[i]` under the same constraint for `i`.

::: margin-note
Note that I've deliberately written this theorem slightly differently than how
it appears in the implementation: here this theorem states a hypothesis about
`i % 3 = 0` and `i % 5 = 0`, whereas `fb_one` does a single check that `i % 15
= 0`.  Dafny had no trouble distinguishing without us explaining why that these
are saying the same thing.
:::
```lean4
theorem fb_one_i_mod_15_is_fizzbuzz:
  ∀ (i : Nat) (H3: i % 3 = 0) (H5 : i % 5 = 0), fb_one i = FB.FizzBuzz := by ...

1 goal
⊢ ∀ (i : ℕ), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz
```

### Intro and unfold, like usual

As usual, our first tactic involves introducing statements into our context
and unfolding some basic definitions.

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

Notice that there's clearly one situation that makes sense here: the left-hand
side only matches the right-hand side when `i % 15 = 0`.  More subtly, though,
it also needs to be the case that if `i % 15 != 0`, it better not be the case
that our two hypothesis `i % 3 = 0` and `i % 5 = 0` also hold.

::: margin-note
Yes, you can extend Lean with custom tactics if you're so inclined!  They're
typically written as a macro that expands into operations over the Tactics
Monad.  (Since Lean's a pure functional language, maybe you surmised that we
would need something like the State Monad in order to remember and modify
the goal and its context.)
:::
Mathlib introduces a new tactic called `split_ifs` which can help us prove
both those situations:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split_ifs with H15 -- NEW

2 goals
case pos
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : i % 15 = 0
⊢ FB.FizzBuzz = FB.FizzBuzz

case neg
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : ¬i % 15 = 0
⊢ False
```

You might expect to see _four_ goals here because we have four branches in
`fb_one`'s nested-if.  It turns out that this tactic will automatically
simplify down and eliminate branches that it knows are logically impossible.
(You can play with the simpler `split` tactic to see the difference: the two
goals missing from our proof have obvious contradictions that `split_ifs` is
able to eliminate right off the bat.

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
  split_ifs with H15
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
expression our theorem states it should.  A `rfl` is enough here.

### Proving `false` means hunting for a contradiction

The second subgoal is more complicated to solve, and introduces a really
interesting concept about what falsity means:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs with H15
  · rfl 
  · --NEW

1 goal
case neg
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : ¬i % 15 = 0
⊢ False
```

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
  split_ifs with H15
  · rfl 
  · have H_15': i % 15 = 0 := by

1 goal
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : ¬i % 15 = 0
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

`lia` is another automated tactic that specifically solves goals involving
linear arithmetic, which is exactly what we've got on our hands here.  The docs
say it's ["inspired by modern SMT
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
  split_ifs with H15
  · rfl 
  · have H_15' : i % 15 = 0 := by lia -- NEW

1 goal
case neg
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : ¬i % 15 = 0
H_15' : i % 15 = 0
⊢ False
``` 

Our contradiction is clear: certainly hypotheses `H_15` and `H_15'` can't
_both_ be true, so the only thing left to us is to close out the subgoal
by marking it as a proof by contradiction:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs with H15
  · rfl 
  · have H_15' : i % 15 = 0 := by lia
    contradiction --NEW 

Goals accomplished!
```

## Connecting it back to `fb_vec`

OK, let's see if we can quickly connect the proof we just wrote to one about
`fb_vec`.   Actually, you know what -- by now you've seen enough proofs that I
think _you_ should give it a try! Here's the scaffholding to get you started:

```lean4
theorem mod_15_is_fizzbuzz' : 
  ∀ (i n : Nat) (H : i < n), 
    (i + 1) % 3 = 0 → 
    (i + 1) % 5 = 0 → 
    (fb_vec n)[i]'H = FB.FizzBuzz := by
```

(You might benefit from knowing about the `exact` tactic: `exact e` closes the
goal if `e` is a proof of the goal.)

## What if we'd gotten the implementation wrong?

It's all fine and well if we prove something about an implementation we
already knew was correct.  Let's introduce a bug into `fb_one` and see
how our proof goes awry:

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
  split_ifs

1 goal
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
⊢ False
```

If this single remaining goal looks unsolvable, that's because ... it _is_
unsolvable!  This makes sense when you consider that the statement we're
trying to prove is fundamentally unsolvable.

You might remember that when we broke our Dafny implementation in a similar way
we got a lovely counterexample back from the solver.  Here we're not so lucky;
we don't get an _error_, per se, so much as just a partial proof that's
impossible to prove.

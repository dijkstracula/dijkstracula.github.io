---
layout: post.njk
title: "FRP in Lean: Hoare Logic, Dafny revisited, and Indexed Monads"
date: 2026-06-30
tags: [post, lean, reactive-programming, frp, hoare-logic]
excerpt: "New program logic just dropped!"
series: lean-ltl
series_title: "Hoare Logic"
draft: true
---

Last time we implemented a series of combinators that transformed not just data
values that might flow through a functional reactive program, but invariants
about that data.  Recall our `RSignal.map` function:

```lean4
def map
  {pre: α → Prop}
  {post: β → Prop}
  (f: {a: α // pre a} → {b : β // post b})
  (s: □ α // pre)
  : □ β // post := ...
```

Given a precondition over the input type `a` and a postcondition over the
output type `β`, and a mapping function that turns an `a` that satisfies `pre`
into a `β` that satisfies `post`, we can turn a signal of `a`s where `pre` is a
safety property into a signal of `β`s with -- yes, you guessed it -- `post` as
a safety property.  (The other combinators we wrote had a similar sort of
shape: consume a refined signal and somehow transform its value and safety
property).

Someone pointed out that this looks a lot like [_Hoare
logic_](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html),
which is a classic way of reasoning about imperative, mutable programs.  I thought
it might be fun to see how far we can connect Hoare logic to our FRP library.
I have a suspicion that we'll get most, but not _all_ of the way there, and
it'll help reveal if there's any gaps in our library.

## Warmup: Faking `RSignal` as a Proper (Applicative) Functor

We discussed last time that we can't make `RSignal` an instance of the
typeclass `Functor`, because `RSignal` has a dependent type `(α : Type) → (α →
Prop) → Type`, which won't fit `Functor`'s `Type → Type` shape.  We can at
least, though, add a custom operator to replace the `<$>` we don't get to use:

::: margin-note
The evaluation semantics of `<**>` are slightly different than `<*>`: because
the right-hand argument doesn't have to have the short-circuiting semantics
that an arbitrary `Applicative` does, we don't have to wrap `sx` in a thunk
to lazily evaluate.  Nice!
:::
```diff-lean4
 -- Unrefined Signals are truly Functors and Applicatives...

 instance : Functor Signal where
   map := Signal.map -- e.g. <$>

 instance : Applicative Signal where
   pure := Signal.const
   seq sf sx := Signal.map2 (· ·) sf (sx ()) -- e.g. <*>

+ -- ... RSignals can have identically-implemented operators, but
+ -- they can't be expressed through the same typeclass interface.
+ infixr:100 " <$$> " => RSignal.map
+ infixr:60 " <**> " => RSignal.map2
```

Going forward, I'll use `<$$>` in place of `Functor`, and `<**>` when I would
have reached for an `Applicative`.

## The essence of Hoare logic, in one formula

We'll see exactly what sorts of program behaviour we can express in Hoare logic
soon enough, but the most important part of the logic is the _Hoare triple_.
It's, as you might expect, a logical expression with three parts:

::: tip
The Hoare triple `{P} c {Q}` is made up of a precondition `P`, a postcondition
`Q`, and a "command" (which usually boils down to a mutable statement in some
progrmaming language `c`.  A Hoare triple is valid if, under the assumption that `P`
holds before `c` executes, `Q` will hold after it executes.
:::

A classic Hoare triple (which I'm borrowing from the _Software Foundations vol
2_ chapter linked above might be `{i == 0} i++ {i == 1}`: if `i` was `0`
before incrementing it, it'll be `1` after.  Another valid triple with the same
precondition might be `{i == 0} i++ {i > 0}` - incrementing a zero-value
variable will leave it as a positive-valued variable.  One more: `{10 < 20} i++
{j == 99}`: here, neither the precondition nor the postcondition state anything
about `i`, and the latter refers to a totally different (presumably in-scope)
variable!

::: margin-note
Is the proposition we just wrote down valid or not?  Probably depends on some
factors about `i` that we haven't explicitly stated in this example.  It's
worth pausing and ponding a situation where that proposition is valid and one
where there's a counterexample.
:::
Just like how we embedded temporal logic in Lean's type theory, we could do the
same here, too: `∀ x, {i == x} i++ {i == x+1}` is a proposition that
quantifies in the host logic to make a statement in the embedded logic.

This is a very different kind of logic from LTL!  A command can be more
structured than just a single statement like `i++`; we'll see that there are
Hoare logic rules for loops, conditionals, variable declarations; anything you
need, really, in a straightforward imperative programming language.  The hope
is that if our FRP library "spans" the space of Hoare logic primitives, then we
ought to imagine our set of FRP combinators is expressive enough to implement
"realistic imperative programs" in.

::: margin-note 
Hey, I know a decent [Dafny tutorial](/posts/proving-the-coding-interview/) or
[two](/posts/proving-the-coding-interview-lean/), if you're looking for one!
:::
Hoare logic is the essence of how Dafny weaves logical statements about different
parts of a program.  Here's a Dafny method that ought to feel familiar:

```dafny
method increment(x: int) returns (y: int)
  requires x == 0      // precondition: P
  ensures y > 0        // postcondition: Q
{
  y := x + 1;
}
```

For Dafny to "typecheck" a program that calls `increment`, the precondition
regarding the input argument (or any other piece of program state) has to be
provably satisfied at all call sites; symmetrically, Dafny will in turn expose
the postcondition for the parts of the program following the function call.

Here's a call of `increment` in some larger Dafny program:  (I haven't written
a square root method, and I'm not sure if the Dafny standard library has one,
but you can probably imagine its preconditions enforce and guarantee
non-negative inputs and outputs.)

::: margin-warning
For now, let's gloss over the fact that sequencing operations like this also
requires an assignment-to-a-variable step.
:::
```dafny
// sequencing...
let z := 0;          // z := 0
z := increment(z);   // z > 0
z := sqrt(z);        // z >= 0

// ... is composition.
z := sqrt(increment(0)) // z >= 0
```

Here we are _sequencing_ operations on some program state, which is the same
here as composing the two functions together.  Lean lets us write the same
program in FRP style: 

```lean4
def incr (i : {i : Int // i = 0}) : {i : Int // i > 0} := ...
def sqrt (i : {i : Int // i > 0}) : {i : Int // i >= 0} := ...

-- sequencing of signals...
def z :  □ Int // (· = 0)  := FRP.Refining.RSignal.const ⟨0, by lia⟩
def z2 : □ Int // (· > 0)  := incr <$$> z
def z3 : □ Int // (· >= 0) := sqrt <$$> z2

-- ... is composition of signals.
def z4 : □ Int // (· >= 0) := sqrt <$$> incr <$$> z
```

This bring us to our first correspondence: composition of Signals is
Hoare logic's _sequencing rule_.

## Sequencing and composition

Here's the sequencing rule for Hoare logic: 

::: margin-note
This might be the first time we've seen [Genzen
notation](https://planetmath.org/gentzensystem), or sequent calculus, in this
series.  This is an _inference rule_; you read this by saying "if the
statements above the line hold, then the statement below the line holds".
:::
::: tip
```
     {P} S1 {Q}    {Q} S2 {R}
      ──────────────────────── (hoare_seq)
          {P} S1; S2 {R}
```
The _sequencing rule_: Starting with two Hoare triples, each with their own
statement, and where the postcondition of the first is the precondition of the
second, it's valid to "toss out the middle proposition" if our Hoare command
becomes "execute the first statement, and then execute the second statement".
:::

In our example here, `z4`, our composition-of-signals, has an intermediary
proposition that gets hidden inside the composition.

::: margin-note
I spent awhile trying to complete the `z4 = z5` proof before discovering a
reflexivity proof is enough.  I genuinely am not sure how Lean figures that out
with such a simple tactic, because I would have thought we'd have to manually
prove that `Signal.spilt` and `Signal.collect` are inverses, which we've never
actually done!
:::
::: note
Here's a fun aside: 

As it happens, because `RSignal.map` maintains the _functor law_ `map (f ∘ g) =
map f ∘ map g` (even though it doesn't implement `Functor`, for reasons we
discussed last time), composing two refined functions and then lifting them
into a Signal gives the same result as lifting each function separately and
then compositing the two signals.  We can even prove they're the same function!

```lean4
def z4 : □ Int // (· >= 0) := sqrt <$$> incr <$$> z
def z5 : □ Int // (· >= 0) := (sqrt ∘ incr) <$$> z
example : z4 = z5 := by rfl`
```
:::

Long-time (long-suffering?) readers of this blog might remember that this isn't
the first time we've seen a mechanism to reason about sequencing operations:
that's part of the fun of a monadic bind, way back in [part
2](/posts/lean-ltl-2).  (Maybe this suggests that we're not entirely done with
monads - stay tuned...)

<TODO: why does sequencing matter?>

## `map2`, conjunctions, and conditionals

`RSignal.map`, ahem, mapped pretty cleanly onto the sequencing rule.  We might
expect `map2` to, as well, but we'll see the correspondence isn't quite so
exact.

The most straightforward interpretation of `map2` is that 

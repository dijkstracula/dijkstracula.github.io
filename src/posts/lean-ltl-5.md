---
layout: post.njk
title: "Reactive Programming in Lean Part 5: More FRP combinators"
date: 2026-04-30
tags: [post, lean, reactive-programming]
draft: true
series: lean-ltl
series_title: "Part five - `step`, `accumulate`, and other non-pointwise combinators"
---

# Non-pointwise combinators have knowledge of previous timesteps

In this post, we'll build up to `accumulate`, which is a general-purpose
non-pointwise combinator.  We'll see that the point of these combinators is to
combine a sequence of discrete `Events` over time to maintain a running
`Signal`.

## Some background: catamorphisms and recursors

You already know how to fold over a List:
[List.foldr](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.foldr)
takes an initial value `β` and a "merge" function `a -> β -> β`, and collapses
the list down into a single result.  For a long time, I thought folds were
somehow intrinsic to `List`s because I'd never seen folds in any other context,
but you can write a fold-like operation over any algebraic datatype.

::: margin-note
In reality, the catamorphic operation for `Nat`, called `Nat.rec`, is a [bit
more
complicated](https://github.com/leanprover/lean4/blob/80cbab16420b90104647a795a18f9890fd8150e8/src/Init/Data/Nat/Basic.lean#L38)
owing to `β` being a dependent type, but the idea is exactly the same - it lets
us "tear down" a value to call a function on its enclosing elements.
:::
That operation is called a _catamorphism_ in category theory, and a _recursor_
in type theory.  A catamorphism for some type replaces each constructor of that
type with a function that consumes _the arguments of the constructor_ and
_produces a value of some new type_.

Why does `List.foldr` have the arguments it does?  It stems from the datatype's
constructors. There are two ways to construct a List, as we all know: `Nil :
Unit -> List a` produces the empty list, and `Cons : a -> List a -> List a`
prepends an element onto a list.  This means the function that replaces `Nil :
Unit -> List a` will be typed `Unit -> β` (or, just a constant `β` value), and
the function that replaces `Cons : a -> List a -> List a` will be typed `a -> β
-> β`.

In other words, `List.foldr` is the catamorphic operation for `List`!


## Our first non-pointwise combinator: `scan` folds over time

Here's one more: A catamorphism for `Nat` (with constructors `Zero` and `Succ
Nat`) would take a `β` and a `β -> β`.  Since `Time` is definitionally a `Nat`,
a catamorphism on `Time` would take a `β` and a `β -> β`, similarly.  But what
do those two arguments actually _mean_?

What it means is stepping through time from an initial state.  And, that's what
`scan`, our first non-pointwise combinator, does.

```lean4
def scan: (step : β → β) (init : β) : Signal β =
  fun n => Nat.rec init (fun _ s => step s) n 
```

`scan` produces a function that takes a time value and steps the `β -> β`
function that many times from an initial state.

::: margin-note
Evaluating `scan step init` at time `t` recomputes from init every time — O(t)
per evaluation, O(n²) to evaluate the whole signal. A real FRP runtime would
cache previous state(s). 
:::

```
def screaming : Signal String := scan (· ++ "a") ""
#eval (List.range 5).map screaming -- ["", "a", "aa", "aaa", "aaaa"]
```

Something interesting to note is that this is our first `Signal` that isn't
ultimately driven by the tick of the `clock`: we never actually do any
computation based on the internal value of `t` like we did with the UTC
time conversion example.

This should also feel a lot like what we did with stepping state machines back
in the first post!  The difference, of course, is that `vmStep` needed an
action at each step (and a proof it was valid, of course).  `scan` `Signal`s
don't, by contrast; it's an autonomous state machine that just evolves on its
own.  We'll need a richer combinator to start folding in `Event`s into the
mix.

## `accumulate` is a temporal fold over an `Event`

The idea of `accumulate` is this: we're going to start with an `Event` of
some type and produce a `Signal` of some type.

```lean4
def accumulate: ... (step? : β → β) (init : β) (ev: Event a) -> Signal β := 
  -- TODO
```

The goal of this section is to build up from intuition what the remaining
arguments of `accumulate` must be.  Given that `accumulate` also involves a
catamorphism over `Time`, we probably want both a `β` and `β -> β`, but their
meaning will probably change, and so their argument names likely will as well.

### When the event is not firing

One thing to notice is that so long as the given `Event` isn't triggering (that
is, when `ev t = none`, this is doing exactly the same thing as our `scan`
combinator.  So, `step?` might as well be called `onNone`, since that's how
to just produce a new `β` given the current one.

### ...and when it is firing

This also means we want a `onSome` function, of some type!

```lean4
def accumulate: (onSome: ? -> β) (onNone: β → β) (init : β) (ev: Event a) -> Signal β := 
  -- TODO
```

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

That operation is called a
[catamorphism](https://ncatlab.org/nlab/show/catamorphism) in category theory,
and relates to _recursors_ in type theory (which we'll see an example of in a
moment).  A catamorphism for some type replaces each constructor with a
corresponding computation (an “algebra component”) that produces the result
type `β`. 

That function consumes:
- the constructor’s **non-recursive** arguments unchanged, and
- the constructor’s **recursive** arguments *after they’ve already been folded*.

Let's invent the catamorphism for `List`s from first principles.  Why does
`List.foldr` have the arguments it does?  It stems from the datatype's
constructors. There are two ways to construct a List, as we all know: `Nil :
Unit -> List a` produces the empty list, and `Cons : a -> List a -> List a`
prepends an element onto a list.  This means the function that replaces `Nil :
Unit -> List a` will be typed `Unit -> β` (or, just a constant `β` value, but
if we're enlightened and lazy Haskell programmers this is one and the same
thing), and the function that replaces `Cons : a -> List a -> List a` will be
typed `a -> β -> β`.

In other words, `List.foldr` is the catamorphic operation for `List`!  It shows
us how to collapse one constructor layer into a `β`.

### Recursors generalise catamorphisms

If we want more generality than just "given the recursive results of the
subdata in each constructor, produce a value", we'll need a different kind of
algebraic transformation on our datatype.  For example, it isn't clear how we
could write a `Nat.predecessor` or `List.drop_last` function with catamorphisms.
A generalisation that _does_ let us do this is a _recursor_.

We could also write a catamorphism for `Nat`s: `Nat` has two constructors,
`Zero : Unit -> Nat` and `Succ : Nat -> Nat`.  Because the `Zero` constructor
morally takes no arguments, we provide a constant `β` value for that case, and
for `Succ`, a `β -> β`.

We said before that recursors occupy a similar purpose to catamorphisms but
have been vague about what that actually means.  Let's look at a simplified
version of Lean's recursor for `Nat`:

::: margin-note
In reality, the recursor, is a [bit more
complicated](https://github.com/leanprover/lean4/blob/80cbab16420b90104647a795a18f9890fd8150e8/src/Init/Data/Nat/Basic.lean#L38)
owing to `β` being a dependent type called the "motive", but the idea is
exactly the same - it lets us "tear down" a value to call a function on its
enclosing elements, while still giving us access to the original, non-folded
over values.
:::
```lean4
def Nat.rec (zero : β) (succ : (n : Nat) → β → β) : (t : Nat) → β
  | .zero => ...
  | .succ n => ...
```

This isn't the catamorphism for `Nat`s: `succ` also consumes the predecessor
argument (that is, the _recursive argument before being folded_).  This is more
general than a catamorphism; it's called a
[paramorphism](https://blog.sumtypeofway.com/posts/recursion-schemes-part-3.html),
and it's built up from a different kind of algebraic structure than
catamorphisms.

## Our first non-pointwise combinator: Signaling on the catamorphism for time

Ok, so a catamorphism for `Nat` (with constructors `Zero` and `Succ Nat`) would
take a `β` and a `β -> β`.  Since `Time` is definitionally a `Nat`, a
catamorphism on `Time` would take a `β` and a `β -> β`, similarly.  But what do
those two arguments actually _mean_?

What it means is stepping through time from an initial state.  And, that's what
`scan`, our first non-pointwise combinator, does.

::: margin-note
Should this have been a _paramorphism_ instead?  After all, we call `Nat`'s
recursor internally here.  Maybe I'll come to regret this design choice!
:::
```lean4
def scan: (step : β → β) (init : β) : Signal β =
  fun n => Nat.rec init (fun _t s => step s) n 
```

`scan` produces a function that takes a time value and steps the `β -> β`
function that many times from an initial state.  It does it with the recursor
for the natural numbers, which produces `init` when `t=0` and applies the given
function `Nat -> β -> β` when `t=(n+1)`.

::: margin-note
Evaluating `scan step init` at time `t` recomputes from init every time — O(t)
per evaluation, O(n²) to evaluate the whole signal. A real FRP runtime would
do something smarter like cache previous state(s). 
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
def accumulate ... (step? : β → β) (init : β) (ev: Event a) : Signal β := 
  sorry -- TODO
```

### Intuiting the function type for `accumulate`...

The goal of this section is to build up from intuition what the remaining
arguments of `accumulate` must be.  Given that `accumulate` also involves a
catamorphism over `Time`, we probably want both a `β` and `β -> β`, but their
meaning will probably change, and so their argument names likely will as well.

Before we go any further, you should spend a moment trying to figure out what
the catamorphism for `Option a` is.  (When you're ready: did you choose `β`
(for the `none` case) and `α → β` (for the `some a` case)?)

### ...when the event is not firing...

One thing to notice is that so long as the given `Event` isn't triggering (that
is, when `ev t = none`, this is doing exactly the same thing as our `scan`
combinator.  So, `step?` might as well be called `onNone`, since that's how
to just produce a new `β` given the previous one.

Notice that this `onNone` is _not_ the same as the `β` we guessed a moment ago.
The reason is that we're not producing `β`s from scratch, but rather one that
involves the previous `β` state.  So, that value has to be threaded through that
function.  Generally, we say we've _lifted_ `β` into the pure catamorphism.

### ...and when it _is_ firing

This also means we want a `onSome` function, of some type!

```lean4
def accumulate (onSome: ? -> β) (onNone: β → β) (init : β) (ev: Event a) : Signal β := 
  sorry -- TODO
```

Using the definition of catamorphisms for `Option a`, as well as our observation
about lifting the current `β`, we can figure out the type for `onSome`.  It's
got to consume an `a`, because that falls out straight from the catamorphism;
we have to do _something_ with `some a`, after all!  And, just like with
`onNone`, we will want to also lift a `β` in, too.  

So, ultimately, our function will have type `a -> β -> β`.  Which, makes sense
for the situation in which we're calling it: `ev` has fired, producing an `a`,
and so we want to combine that with the current signal value in some way.  And
so, our final function will look thus:

```lean4
def accumulate (onSome: a → β) (onNone: β → β) (init : β) (ev: Event a) : Signal β := 
  sorry -- TODO
```

### Implementing `accumulate` with the recursor for Time, again

OK, how do we actually write this thing?  Since we said earlier that
`accumulate` generalises `scan`, using the recursor for `Nat` seems
like a good idea.  Here's the overal shape we'll be working with:

```lean4
def accumulate (onSome: a → β) (onNone: β → β) (init : β) (ev: Event a) : Signal β := 
  fun n => Nat.rec 
    sorry            -- TODO: what to do at t=0?
    (fun s => sorry) -- TODO: what to do at t=(n+1)?
    n
```

One helper that might be worth writing: both branches in `Nat.rec` need to either
call `onSome` or `onNone`: let's factor out dispatching on whether the event has fired
into a helper function, called, I donno, `switch`:

```lean4
(* Helper: at each time step, decide which β → β to use. *)
let switch (t: Time) : β → β := match ev t with
| none => onNone
| some a => onSome a
```

When `n=0`, we'll want to dispatch on `ev 0` with our initial state `init`.
For the `n=(n'+1)` case, we'll pass in the next time value, and the previous
state, which the recursor will automatically supply for us.

So in conclusion, our final `accumulate` is:

```lean4
def accumulate (onSome: a → β → β) (onNone: β → β) (init : β) (ev: Event a) : Signal β :=
  let switch (t: Time) : β → β := match ev t with
  | none => onNone
  | some a => onSome a

  fun n => Nat.rec 
    (switch 0 init)               -- n=0
    (fun n' s => switch (n'+1) s) -- n=(n'+1)
    n
```

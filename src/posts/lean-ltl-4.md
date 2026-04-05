---
layout: post.njk
title: "Reactive Programming in Lean Part 4: Functional Reactive Programming"
date: 2026-04-17
tags: [post, lean, reactive-programming]
excerpt: "Get in losers, we're doing Curry-Howard"
draft: true
series: lean-ltl
series_title: "Part four - OMG WTF LTL FRP BBQ"
---

# The Curry-Howard correspondence for LTL: FRP

So far, what we've been doing is playing with LTL in the way that someone
using a model checker like TLA+ might.  We build a reactive system, built
some traces over that system, wrote formulas about that system, and asked
"does this trace satisfy this formula?"

All the dependently-typed programming we've done in this and other series has
been the _Curry-Howard correspondence_ in action.  When we say "a `Prop` is a
type" and "we prove a proposition by writing a program that typechecks to that
`Prop`-type", that's Curry-Howard in action.

We've extended the notion of a `Prop` to temporal logic.  By Curry-Howard, that
must mean that there are some program types (and therefore program
compuatations) that align with those propositions.  The *LTL Types FRP* paper
shows exactly what that connection is: it's to a programming model called
_functional reactive programming_.

In FRP, your core program values (which we'll see soon are called _signals_)
are _time-varying_, and you build your program by composing these signals using
pure functions.  Instead of thinking about our reactive systems imperatively,
where we're mutating a state structure action by action, FRP is about building
relationships between different values.

The `LTL types FRP` paper builds up a formulation that shows that under
Curry-Howard, the LTL logic maps to types of value in an FRP program.  Building
this connection up will be the ultimate goal of this post; by the end of it,
we should end up with two Lean namespaces that look pretty similar in structure
and function.

```lean4
namespace LTL
    ...
end LTL

namespace FRP
    ...
end FRP
```

## A `Signal` is a time-varying value

We just said that FRP is all about modeling your problem domain in terms of how
your program's values change over time.  In this programming model, a _signal_
(sometimes called a _behaviour; I may use these terms interchangably even
though true FRP-heads would point out technical differences between them) is
such a time-parameterized value.

```lean4
abbrev Time := Nat
type Signal α := Time → α
```

Notice that this the same type as our execution traces!  We'll see that the
intended meaning of a signal is different, though.  Earlier, a `Trace` was an
artifact of running some computation; it was in some sense an "output".  You
can poke at it by writing theorems about the trace, but it just sits there;
running the system through our monadic API produced the trace, and then we
use Lean's theorem proving capabilities to inspect it.

::: margin-note
We said just now that a `Signal` is a time-varying value. Technically, FRP
allows for so called _reactive types_, which are _time-varying types_.
Concretely, imagine a value such that on time steps `[0,5)`, it's a `Nat`, but
from `[5,10)` it's a `String`.  This is a dependently-typed signal!

You might enjoy trying to extend our `Signal` type to allow for time-dependent
types.
:::
A functional reactive program, on the other hand, treats Signals as core
program values.  A `Signal Int` isn't "here's the integers that were observed
at time steps 0, 1, 2, ...", but rather "here's an integer that changes over
time; let's build other time-varying values out of it".  (How we actually _do_
that will come soon enough, but you can imagine that it might involve the
"functional" part of "FRP".)


## Some `Signal`s and a few basic combinators

Here's our first `Signal`, which doesn't do more than act as a "what time is it"
clock:

```lean4
def now : □ Time := fun t => t --At time step t, our output is t itself
```

Next, let's define a way that lifts a value into the world of `Signal`s:

```lean4
def const (v: α) : □ α := fun _ => v

#eval (const 42) 5 -- at t=5, this signal has value 42, unsurprisingly.
```

OK, we can define some pretty uninteresting signals - FRP is really all
about writing functions that transform signals by way of _functional
combinators_.  Let's write a few of those.

We can transform existing signals by performing a mapping operation over them:

::: margin-note
If you're a type zoologist, you might recognise that `const` and the `map`s
mean that `Signal` is an applicative functor (which are more expressive than
ordinary functors but not as expressive as a Monad - we have defined `map` but
not `bind`).  Should perhaps `Signal`s be outright Monads?  Stay tuned for the
tradeoffs.
:::
```lean4
def map (f: α → β) (s : □ α) : □ β := 
  fun t => f (s t)  

def map2 (f: α → β → γ) (s1 : □ α) (s2 : □ β) : □ γ := 
  fun t => f (s1 t) (s2 t)

-- examples
def evens : □ Nat := map (· * 2) now
def incrementing := map2 (· + ·) (const 10) evens
#eval incrementing 42 -- at t=42, output is 94
```

These map functions are called _pointwise_ because they only operate on a
signal at the "present moment" (that is, whatever the value of `t` is). You
could imagine a _time-dependent tranformation_ that somehow involves other
values of `t` (say, computing the finite difference of `t` and `t-1`)
but we can't do that with `map`.

## A more interesting signal

Here's a silly data definition for a traffic light type.  Let's write a signal
that defines how a value of this type could change over time, say, where the
colour changes once per time step:

```lean4
inductive Light where | Red | Yellow | Green

def cycling : □ Light := 
  fun n => 
    match n % 3 with 
    | 0 => .Red
    | 1 => .Yellow
    | 2 => .Green
    | _ => panic "impossible: forall n, 0 <= n % 3 < 3"

#eval cycling 42 -- Light.red
```

Not the most realistic definition of a traffic light, but whatever.  

### Matching on a value and proof to eliminate imposible branches

A quick diversion into how dependent types can help us write simple programs
more easily:

In Lean and other functional languages that have _exhaustiveness checking_, we,
ro make the pattern matching well-formed for all possible values of `n`, have a
fourth catch-all case that we know we'll never hit.  Without this final case,
we'll get an error that looks like `Missing cases: (3 + _)`.

::: margin-note
Recall from some previous posts that `have` is like `let`, but instead of
introducing a program value (something of type `Type`), it introduces a
proof (of type `Prop`) which exists only at typechecking time.
:::
Of course, if I can write this explanation in my panic string, maybe we can
explain it to Lean's typechecker, too.  And, of course, we can: `have h : n % 3
< 3 := (by lia)` proves a statement about `Nat.mod_lt`, which we can use to
explain away our catch-all `match` arm.

```lean4
def cycling : □ Light := 
  fun n => 
    have h : n % 3 < 3 := Nat.mod_lt n (by lia)
    match n % 3, h with 
    | 0, _ => .Red
    | 1, _ => .Yellow
    | 2, _ => .Green
```

Notice we are threading through a value and _evidence about that value_.  Lean
will check each match arm and ask, "could this proof exist for the given
value?". The pair in the firt match arm would be `0 : Nat, 0 < 3 : Prop` (the
latter of which is a true), for example, so that's a valid case arm.  Since any
fourth case arm we would write -- a `_` wildcard, or explicitly `3` or `42` or
whatever -- would ask Lean to prove `3 < 3` or `42 < 3`, which is false, the
exhaustiveness checker stops complaining here.

This is Curry-Howard in action: we have a value and a proof about that value;
however, a proof _is also_ a value, with a type, and some types are empty.
Matching against an empty type eliminates the branch.

## The Curry-Howard correspondence for `Signal`

Before proceeding, you should convince yourself of the fact that one way to
summarise a `Signal α` is as an `α` value that's always available, no matter
what time-step we're at.

Since a `Signal T` makes an value of type `T` _always_ available at all points
in time, this is our first Curry-Howard correspondence: The type of a
`Signal T` is `□ T`.  `□` means the same thing in both worlds.

```lean4
namespace LTL
    ...
    prefix:max "□ " => always
end LTL
namespace FRP
    notation "□ " α => Signal α
end FRP
```

On its own, this isn't all that interesting, because so far the
`α` parameters we've seen for Signal (`Int`, `String`, `Light`) themselves
aren't all that interesting as logical propositions.  If you told a
Java programmer "`String.valueOf(i)` proves `String` given a proof of `Int`,
isn't type theory amazing??", they probably wouldn't be impressed;
similarly, "A `Signal Int` always makes an `Int` available" isn't super cool
on its own either.  We need a second fundamental primitive to add reactivity to
FRP systems.

# An `Event` occurs at some point in time

The dual of a `Signal` is an `Event`, which you can think of a stream of values
to be consumed by the system at a particular moment in time.  For an
interactive webapp, you might, "right at this moment", send a "click" `Event`
to a form button, which perhaps triggers other events to fire.  Or, maybe, you
enqueue an event to fire some point in the future, like registering a timeout
on a network call or something.  (If you come from an OO background, an `Event`
is very much like an
[Observable](https://reactivex.io/documentation/observable.html).)

## Designing an `Event` type

The second example I gave you, where we just define "at these points in the
future, consume these actions" feels, operationally, extremely different from
the first example, "wait for the outside world to inject an action", though.
One's a _closed system_ where the whole timeline exists in advance and the
other is _open_, where we need to discover what actually happens at runtime.
These will by necessity require fundamentally different data definitions; for
today, I'm going to focus on the closed system definition.  This one is both
conceptually simpler and has a nicer LTL correspondence that the equivalent one
that has to messily interact with the real world.

OK, so what's the type of a (closed) Event?  Before we can start reasoning
about `Event`s we need to make sure our data definition is well-formed.

Just like `Signal`, we'll want the type parameterised on whatever the valid
action space is, so it'll be a polymorphic type for sure, so `def Event α :=
... α` is not a terrible place to start.

Since an action can be taken or not taken at any given moment in time, the
rough shape will be `def Event α := Time → (Option α)`.  That this looks a
lot like the datatype for `Signal` perhaps indicates to us that we're on the
right track, and maybe that `Event`s are actually just a particular sort of
`Signal`?  (This is a valid design choice -- Elm originally did just this --
but I'm going to deliberately keep the datatypes distinct here.)

OK!  So, in our vending machine example, an `Event VMAction` that corresponds
to our "choose an Orange pop" might look like:

::: margin-note
Maybe, in a later installment, we'll revisit the open-termed version of
`Event`, where input can come in from the outside world.  It might be worth
meditating on what a good datatype for such an `Event` would be.
:::
```lean4
def Event α := Time → (Option α)
...
def orangeActions : Event VMAction := fun t =>
  match t with
  | 0 | 1 => some .DropCoin
  | 2 => some (.Choose .LemonLime)
  | 3 => some .TakeItem
  | _ => none
```

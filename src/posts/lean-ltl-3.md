---
layout: post.njk
title: "LTL-in-Lean part 3: Temporal Logic as Types"
date: 2026-03-17
tags: [post, lean, reactive-programming]
excerpt: "Get in losers, we're doing temporal logic"
draft: true
series: lean-ltl
series_title: "Part three - temporal logic as types"
---

In the previous posts, we saw how dependent types let us enforce validity
of a reactive program's step function, and how our monadic API gives us
a nice way to sequence those steps.

However, we hit the limits of what we could express in terms of propositions
over our system's traces.  It's straightforward enough to write statements
about an individual moment in an execution, but stating things about how
the system needs to move through time feels like we'll need additional mechanism.

Today, we'll define temporal logic and _linear temporal logic_, which is a
common logical system used by model checkers like TLA+ and SPIN, as well as
programming paradigms like _functional reactive programming_, and embed it into
Lean's existing logical system. We'll then see how to specify how our vending
machine should behave over time, with an eye to writing "real reactive
programs" in Lean and specifying them with LTL.


## The limits of `Prop`

Remember our "drop a coin, drop another coin, choose a pop flavour, take
the can" example from last time:

```lean4
def getOrange : TSM Flavour := do
  perform (.DropCoin)
  perform (.DropCoin)
  perform (.Choose .LemonLime)
  take
```

When we executed these actions on our initial pop machine state, we ended up
with:

```lean4
#eval getOrange.run init 

Except.ok (
   -- The `Flavour` returned by the computation
  (LemonLime,

   -- The execution trace observed by running the computation
  [{ coins := 0, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 1, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 2, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 0, dispensed := some LemonLime, numOrange := 5, numLL := 4 }]),

   -- The final state following the computation
 { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```

There are all sorts of propositions we could write about the final state:
maybe we want to be assured that the machine successfully ate all the coins
in the hopper, or that we didn't accidentally decrement `numOrange` versus
`numLL`.  We could also write and prove the statement `validStep <final state>
.DropCoin`, or write and _refute_ `validStep <final state> .TakeItem`.

We could also write a proposition related to the output `Flavour` or previous
steps in the trace: for instance, if we're handed back a `LemonLime` at the end
of the computation, we could ensure that at time step `t=3` we had dispensed a
`LemonLime`.

These kind of aren't terribly _interesting_ propositions, though, and this
makes sense becaue what makes reactive programs interesting is that they change
over time.  So, our logical propositions also need to be able to talk about
change over time.

## Linear temporal logic

There's lots of different kind of logics out there: you know propositional
logic as "the language of boolean formulas".  First order logic has existental
and universal quantifiers ("there exists" and "for all") over arbitrary
predicates.  Type systems are a logical system, as we've seen.  And, of course,
we can have _metalogics_ that state logical facts about logical systems.

::: margin-note
LTL isn't the only temporal logic we could use - another one is _computation
tree logic_ (CTL) is another common logic that encodes _possible futures_ as a
tree of states, versus LTL's "linear sequence of states".  We could also add
the notion of probabilities into our logical system, making a transition system
more like a Markov chain.  Something to think about playing with another time.
:::
_Linear temporal logic_ is a _modal_ logic that let us refer to relationships
between a sequence of states, as opposed to statements (like `validStep s a`)
which only speak about some given state without any connection to what might be
true or false in subsequent states.

The "linear" in LTL refers to the fact that what interests us is a sequential
_path_ of states in the system, determined by which actions were taken.  You
might that our "pay, pay, choose, take" example last time was actually a trace
just like this.

In practice formal methods folks like LTL because you can encode important
properties about real-world systems like fairness, which is important for
stating correctness about things from a spinlock up to a distributed consensus
protocol.  (Maybe we'll build up to one of those examples down the road!)

## The syntax of an LTL formula

OK, we have the notion of time, and the notion of traces, but we don't have the
nouns and verbs defined to state a temporal propsition.

::: margin-note
A _deep embedding_, by contrast, would involve implementing a syntax tree
definition for our logic, and an "interpreter" that does computation on those
syntax trees.  If you've ever implemented a language interpreter, it's a lot
like that; the world of "your host language" and "the language you're
interpreting in the host language" are sort of cleaved in two.
:::
Let's start implementing a _shallow embedding_ of LTL in Lean.  A shallow
embedding of a logic defines that logic in terms of an existing one, which
will be Lean's dependent type system.  That means that a temporal property
will, in the end, just be a `Prop`, so we will end up proving them in exactly
the same way that we'd prove any other theorem in Lean.

I'm going to put all our relevant LTL definitions in their own namespace,
just to organize things a bit better than what we've been doing so far.

```lean4
namespace LTL
  -- TODO: for each temporal modality, write a funciton that
  -- function that returns an appropriate Prop.
end LTL
```

### `LTL.atom` states something about the current moment

Logicians wouldn't really call this a modality, but "something about the
present moment" is certainly something we need to be able to make statements
about.  For example, we might define a `Prop` that expresses whether the
pop machine's coin hopper is empty:

```lean4
def hopperEmpty (s: VMState) : Prop := s.coins > 0
```

If we weren't programming in a dependently-typed language, this would probably
be a predicate function that consumes a state and returns a boolean.  Here,
though, we're not evaluating a conditional expression so much as returning the
expression itself, for a given state.  So, this means `LTL.atom` will want
to consume such a function, for an arbitrary state type sigma:

```lean4
namespace LTL
    def atom (p : σ → Prop) ... : Prop := ... -- NEW
end LTL
```

Since we're making a statement about a particular trace, `atom` needs to know
what trace that is:

```lean4
namespace LTL
    def atom (p : σ → Prop) (t : Trace σ) : Prop := ... -- NEW
end LTL
```

So that's the statement we want to assert and over what execution we want to
assert it.  We can now define what `atom` means: it's an assertion that the
proposition holds at the current moment.  Using our `now` helper from last
time, we can finish the definition.

To make use of `LTL.atom`, we use it as part of a `theorem`, just like any
other proposition in Lean.  

```lean4
namespace LTL
   def atom (p : σ → Prop) (t : Trace σ) : Prop := p (now t)
end LTL
```
::: margin-note
`rfl` is enough to discharge the proof of this theorem, but we can make a
more general statement: _for every_ trace where `t 0` is `init`, the hopper
starts out empty.  Can you state this formally and prove it?
:::
```lean4
def hopperEmpty (s : VMState) : Prop := s.coins = 0
def isCurrentlyEmpty := LTL.atom hopperEmpty

theorem startsEmpty : isCurrentlyEmpty (getFragment init getOrange) := by rfl
```

### `eventually` and `always` make existential and universal claims about traces

The first of the real modalities is `eventually`, which states that at some
point in the future, some statement holds.  (Symmetrically, `always` makes
the claim about a statement holding at every future point.)


`eventually` is an _existential_ proposition because it's saying _there exists_
some point in time where the statement is true, and dually, `always`
universally quantifies over _all_ subsequent points in time.  You could imagine
that `\exists` and `\forall` will likely appear somewhere in them, and indeed
that's the case:

```lean4
namespace LTL
    ...
    def always     /- TODO: what types are p and t? -/ : Prop := ∀ i, p (drop i t)
    def eventually /- TODO: what types are p and t? -/ : Prop := ∃ i, p (drop i t)
end LTL
```

As before, these definitions will take some `p` and `t` as argument.  `t` isn't
surprising: it's our `Trace σ`.  But, `p` clearly can't consume just an
individual state `σ` as it did in `atom`, because `drop` produces a whole new
`Trace σ`.  So, this is a predicate over _entire traces_:

```lean4
namespace LTL
    def always (p : Trace σ → Prop) (t : Trace σ) : Prop := 
      ∀ i, p (drop i t)
    def eventually (p : Trace σ → Prop) (t : Trace σ) : Prop := 
      ∃ i, p (drop i t)
end LTL
```

::: margin-note
"the diamond operator is a box that will _eventually_ fall over, whereas a
square operator will _always_ lie flat on the floor"?  I donno.
:::
`eventually` is sometimes abbreviated to the somewhat-opaque `F` (for _F_uture)
and the very-opaque `⋄`, and `always` to `G` (for _G_lobal) and `□`.  I will
suffer `F` and `G` since I kind of have a mnemonic for them, but "the diamond
operator" and "the square operator" will forever be utterly impossible for me
to keep straight.  Maybe writing this blog post will help, so let's create
new Lean syntax to accommodate them.  The `prefix:max` directive indicates that
they're prefix operators, bound as tightly as possible.

```lean4
namespace LTL
    ...

    prefix:max "□" => always
    prefix:max "◇" => eventually
end LTL

```

### `until` generalises `eventually` and `always`

Here's a more exotic modality: `p1 until p2` states that `p1` holds up to
some indeterminate point in the future, upon which `p2` will start to hold.

We can, in fact, write `always` and `eventually` in terms of `until`.

::: margin-note
`until` seems to be a reserved word??? So I'm just calilng it U.
:::
```lean4
namespace LTL
    ...
    def U (p1 : Trace σ → Prop) (p2 : Trace σ → Prop) (t : Trace σ) : Prop :=
      ∃ n, (∀ i, i < n → p1 (drop i t)) ∧ p2 (drop n t)

end LTL
```

`until` lets us make some fairly general statements: for instance, consider
saying "you don't get a can until you've paid":

```lean4
def mustPayFirst : Trace VMState → Prop :=
  LTL.U (LTL.atom (·.dispensed = none)) (LTL.atom (·.coins ≥ 2))
```

Applying this proposition to our sample trace isn't as scary as it might look:

```lean4
theorem allPaidUp : mustPayFirst (getFragment init getOrange) := by --TODO

1 goal
⊢ mustPayFirst (getFragment init getOrange)
```

First, let's unfold a bunch of our definitions (using `simp` so we can one-line it):

```lean4
theorem allPaidUp : mustPayFirst (getFragment init getOrange) := by
  simp [mustPayFirst, LTL.U, LTL.atom]

1 goal
⊢ ∃ n,
  (∀ (i : ℕ), i < n → (now (drop i (getFragment init getOrange))).dispensed = none) ∧
    2 ≤ (now (drop n (getFragment init getOrange))).coins
```

The goal is asking us to provide us with the point in the trace that satisfies
the `until`.  Because we know this particular trace, we know it's at index 2,
and that's enough to satisfy Lean.

```lean4
theorem allPaidUp : mustPayFirst (getFragment init getOrange) := by
  simp [mustPayFirst, LTL.U, LTL.atom]
  exists 2

Goals accomplished!
```

### `LTL.next` looks ahead one step

Here's our final true temporal modality: Given a trace, we can make a statement
about one unit of time in the future with the `next` (abbeviated `X`) operator:
after `U`, it's not that goofy looking:

```lean4
namespace LTL
    ...
    def next (p : Trace σ → Prop) (t : Trace σ) : Prop := p (drop 1 t)
end LTL
```

## The Curry-Howard correspondence, for time

::: note
(Note: the following section, and indeed, a lot of what is to come in this
series, was insprired by Alan Jeffrey's paper, [LTL Types
FLP](https://dl.acm.org/doi/epdf/10.1145/2103776.2103783).  All credit where
credit's due!)
:::

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
shows exactly what that connection is.

## A `Signal` is a time-varying value

Functional reactive programming is all about modeling your problem domain in
terms of how your program's values change over time.

In FRP, a _signal_ (sometimes called a _behaviour; I may use these terms
interchangably even though true FRP-heads would point out technical differences
between them) is such a time-parameterized value.

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

You might enjoy trying to define such a type in Lean.
:::
A functional reactive program, on the other hand, treats Signals as core
program values.  A `Signal Int` isn't "here's the integers that were observed
at time steps 0, 1, 2, ...", but rather "here's an integer that changes over
time; let's build other time-varying values out of it".  (How we actually _do_
that will come soon enough, but you can imagine that it might involve the
"functional" part of "FRP".)

## The Curry-Howard correspondence for `Signal`

Before proceeding, you should convince yourself of the fact that one way to
summarise a `Signal α` is as an `α` value that's always available, no matter
what time-step we're at.

Since the definition of `Signal` essentially makes an `α : T` available at all
points in time.  Since under Curry-Howard, `a` is a proof of `T`, 

TODO: introduce 

```
  namespace FRP
    notation "□" α => Signal α
  end FRP
```

## Some `Signal` and a few signal combinators

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

```lean4
def map (f: α → β) (s : □ α) : □ β := 
  fun t => f (s t)  

def map2 (f: α → β → γ) (s1 : □ α) (s2 : □ β) : □ γ := 
  fun t => f (s1 t) (s2 t)

def evens : □ Nat := map (· * 2) now
def incrementing := map2 (· + ·) (const 10) evens
#eval incrementing 42 -- at t=42, output is 94
```

These map functions are called _pointwise_ because they only operate on a
signal at the "present moment" (that is, whatever the value of `t` is). You
could imagine a _time-dependent tranformation_ that somehow involves other
values of `t` (say, computing the fininite difference of `t` and `t-1`)
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

## An `Event` occurs at some point in time

The dual of a `Signal` is an `Event`:

---
layout: post.njk
title: "LTL in Lean 4"
date: 2026-03-05
tags: [post, lean, reactive-programming]
excerpt: "Get in losers, we're doing temporal logic"
draft: true
---

## Last time...

Last time we implemented a simple reactive program in Lean.  We implemented a
pop machine `State`, datatype, an `Action` type, and a `step` function that
consumes a state, an action, and a _logical proposition_ encoding why the
action is valid for the given state, and produces a new state with that action
applied.

We also saw that while that step validity propsition was straightforward enough
to write for some concrete state, reactive programs change over time.  We need
our proof system to also be able to state facts about what we expect to happen
over time, too.

## This time...

We'll define _linear temporal logic_, which is a common logical system used by
model checkers like TLA+ and SPIN, and embed it into Lean's logical system.
We'll then see how to specify how our vending machine should behave over time,
with an eye to writing "real reactive programs" in Lean and specifying them
with LTL.

## Linear temporal logic

::: margin-note
LTL isn't the only temporal logic we could use - another one is _computation
tree logic_ (CTL) is another common logic that encodes _possible futures_ as a
tree of states, versus LTL's "linear sequence of states".  We could also add
the notion of probabilities into our logical system, making a transition system
more like a Markov chain.  Something to think about playing with another time.
:::
LTL is a _modal_ logic that let us refer to relationships between the ordering
of states, as opposed to statements (like `validStep s a`) which only speak
about some given state without any connection to what might happen later.  The
"linear" in LTL refers to the fact that what interests us is a sequential
_path_ of states in the system, determined by which actions were taken.  You
might that our "pay, pay, choose, take" example last time was actually a trace
just like this.

In practice formal methods folks like LTL because you can encode important
properties about real-world systems like fairness, which is important for
stating correctness about things from a spinlock up to a distributed consensus
protocol.

## The syntax of an LTL formula

Let's start implementing a _deep embedding_ of LTL in Lean by specifying
the ways to construct an LTL formula.  Since a statement in LTL relates to
some property about a reactive system's state (like our `VMState`), we're
going to parameterise LTL formulae on that state type.  (This means we couldn't
compose an `LTL VMState` with, say, an `LTL TrafficLightState`, but that's
probably okay here.)

::: margin-note
We'll be slightly fancy and use `σ` as our state type variable.  Typing
`\sigma` in the IDE will produce this character.
:::
```lean4
inductive LTL σ where
  | -- TODO: what are the constructors of an LTL formula?
```

Certainly, the present moment is a moment in time, so we ought to be able
to make a statement about a state "right now".  In a non-dependently-typed
language, we'd do this with a predicate function `σ → Bool`, but since
 we're really interested in writing proofs, let's return a `Prop` instead:

::: margin-note
Recall from last time that `(·.coins > 0)` is shorthand for `fun s => s.coins >
0`.
:::
```lean4
inductive LTL σ where
  | atom : (σ → Prop) → LTL σ -- NEW
  | -- TODO

def paidAnything : LTL VMState := LTL.atom (·.coins > 0)
```

(Even though we're still only specifying the syntax for LTL and not how to
interpret it, you probably have a rough sense of how to "evaluate" this formula
for a concrete state!)

OK, next: Propositional and first-order logic let us conjoin two propositions
with an `and`, as well as negate formulas with `not`.  (Combining those two
gets us `or`, of course!) We better be able to do the same here, too.

```lean4
inductive LTL σ where
  ...
  | and : LTL σ → LTL σ → LTL σ
  | neg : LTL σ → LTL σ
  ...

-- Derived LTL operators
namespace LTL


@[simp] def or      (a : LTL σ) (b : LTL σ) := LTL.neg <| LTL.and a b
@[simp] def implies (a : LTL σ) (b : LTL σ) := (LTL.neg a).or b

end LTL
```


So far all we've done is embedded `Prop` inside a cool new sum type.  Adding
some temporal modalities makes this logic more interesting!

### `next` refers to the subsequent state

Here's a simple one: Given some point in time, the `next` modality makes a
statement about the state to come:

::: margin-note
Might be worth thinking what states and actions might lead to the
`remainsStocked` example being true.
:::
```lean4
inductive LTL σ where
  ...
  | next : LTL σ → LTL σs
  ...

def fullyStocked : LTL VendingMachine :=
  (LTL.atom (·.numLL = 5)).and (LTL.atom (·.numOrange = 5))

def remainsStocked := LTL.next fullyStocked
```

### `eventually` and `always` make existental and universal statements

Here are some more exotic ones. `p1 until p2` states that `p1` will hold up to
some indeterminite point in the future, upon which `p2` will start to hold.
A special case of `until` is `eventually p`, which just says that at some point
in the future, `p` will hold.  Lastly, `always p` states just that: no matter
how far into the future we go, we can rely on `p` holding.

`eventually` is sometimes abbreviated to the somewhat-opaque `F` (for _F_uture)
and the very-opaque `⋄`, and `always` to `G` (for _G_lobal) and `□`.  I will
suffer `F` and `G` since I kind of have a mnemonic for them, but "the diamond
operator" and "the square operator" will forever be utterly impossible for me
to keep straight, so we'll pretend those don't exist.

::: martin-note
Technically, `eventually` can be defined in terms of `until`, and `always` can
be defined in terms of `eventually`, and so the textbook definition typically
doesn't include them in the snytax definition.  I think it'll simplify the
manual proofs to derive them explicitly, though, so we'll do so here.

You might enjoy trying to build those in terms of their simpler components,
though.
:::
```lean4
inductive LTL σ where
  ...
  | until : LTL σ → LTL σ → LTL σ
  | eventually: LTL σ → LTL σ
  | always: LTL σ → LTL σ

...
@[simp] def F (p : LTL σ) := LTL.eventually p
@[simp] def G (p : LTL σ) := LTL.always p
...
```

## Accumulating execution traces

Eventually we want to be able to write down statements about our pop machine's
behaviour over time, no matter how the user(s) use it.  Something we'd like to
have, in addition to carrying through the state of the system, is a record that
"at time `t`, `VMAction a` was taken on `VMState s`.  So, the idea is that if
we "folded over" all those actions, we'd end up with the final produced state.
(We don't have a real notion of time yet, despite all this talk about
"temporal" logic, so let's just say for now that every action that gets taken
advances our clock by one.)

### Choosing a datatype for traces

We'll see in a bit these execution traces are going to be really crucial for
writing proofs about our reactive systems, so we have to be careful about our
data definition for them.

Execution traces can be infinitely long (this is a bit hard to see in our
vending machine example, but consider the other canonical example, a traffic
light: it loops through its green-yellow-red sequence indefinitely.)   The
literature (in particular, Baier & Katoen's _Principles of Model Checking_ and
Lamport's _Specifying Systems_) typically use a functional approach, mapping
times to states (so, for us, that would look like a function `Nat -> (VMState *
VMAction)`.)

My natural inclination is to define a trace as an `Iterator (VMState *
VMAction)`, though, so I'm going do to that here instead.  If in a later blog
post I discover the error of my ways and revert back to the more general
functional definition, I'll leave a backpointer to this paragraph; if I had a
comment section all ya'll could make fun of me there.

[Writer](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Control/Monad/Writer.html)
monad for this, which allows us to mix in "accumulating log entries"-like
behaviour.  Here's our new `TSM` monad:

```lean4
import Mathlib.Control.Monad.Writer

...

abbrev TSM α := WriterT (List VMAction) (StateT VMState (Except String)) α

def perform (a : VMAction) : TSM Unit := do
  let s ← get
  if h : validAction s a then
    tell [(s, a)] -- NEW: appends this "log entry" to the Writer's state
    let s' := vmStep s a h
    set s'
  else Except.error s!"Invalid action {repr a} in state {repr s}"

...

#eval getOrange.run init 

Except.ok (
  (LemonLime,
  [({ coins := 0, dispensed := none,           numOrange := 5, numLL := 5 }, DropCoin),
   ({ coins := 1, dispensed := none,           numOrange := 5, numLL := 5 }, DropCoin),
   ({ coins := 2, dispensed := none,           numOrange := 5, numLL := 5 }, Choose LemonLime),
   ({ coins := 0, dispensed := some LemonLime, numOrange := 5, numLL := 4 }, TakeItem)]),
 { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```


## 

---
layout: post.njk
title: "Reactive Programming in Lean Part 2: Execution traces"
date: 2026-03-15
tags: [post, lean, reactive-programming]
excerpt: "Recording and reasoning about the states our programs pass through"
series: lean-ltl
series_title: "Part two - execution traces"
---

## Welcome back!

Last time we implemented a simple reactive program in Lean.  We implemented a
pop machine `State` datatype, an `Action` type, and a `step` function that
consumes a state, an action, and a _logical proposition_ encoding why the
action is valid for the given state, and produces a new state with that action
applied.

We also saw that while that step validity proposition was straightforward enough
to write for some concrete state, reactive programs change over time.  We need
our proof system to also be able to state facts about what we expect to happen
over time, too.

[Here](https://live.lean-lang.org/#codez=LTAEGUBcENIUwM4CgkEsB2ATArgY0qgG5ygBiANtIQPbYBOoA7gBZx1xKigA+oA8nWjoA5hy68AMnAC21dBNTSOmNkQzDQAJTgAHOigSQ6eSPRIA1ALJRYJFmzGhc1DAgBcoAHKxOoTKgQdOHQEOEwPPh0COTJKGnpfdGxpASFRUA9vSETkiQkMrx8VOjURLV19JBBQAEF8VDlkNCwTIgtLOuj0JlZ2X14AETpqHQBhF3R+0FHmampQgooqWgZAJMJQK06GyfFyw2pcAGspgBVoQ7gASXhpJGLSjW09FAABAG0ERR0AXTu4ADNQIRoORUJgtjEABQIApWGzwACUoEh0FhHXqciRHgACsMdBkALy+aSwXDMUCoxioSDMKYAOiGI3GGC4rLZoAJAD5QCdjI5eHTtPsjuzRVyeXz6TM5gs6akRCRWeKEHTnK5QJyCaAAEygQDkRKAVUkUoIFRrQAAGKWzeYkOlSWTyRQkZWqiYwzU6/WGunGvLmq27OlnC7XGSitniyJdOkBcDUJQ+/yBYKhTAoFSAjDUtHwkhuLUAb1AvjVIUJloANH4AkEQmEK+g5HBq8b5ekC6AAKyt3L5TtdksAXxQ1Sguh06gzAKB0nH+OhuZgiJLEbZKLREPQSN8a+RAAkCsDQeCMd0YdAEbu1x44cv80SuCTIGSKUxqbSg4yxhM1+LizCVI0k47oViqZYwgA1KAACMoAjkGIZXDcf7cgB77AcmdZpo2zbwdaMp2u2ir/oaGGfqyEHsp24GgWA2qVtebamh2WpGskxGgGAMHXlhqYNjRCZESxLa+AhPCgHS0q2pJDpyAoiakYBH7XlRbI0W66r0YxbJ+vk6lsb6fZcbBvG1vxmBgUJskyPJzo6fhQZCpAByHHu4rZtkzSGEIuAkIut7WPeSIboFW5YqAAxwLgYLQAARuQ/nHmCW5kZeFZxQAnr4nzSDoADcho6KCkCgAAPPl3IYP8bAAPquDA6B+aOYBwAAHtF2BdE08VxewhA8uAligIAjcAVnmJwbEFtjIgAom1flRBARjqEiI3ToCQR0P81B0NIyKomFZ4RScQ2gAAqugOadpg1C+IlpUwoACYSgKI2RcKggLkh4yWnl0aWgDSwTXg9hoAOQVoQc7wPiF6gBRXChI9YO+HA5ALPNi2QHSbDDAwCAAIQAESXOgv0UmeoCFuwegUkOoAsj58BUzT+NDkTG2A+c+aDcNSzxAwN13VwoPPa9cDvQzgKHj9IIpZTMLBtzYb7UDOysltO17ZJSEq9eOhmMi0bbHSb1JuZ9aWfuV5cGjGMLbo2O47thrE541A0uogPUFzFwM+e94sxUhrs5zb2cR4p183EKwVrdvia7t+2QgyeLMtuCdsFryep0yEw26Aifayn0mynJTpKAXMAXEgQA)
is a Lean playground with the state of our program from last time.

We'll define _execution traces_, which are a conceptually-infinite series of
steps that a system like our vending machine can take, and we'll extend our
monadic interpreter to produce such traces.  We'll soon hit the limits of
expressivity in terms of what sorts of `Prop`s we can write over such traces,
which we'll use to broaden our theorem vocabulary into richer program logics in
subsequent posts.

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
Except.ok (Flavour.LemonLime, { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```

There are all sorts of propositions we could write about the final state:
maybe we want to be assured that the machine successfully ate all the coins
in the hopper, or that we didn't accidentally decrement `numOrange` versus
`numLL`.  We could also write and prove the statement `validStep <final state>
.DropCoin`, or write and _refute_ `validStep <final state> .TakeItem`.

These kind of aren't terribly _interesting_ propositions, though, and this
makes sense because what makes reactive programs interesting is that they change
over time.  So, our logical propositions also need to be able to talk about
change over time.

## Time and execution traces

We're going to define our sequence of states as "the states of the system at
time `t`".

We don't have a real notion of time or how long an action takes, so let's just
say for now that every action that gets taken advances our clock by one, so at
`t = 0` we're in our system's initial state, and after taking our first action,
the state advances to the value for `t = 1`.  Time for us is kind of an
arbitrary quantity; we're less interested in what unit `t` has and more that
assigning time a number lets us _order events_: if `i < j`, then we know the
action that happened at `t = i` must have happened before the one at `t = j`.

So, an _execution trace_ relates "at what time are we" to "what's the state of
the system".  And by our choice of time, every time has a state, and we can
reason about the order in which states occurred, because we can reason about
the order of time steps themselves.

### Choosing a datatype for time

A lot of papers like to, in my opinion, overengineer the definition of time,
with a fancy typeclass and monadic operations and a proof of total order.
We're going to just do the simplest thing here, which is to say that time is
over the natural numbers.  This fits what we said earlier: the first state's
timestep is "the first natural number", every action advances the clock to "the
next natural number", and we can keep doing that, conceptually, infinitely many
times.  This means we'll always have a well-defined initial state of the
system, but it doesn't make sense to talk about "the system's final state".

```lean4
abbrev Time := Nat
```

### Choosing a datatype for traces

OK, so given a time value, how should we get a state? We'll see in a bit these
execution traces are going to be really crucial for writing proofs about our
reactive systems, so we have to be careful about our data definition for them.

::: margin-note
My natural inclination, as more a hacker than a mathematician, is to think in
data structures like defining a trace as an `Iterator (VMState * VMAction)`,
though.  But, in the spirit of not second-guessing those who've come before,
I'll stick with the more functional definition.
:::
Since `Nat`s can be infinitely large, execution traces can be infinitely long.
For reactive systems this is the thing we want (this is a bit hard to see in
our vending machine example, but consider the other canonical example, a
traffic light: it loops through its green-yellow-red sequence indefinitely).
The literature (in particular, Baier & Katoen's _Principles of Model Checking_
and Lamport's _Specifying Systems_) typically use a functional approach,
mapping times to states (so, for us, that would look like a function `Nat ->
VMState`.)

(Of course, the particular example we have is _finite_: it only defines states
at time 0, 1, 2, and 3.  We'll say a bit shortly about how to take a _finite
trace fragment_ and extend into a proper infinite trace.)

(Conal Elliott, whose work will come into play in later chapters, has
[bemoaned](https://www.youtube.com/watch?v=rfmkzp76M4M) discretizing time like
we're doing here.  We'll refine this definition of time soon enough.)

### All time is relative

One of the things we _don't_ have is the notion of a global clock that tells
us what, at some moment, "the current time is".  Instead, we'll use a notion
of relative time: `t = 0` is always "right now", and if we want to "advance the
clock", we need return a new trace function that offsets the input value by the
right time delta.  If this is confusing, think back to the `Iterator` example:
the current state is always at element 0 -- the head -- of the iterator, and to
advance the clock by, say, three time units, we'd drop the first three elements
from the iterator.

::: margin-note
It feels significant to me that some of the best distributed systems
programmers I know majored in physics: I'm sure they wouldn't find "all time is
relative" to be all that scary of a notion.
:::
```lean4
def Trace α := Time → α

def now (t : Trace α) : α := t 0
def drop (k : Nat) (t : Trace α) : Trace α := fun n => t (k + n)
def next : Trace α → Trace α := drop 1
```

## Traces, concretely

Let's get our bearings by accumulating finite traces from our monadic API. 

Remember that `Trace`s are conceptually-infinite in length, so when we actually
execute a series of actions, we're actually producing a _trace fragment_. (This
is sometimes called a _trace prefix_ or just a finite trace.)  Fragments will
be produced by executing our TSM monad - the only thing we have to do to make
this happen is to accumulate the states we transition to.

The thing is, `TSM` now has _two_ interpretations: the "execute a sequence of
actions, producing a final state or an error" one, and also the "just give me
all the sequence of states".  These interpretations aren't fundamentally different
from each other, so we could try and maintain a stateful list of transitioned
states, or maybe use the
[Writer](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Control/Monad/Writer.html)
monad, which allows us to mix in "emitting log entries"-like behaviour.  

```lean4
import Mathlib.Control.Monad.Writer

...
abbrev Fragment := List VMState
abbrev TSM α := WriterT Fragment (StateT VMState (Except String)) α
```

`TSM` is three monads stacked together, which is kind of convoluted, but
we only need to know that this monad now imbues computation in `TSM`
with a new `tell` function, which records `VMStates` as we come across them:

:::margin-note
A sufficiently-complicated monad transformer stack actually makes it _easier_
to see why monads are an interesting way to program: every monad can be seen as
introducing a new "language feature": `State` introduces, well, mutable state,
`Except` introduces exception raising, and now `Writer` introduces output
logging, none of which are obviously present in a pure functional language!
:::
```lean4
def perform (a : VMAction) : TSM Unit := do
  let s ← get
  if h : validAction s a then
    tell [s] -- NEW: remember that we saw [s]
    let s' := vmStep s a h
    set s'
  else Except.error s!"Invalid action {repr a} in state {repr s}"

...

#eval getOrange.run init 

Except.ok (
  (LemonLime,
  [{ coins := 0, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 1, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 2, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 0, dispensed := some LemonLime, numOrange := 5, numLL := 4 }]),
 { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```

With a little helper, we can pull out only the fragment from a computation.
In fact, while we're doing so, why don't we turn that fragment into a proper
trace:

::: margin-note
You may disagree with my choice of return value of `.error`: since we will only
use this for a few examples, feel free to change it to a `panic!`, after you
solve the type error that it creates for you >:)
:::
```lean4
def getFragment (init : VMState) (tsm : TSM σ) : Trace VMState :=
  match (tsm.run init) with
  | .ok ((_, frag), final) =>
    (fun n => if h : n < frag.length then frag.get ⟨n, h⟩ else final)
  | .error e => (fun _ => init)

def orangeTrace : Trace VMState := getFragment init getOrange
```

Here, we make the trace well-defined by saying it's just staying in the same
state for all points in time after the final transition.  You might think
another way to do this would be to just loop back to the first action and
repeat the sequence over and over again, but this wouldn't work for this trace;
we'd eventually run out of pop cans to dispense so we'd get stuck.  

To ask about the state after the first coin drop, we could evaluate
`orangeTrace 1`; to produce a _new_ trace that begins after the first coin
drop, we could evaluate `drop 1 orangeTrace`.  Constructing new traces out of
old ones will become super important in future posts.

```lean4
#eval orangeTrace 0   -- { coins := 0, dispensed := none, numOrange := 5, numLL := 5 }
#eval orangeTrace 3   -- { coins := 0, dispensed := some (VM.Flavour.LemonLime), numOrange := 5, numLL := 4 }
#eval orangeTrace 42  -- { coins := 0, dispensed := none, numOrange := 5, numLL := 4 }
```

While we're on the topic, though, you should pause and ponder about whether
"just staying in the same state" is something that the pop state machine would
actually permit...

## Proofs over finite traces

Since at the end of the day, `orangeTrace` is just a function, it's really easy
to write some simple propositions about specific states in that trace:

```lean4
example : (orangeTrace 0).coins = 0 := by rfl
example : (orangeTrace 2).coins = 2 := by rfl
example : (orangeTrace 3).dispensed = some .LemonLime := by rfl
```

Even though the `TSM` monad ensures we don't return an invalid trace, we could
also write a proposition over _transitions_ between states:  Say, for instance,
we might want to assert that what action takes us from `orangeTrace 2` to
`orangeTrace 3` is `Choose .LemonLime`.  That's easy to prove, too:

::: margin-note
Technically, this is saying "there's a valid proof that this step is valid, and
stepping produces the next step".
:::
```lean4
example : ∃ h, orangeTrace 3 = vmStep (orangeTrace 2) (.Choose .LemonLime) h := by
  exact ⟨by decide, by rfl⟩
```

`⟨_, _⟩` introduces the existential witness; it's `Exists.intro` in anonymous
constructor syntax. `by decide` fills the first slot: it evaluates `validAction
(orangeTrace 2) (.Choose .LemonLime)` computationally (using the Decidable
instance) and confirms it's true. `by rfl` fills the second slot: it evaluates
both sides of the equality — `orangeTrace 3` and `vmStep (orangeTrace 2)
(.Choose .LemonLime) h` — and confirms they reduce to the same value.

We can generalise proofs about `orangeTrace`, too.  The previous example picked
a specific action (`Choose .LemonLime`) and a specific state and showed
stepping was valid.  But we could also weaken the claim and just ask "there
exists _some_ valid action connecting these two states":

```lean4
example : ∃ a, ∃ h : validAction (orangeTrace 2) a, 
    orangeTrace 3 = vmStep (orangeTrace 2) a h := by
  exact ⟨.Choose .LemonLime, by decide, by rfl⟩
```

The shape of the statement "there exists an action, a proof that the action is
valid, and a proof that the step matches the action taken" is exactly what we
need to say about every consecutive pair of states in a trace.

## Valid traces

We'll call an entire trace _valid_ if two conditions hold:

1. **Initialization**: the trace starts in a known initial state.
2. **Consecution**: every consecutive pair of states is connected by some valid action.

::: margin-note
It might be worth pondering about the relationship between a valid trace and an
inductive invariant, and what sorts of invariants might not be inductive.
:::
```lean4
def validTrace (t : Trace VMState) : Prop :=
  t 0 = init ∧
  ∀ i, 
    ∃ a, 
      ∃ h : validAction (t i) a, 
        t (1 + i) = vmStep (t i) a h
```

The initialization condition is easy to check for `orangeTrace`:

```lean4
example : (orangeTrace 0) = init := by rfl
```

And we've essentially been proving consecution for individual steps already.
We just showed that step 2 leads to step 3 via `Choose .LemonLime`; verifying
the other transitions is the same pattern:

```lean4
example : ∃ a h, orangeTrace 1 = vmStep (orangeTrace 0) a h :=
  ⟨.DropCoin, by decide, by rfl⟩

example : ∃ a h, orangeTrace 2 = vmStep (orangeTrace 1) a h :=
  ⟨.DropCoin, by decide, by rfl⟩
```

### Our concrete trace isn't an infinite valid trace

You might be tempted to prove `validTrace orangeTrace` outright, but there's a
snag.  

Remember that `getFragment` extends the finite trace by repeating the
final state forever: `orangeTrace 4 = orangeTrace 5 = orangeTrace 6 = ...`.
For that to satisfy consecution, we'd need some action that is both valid _and_
leaves the state unchanged.  But there isn't one: `DropCoin` increments
`coins`, `Restock` resets to `init`, `Choose` dispenses a can, and `TakeItem`
isn't valid when nothing's been dispensed.  (If we'd instead had the machine
restock itself indefinitely, then the trace would be a valid one.)

So our `getFragment` helper produced a well-defined _function_ `Nat → VMState`,
but the infinite extension is not a valid _trace_ in our formal sense.  That's
fine.  We can still verify the finite prefix step-by-step, which is useful for
testing concrete executions.

In general: if you consider all the possible states the vending machine can
find itself in, only some of those will be valid (insofar as the system's
invariants don't forbid them), and only some of _those_ will actually ever be
reachable (insofar as the transition function of the system doesn't preclude
stepping to them).

## The limits of what we can express

For our concrete `orangeTrace`, we can point at specific time steps and verify
whatever we like.  What's a lot harder is to make such statements about
_arbitrary_ traces, where the only thing we know is that at every step they
satisfy `validTrace`.

Consider a statement like "a can was dispensed and it hasn't been taken".  We'd
need to be able to say something like "at some point `t` a can was dispensed,
and for all times between then and now, it wasn't taken."  This is about
quantifying over _part of a trace itself_, and we don't have the vocabulary to
make that statement yet.

## Next time: temporal propositions

Today we built up some mechanism to reason about specific states in our traces.
Next time we are going to introduce _temporal logic_, which will let us make
statements of the form "eventually a can will dispense", or "it will never be
the case that you get a can for free".

We'll also switch to a new running example; a vending machine only has one user
at a time, whereas _concurrency_ is an innate attribute of many reactive programs. 
There's something else worth noticing about our vending machine. The fields in
`VMState` -- `coins`, `dispensed`, `numOrange`, `numLL` --  are all packed into
a single record.  We can't talk about how `dispensed` evolves without `coins`.

To put it differently: our trace is one monolithic signal: at each point in
time, we get the entire state of the world.  Reformulating our system as a
composition of signals will open up a broader set of problems to model.

We won't have to throw away much to generalise this, though.  Notice that
`Trace α := Time → α` is a very general type, and stepping a state machine
isn't the only kind of system that can yield such a trace. In a spreadsheet, if
cell `C` says `A + B`, the relationship between `C` and its dependencies moves
through time independently of, say, `D` and `E`. In aggregate, a spreadsheet
doesn't form a single monolithic trace, but rather a constellation of
interconnected ones. 

Next time, we'll see what temporal properties look like for systems like that.

---
layout: post.njk
title: "LTL in Lean 4"
date: 2026-03-15
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

[Here](https://live.lean-lang.org/#codez=LTAEGUBcENIUwM4CgkEsB2ATArgY0qgG5ygBiANtIQPbYBOoA7gBZx1xKigA+oA8nWjoA5hy68AMnAC21dBNTSOmNkQzDQAJTgAHOigSQ6eSPRIA1ALJRYJFmzGhc1DAgBcoAHKxOoTKgQdOHQEOEwPPh0COTJKGnpfdGxpASFRUA9vSETkiQkMrx8VOjURLV19JBBQAEF8VDlkNCwTIgtLOuj0JlZ2X14AETpqHQBhF3R+0FHmampQgooqWgZAJMJQK06GyfFyw2pcAGspgBVoQ7gASXhpJGLSjW09FAABAG0ERR0AXTu4ADNQIRoORUJgtjEABQIApWGzwACUoEh0FhHXqciRHgACsMdBkALy+aSwXDMUCoxioSDMKYAOiGI3GGC4rLZoAJAD5QCdjI5eHTtPsjuzRVyeXz6TM5gs6akRCRWeKEHTnK5QJyCaAAEygQDkRKAVUkUoIFRrQAAGKWzeYkOlSWTyRQkZWqiYwzU6/WGunGvLmq27OlnC7XGSitniyJdOkBcDUJQ+/yBYKhTAoFSAjDUtHwkhuLUAb1AvjVIUJloANH4AkEQmEK+g5HBq8b5ekC6AAKyt3L5TtdksAXxQ1Sguh06gzAKB0nH+OhuZgiJLEbZKLREPQSN8a+RAAkCsDQeCMd0YdAEbu1x44cv80SuCTIGSKUxqbSg4yxhM1+LizCVI0k47oViqZYwgA1KAACMoAjkGIZXDcf7cgB77AcmdZpo2zbwdaMp2u2ir/oaGGfqyEHsp24GgWA2qVtebamh2WpGskxGgGAMHXlhqYNjRCZESxLa+AhPCgHS0q2pJDpyAoiakYBH7XlRbI0W66r0YxbJ+vk6lsb6fZcbBvG1vxmBgUJskyPJzo6fhQZCpAByHHu4rZtkzSGEIuAkIut7WPeSIboFW5YqAAxwLgYLQAARuQ/nHmCW5kZeFZxQAnr4nzSDoADcho6KCkCgAAPPl3IYP8bAAPquDA6B+aOYBwAAHtF2BdE08VxewhA8uAligIAjcAVnmJwbEFtjIgAom1flRBARjqEiI3ToCQR0P81B0NIyKomFZ4RScQ2gAAqugOadpg1C+IlpUwoACYSgKI2RcKggLkh4yWnl0aWgDSwTXg9hoAOQVoQc7wPiF6gBRXChI9YO+HA5ALPNi2QHSbDDAwCAAIQAESXOgv0UmeoCFuwegUkOoAsj58BUzT+NDkTG2A+c+aDcNSzxAwN13VwoPPa9cDvQzgKHj9IIpZTMLBtzYb7UDOysltO17ZJSEq9eOhmMi0bbHSb1JuZ9aWfuV5cGjGMLbo2O47thrE541A0uogPUFzFwM+e94sxUhrs5zb2cR4p183EKwVrdvia7t+2QgyeLMtuCdsFryep0yEw26Aifayn0mynJTpKAXMAXEgQA)
is a Lean playground with the state of our program from last time.

## This time...

We'll define temporal logic and _linear temporal logic_, which is a common
logical system used by model checkers like TLA+ and SPIN, and embed it into
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

```
#eval getOrange.run init
Except.ok (Flavour.LemonLime, { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```

There are all sorts of propositions we could write about the final state:
maybe we want to be assured that the machine successfully ate all the coins
in the hopper, or that we didn't accidentally decrement `numOrange` versus
`numLL`.  We could also write and prove the statement `validStep <final state>
.DropCoin`, or write and _refute_ `validStep <final state> .TakeItem`.

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
protocol.

## Time and execution traces

We're going to define our sequence of states as "the states of the system at
time `t`".

We don't have a real notion of time or how long an action takes, despite all
this talk about "temporal" logic, so let's just say for now that every action
that gets taken advances our clock by one, so at `t = 0` we're in our system's
initial state, and after taking our first action, the state advances to the
value for `t = 1`.  Time for us is kind of an arbitrary quantity; we're less
interested in what unit `t` has and more that assigning time a number lets us
_order events_: if `i < j`, then we know the action that happened at `t = i`
must have happened before the one at `t = j`.

So, an _execution trace_ relates "at what time are we" to "what's the state of
the system".  And by our choice of time, every time has a state, and we can
reason about the order in which states occurred, because we can reason about
the order of time steps themselves.

### Choosing a datatype for time

A lot of papers like to, in my opinion, overengineer the definition of time,
with a fancy typeclass and monoidial operations and a proof of total order.
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
I'll stick with the more functional defintion.
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

def drop k (t : Trace α):= fun n => t (k + n)
def next (t : Trace α) := fun n => t (n
```

## The syntax of an LTL formula

OK, we have the notion of time, and our notion of traces, but not yet a way of
writing propositions about how our system changes over time.

Let's start implementing a _deep embedding_ of LTL in Lean by specifying the
ways to construct an LTL formula.  Since a statement in LTL relates to some
property about a reactive system's state (like our `VMState`), we're going to
parameterise LTL formulae on that state type.  (This means we couldn't compose
an `LTL VMState` with, say, an `LTL TrafficLightState`, but that's probably
okay here.)  Similarly, this means that our `Trace` datatype is concretely a
`Nat -> VMState` function.

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

```lean4
inductive LTL σ where
  | atom : (σ → Prop) → LTL σ -- NEW
  | -- TODO

def hopperEmpty (s: VMState) : Prop := s.coins > 0

def hopperCurrentlyEmpty : LTL VMState := LTL.atom hopperEmpty
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


@[simp] def or      (a : LTL σ) (b : LTL σ) := 
  LTL.neg <| LTL.and (LTL.neg a) 
                     (LTL.neg b)
@[simp] def implies (a : LTL σ) (b : LTL σ) := (LTL.neg a).or b

end LTL
```

Here we've defined `or` and `implies` in terms of our core LTL primitives,
but wrapping them in the `LTL` namespace means external users won't know
the difference.

### `next` refers to the subsequent state

So far all we've done is embedded `Prop` inside a cool new sum type.  Adding
some temporal modalities makes this logic more interesting!

Here's a simple one: Given some point in time, the `next` modality makes a
statement about the state to come:

::: margin-note
Might be worth thinking what states and actions might lead to the
`remainsStocked` example being true or being falsified.
:::
```lean4
inductive LTL σ where
  ...
  | next : LTL σ → LTL σs
  ...

-- examples

def fullyStocked : LTL VendingMachine :=
  (LTL.atom (·.numLL = 5)).and (LTL.atom (·.numOrange = 5))

def remainsStocked := LTL.next fullyStocked
```

Here is a more exotic one. `p1 until p2` states that `p1` will hold up to some
indeterminite point in the future, upon which `p2` will start to hold. 

```lean4
inductive LTL σ where
  ...
  | until : LTL σ → LTL σ → LTL σ
```

### `eventually` and `always` make existental and universal statements

A special case of `until` is `eventually p`, which just says that at some point
in the future, `p` will hold.  Lastly, `always p` states just that: no matter
how far into the future we go, we can rely on `p` holding.

`eventually` is sometimes abbreviated to the somewhat-opaque `F` (for _F_uture)
and the very-opaque `⋄`, and `always` to `G` (for _G_lobal) and `□`.  I will
suffer `F` and `G` since I kind of have a mnemonic for them, but "the diamond
operator" and "the square operator" will forever be utterly impossible for me
to keep straight, so we'll pretend those don't exist.

`eventually` is an _existential_ proposition because it's saying _there exists_
some point in time where the statement is true, and dually, `always` universally
quantifies over _all_ subsequent points in time.  We haven't written down the
semantics of these formulas yet but you could imagine that `\exists` and
`\forall` will likely appear somewhere in them.

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

So, in total, here's our LTL formula syntax.  Now that we have it all in place,
it's worth thinking about what isn't expressible in this logic: A few come to
mind for me:

* We only have _forward-looking_ temporal operators.  The past-tense equivalent
  of `eventually` could be, I donno, `previously`, or something.  Since we
  don't have the notion of negative relative time, though, this might require
  rethinking our `Time` type definition, though.
* Nothing stops us from writing _quantified statements_ of the form "for all
  possible states, ..." or "there exists a state such that..."  (We get quantifiers
  for free because `atom`'s "predicate" function produces a Lean proposition,
  which can hold them!).  What we can't do, though, is quantify over _time_, like
  to say "for every other timestep, ..."
* It might be interesting to ascribe probabilities of some proposition being true-
  "eventually" could then become a "as time goes to infinity, P(some_proposition) -> 1"
  sort of statement.  But, our logic here isn't "fuzzy" in that sense.

::: tip
```lean4
inductive LTL σ where
  | atom : (σ → Prop) → LTL σ
  | and : LTL σ → LTL σ → LTL σ
  | neg : LTL σ → LTL σ
  | next : LTL σ → LTL σ
  | until : LTL σ → LTL σ → LTL σ
  | eventually: LTL σ → LTL σ
  | always: LTL σ → LTL σ

-- Our derived LTL operators
namespace LTL

@[simp] def or      (a : LTL σ) (b : LTL σ) := 
  LTL.neg <| LTL.and (LTL.not a) 
                     (LTL.not b)
@[simp] def implies (a : LTL σ) (b : LTL σ) := (LTL.neg a).or b

@[simp] def F (p : LTL σ) := LTL.eventually p
@[simp] def G (p : LTL σ) := LTL.always p

end LTL
```
:::

## The semantics of an LTL formula

All we've done so far is define a new datatype, but we haven't imbued it with
any real concrete meaning yet.  This is kind of like defining an `Expr` datatype
for some language, but not implementing an `eval()` function.

## I demand satisfaction!

We said earlier that we need an "interpreter" or `eval()` for our formula
language.  We can't "execute" an LTL formula, but we _can_ ask whether our
formula "evaluates to true or false", for a given trace, in a not-dissimilar
way.  Let's write the function `models` that does this for us:

```lean4
@[simp]
def satisfies : Trace σ → LTL σ → Prop
  | t, LTL.atom p =>       -- TODO
  | t, LTL.and a b =>      -- TODO
  | t, LTL.neg s =>        -- TODO
  | t, LTL.next s =>       -- TODO
  | t, LTL.until a b =>    -- TODO
  | t, LTL.eventually s => -- TODO 
  | t, LTL.always s =>     -- TODO
```

A lot of these don't require much thought and just fall out from the recursive
definition of formulas: An `and` contains two subformulae, and is simply the
conjunction of its two formulas' satisfiability; and, `neg` wraps a subformula,
and is the negation of its satisfiability. We can write those down without too
much difficulty.

```lean4
@[simp]
def satisfies : Trace σ → LTL σ → Prop
  ...
  | t, LTL.and a b => satisfies t a ∧ satisfies t b -- NEW
  | t, LTL.neg s =>  ¬ (satisfies t s) -- NEW
  ...
```

We might have to think a bit, but only a bit, harder about `atom`.  `p` is
our "predicate over states", and in particular we're interested in the state
at the present, which `t 0` will give us.  Similarly, `next` wants us to reason
about `t 1`.  So, we have:

```lean4
@[simp]
def satisfies : Trace σ → LTL σ → Prop
  | t, LTL.atom prop => prop (t 0)
  ...
  | t, LTL.next s => satisfies (next t) s
```

Now `until` is a slightly gnarly one.  Informally: "`a` holds until some point
in the future, at which point `b` then holds".  Formally: we have to
existentially quantify over how long `a` is going to hold before `b`:

```lean4
def satisfies : Trace σ → LTL σ → Prop
  | t, LTL.until a b => 
    ∃ (n : Nat),
      ∀ (i : Nat), 
        i < n → satisfies (drop i t) a ∧ satisfies (drop n t) b
```

::: martin-note
Technically, `eventually` can be defined in terms of `until`, and `always` can
be defined in terms of `eventually`, and so the textbook definition typically
doesn't include them in the snytax definition.  I think it'll simplify the
manual proofs to derive them explicitly, though, so we'll do so here.

You might enjoy trying to build those in terms of their simpler components,
though.
:::
The remaining two can be read off as "something eventually is satisfied if
there exists some point in the future where it is satisfied" and "something
always is satisfied if for all points in the future, it is satisfied".

```lean4
def satisfies : Trace σ → LTL σ → Prop
...
  | t, LTL.eventually s => ∃ (n : Nat), satisfies (drop n t) s
  | t, LTL.always s     => ∀ (i : Nat), satisfies (drop i t) s
```


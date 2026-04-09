---
layout: post.njk
title: "Reactive Programming in Lean Part 4: Functional Reactive Programming"
date: 2026-04-17
tags: [post, lean, reactive-programming]
excerpt: "So if propositions are types, and LTL are propositions, what programs are well-typed by LTL?"
draft: true
series: lean-ltl
series_title: "Part four - OMG WTF LTL FRP BBQ"
---

# The Curry-Howard correspondence for LTL: FRP

So far, what we've been doing is playing with LTL in the way that someone using
a model checker like TLA+ might.  We implemented a reactive system, executed
some traces over that system, and wrote formulas to answer "does this trace
satisfy this formula?"  Later on, we saw how some formulas can be answered no
matter which (valid!) trace is under consideration.  That's a pretty powerful
set of tools to reason about software.

All the dependently-typed programming we've done in this and other series has
shown the _Curry-Howard correspondence_ in action.  When we say "a `Prop` is a
type" and "we prove a proposition by writing a program that typechecks to it",
that's Curry-Howard in action.

Last time, we extended the notion of a `Prop` to temporal logic in order to
reason about temporal programs.  By Curry-Howard, that must mean that there are
some program types (and therefore program compuatations) that align with those
propositions.  The *LTL Types FRP* paper shows exactly what that connection is:
it's to a programming model called _functional reactive programming_.

In FRP, your core program values (which we'll see soon are called _signals_)
are _time-varying_, and you build your program by composing these signals using
pure functions.  Instead of thinking about our reactive systems imperatively,
where we're mutating a state structure action by action, FRP is about building
relationships between different values in a way that should feel natural to you
if you've programmed functionally before.

The *LTL types FRP* paper builds up a formulation that shows that under
Curry-Howard, the LTL logic maps to types of value in an FRP program.  Building
this connection up will be the ultimate goal of this post; by the end of it, we
should end up with two Lean namespaces that look pretty similar in structure
and function.

```lean4
-- From Part 3 (last time)
namespace LTL
    ...
end LTL

-- From Part 4 (this part!)
namespace FRP
    ...
end FRP
```

## A `Signal` is a time-varying value

We just said that FRP is all about modeling your problem domain in terms of how
your program's values change over time.  So, we better have a means to model
time itself.

::: margin-note
We're sticking with just natural numbers for keeping time here, but the
original FRP formulation was pretty particular about time being "real numbers".
FRP was originally designed for graphics programming, so having a dense time
representation made it easy to, for instance, contract and extend time to speed
up or slow down animation speeds.  

But, by hiding the actual type behind `Time`, hopefully this buys us the
ability to swap out a different time notion of a clock later on.
:::
```lean4
abbrev Time := Nat
```

In this programming model, a _signal_ (sometimes called a _behaviour_) is such
a time-parameterized value.

```lean4
abbrev Signal α := Time → α
```

Notice that this the same type as our execution traces!  That's not entirely a
coincidence.  The _interpretation_ of a signal is different, though.  Earlier,
a `Trace` was an artifact of running some computation; it was in some sense an
"output".  You can poke at the trace by writing theorems about it, but it
otherwise just sits there; running the system through our monadic API produced
it, and then we use Lean's theorem proving capabilities to inspect it.

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


## Some `Signal`s

Here's our first `Signal`, which doesn't do more than act as a "what time is it"
clock:

```lean4
def clock : Signal Time := 
  fun t => t --At time step t, our output is t itself
```

Just like with LTL's `drop`, we can delay the value of a signal of any time by
shifting it forward in time:

```lean4
def delay (s: Signal α) (t: Time): Signal α := fun n => s (n+t)

#eval (delay clock 3) 5 -- At t=5, a clock delayed by 3 is 8
```

Next, let's define a way that lifts a value into the world of `Signal`s:

```lean4
def const (v: α) : Signal α := fun _ => v

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
def map (f: α → β) (s : Signal α) : Signal β := 
  fun t => f (s t)  

def map2 (f: α → β → γ) (s1 : Signal α) (s2 : Signal β) : Signal γ := 
  fun t => f (s1 t) (s2 t)
```
These map functions are called _pointwise_ because they only operate on a
signal at the "present moment" (that is, whatever the value of `t` is). You
could imagine a _time-dependent transformation_ that somehow involves other
values of `t` (say, computing the finite difference of `t` and `t-1`)
but we can't do that with `map`.

OK, here's our first reactive program that converts a signal of British
Columbia timestamps into a well-formatted triple of the current UTC time:

::: margin-warn
Here's a hazard of `Signal α` being a type alias rather than a genuine new
type: Lean can't distinguish a Signal from a function, since from the type
system's perspective they're genuinely interchangable. So, unfortunately, `map
clock (· / 3600)` and `map (· / 3600) clock` both typecheck, but the former
treats the signal as the function and vice versa.
:::
```lean4
-- Some signal combinators: these have type Signal Time -> Signal Time;
-- from a given timestamp, produce hours/mins/secs
def to_h := map (· / 3600)
def to_m := map (· / 60 % 60)
def to_s := map (· % 60)

-- OK, here's our reactive program: values flow from `clock` into `pst_secs`,
-- fork off into `to_h`/`to_m`/`to_s`, and ultimately rejoin in `hms`.
-- (exercise for you: implement map3!)

def pst_secs := clock
def utc_secs := delay utc_secs (7 * 3600)
def hms : Signal String := map3 (s!"{·}:{·}:{·}") 
                                (to_h utc_secs) (to_m utc_secs) (to_s utc_secs)

#eval hms 34234 -- "16:30:34"
```

## A more interesting signal

Here's a silly data definition for a traffic light type.  Let's write a signal
that defines how a value of this type could change over time, say, where the
colour changes once per time step:

```lean4
inductive Light where | Red | Yellow | Green
deriving Repr

def cycling : Signal Light := 
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
def cycling : Signal Light := 
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

Since a `Signal T` makes a value of type `T` _always_ available at all points
in time, this is our first Curry-Howard correspondence: The type of a `Signal
T` is `□ T`.  `□` means the same thing in both worlds.

::: margin-warn
In Lean, we have to be a bit careful: in a previous article we discussed that
`Prop`s and `Type`s differ: one lives in "the logical world" and the other "the
computational world".  The LTL-types-FRP paper is implemented in Agda, another
dependently-typed language but one that doesn't have this division.  

So, in Agda, we could simply define `□` once and use it in both contexts:
"write a well-typed FRP program" is _literally_ "prove an LTL property".  In
Lean, a `Signal α` is a function `Time → α` that produces a value at every time
step, and a proof of `□ p` is a function `Time → proof` that produces evidence
at every time step.  (This design choice buys some ergonomic simplicity in Lean
at the expense of expressiveness.)
:::
```lean4
namespace LTL
    ...
    prefix:max "□ " => always
end LTL
namespace FRP
    notation "□ " α => Signal α
end FRP
```

On its own, this isn't all that interesting, because so far the `α` parameters
we've seen for Signal (`Int`, `String`, `Light`) themselves aren't all that
interesting as logical propositions.  If you told a Java programmer
"`String.valueOf(i)` proves `String` given a proof of `Int`, isn't type theory
amazing??", they probably wouldn't be impressed; similarly, "A `Signal Int`
always makes an `Int` available" isn't super cool on its own either.  We need a
second fundamental primitive to add reactivity to FRP systems.

So, here're the new type signatures with their LTL-inspired typings:

```lean4
-- The current time is always available
def now : □ Time := fun t => t

-- If I always have an α, I can always transform it into a β.
def map (f: α → β) (s : □ α) : □ β := 
  fun t => f (s t)  

-- ...and if I always have both an α and a β, can do the same to get a γ
def map2 (f: α → β → γ) (s1 : □ α) (s2 : □ β) : □ γ := 
  fun t => f (s1 t) (s2 t)
```

## Proving a safety property about an FRP program

Recall from last time that `□`-statements form _safety properties_, of the
form "it's always the case that a bad state ie never reached."  A traffic
light might not have a bad state, per se, but _two_ traffic lights at a
road junction certainly do!

```lean4
def l1 : □ Light := cycling
def l2 : □ Light := FRP.delay cycling 1
def junction : □ (Light × Light) := FRP.map2 Prod.mk l1 l2

#eval junction 5 -- (Light.Green, Light.Red)
```

Let's ensure _mutual exclusion_ on the intersection: at no point can cars from
both streets enter the junction:

```lean4
def neverBothGreen : Prop :=
  LTL.always (LTL.not (LTL.atom (fun (l1, l2) => (l1 = .Green ∧ l2 = .Green)))) junction

example : neverBothGreen := by
  -- TODO

1 goal
⊢ neverBothGreen
```

Right now the goal is pretty opaque, so let's unfold the definitions of `neverBothGreen`
and `junction` so we actually have something to work with:

```lean4
example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2] -- NEW: unfold domain definitions

1 goal
⊢ □ (LTL.not (LTL.atom fun x => x.1 = Light.Green ∧ x.2 = Light.Green)) 
    (FRP.map2 Prod.mk cycling (FRP.delay cycling 1))
```

Next, let's unfold our relevant LTL primitives.  That gives us a quantified variable
for the value of time that we can also introduce into the context.

```lean4
example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2]
  simp [LTL.always, LTL.not, LTL.atom] -- NEW: unfold LTL operators
  intro t

1 goal
t : ℕ
⊢  (now (drop t (FRP.map2 Prod.mk cycling (FRP.delay cycling 1)))).1 = Light.Green →
  ¬(now (drop t (FRP.map2 Prod.mk cycling (FRP.delay cycling 1)))).2 = Light.Green
```

So far so good; that seems like a nice primitive.  Now let's do the same with our FRP
combinators.

::: margin-note
Don't forget that both `l1` and `l2` were defined in terms of `cycling`, hence we see
two occurrences of it in this simplified form.
:::
```lean4
example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2]
  simp [LTL.always, LTL.not, LTL.atom]
  intro t
  simp [now, drop, FRP.map2, FRP.delay] -- NEW: unfold FRP operators

1 goal
t : ℕ
⊢ cycling t = Light.Green → ¬cycling (t + 1) = Light.Green
```


After all that, we can finally unfold `cycling` and see some crunchy modular arithmetic.

::: margin-note
You might be tempted, since there's an implication here, to `intro` the antecedent as a
`h_green_now` theorem or something.  The problem with doing that is that we'll need to
evenutally case-split on `t % 3`.  You might find it amusing/annoying to try introing
it and seeing where you get stuck.
:::
```lean4
example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2]
  simp [LTL.always, LTL.not, LTL.atom]
  intro t
  simp [now, drop, FRP.map2, FRP.delay]
  simp [cycling]

1 goal
t : ℕ
⊢ (match t % 3, ⋯ with
    | 0, x => Light.Red
    | 1, x => Light.Yellow
    | 2, x => Light.Green) = Light.Green →
  ¬(match (t + 1) % 3, ⋯ with
      | 0, x => Light.Red
      | 1, x => Light.Yellow
      | 2, x => Light.Green) = Light.Green
```

So now let's `split` on the antecedent `match`, leaving us with three
cases depending on the value of `t % 3`, noting that `h_1` and `h_2`
could immediately be discharged away:

```lean4
example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2]
  simp [LTL.always, LTL.not, LTL.atom]
  intro t
  simp [now, drop, FRP.map2, FRP.delay]
  simp [cycling]
  split -- NEW

3 goals
case h_1
...
heq✝¹ : t % 3 = 0
⊢ Light.Red = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
case h_2
...
heq✝¹ : t % 3 = 1
⊢ Light.Yellow = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
case h_3
...
heq✝¹ : t % 3 = 2
⊢ Light.Green = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
```

For each of these three cases, we have three more possibilities, so let's
`split` on _those_, too:

```lean4
example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2]
  simp [LTL.always, LTL.not, LTL.atom]
  intro t
  simp [now, drop, FRP.map2, FRP.delay]
  simp [cycling]
  split <;> split

9 goals
case h_1
...
heq✝³ : t % 3 = 0
heq✝¹ : (t + 1) % 3 = 0
⊢ Light.Red = Light.Green → ¬Light.Red = Light.Green
case h_2
...
heq✝³ : t % 3 = 0
heq✝¹ : (t + 1) % 3 = 1
⊢ Light.Red = Light.Green → ¬Light.Yellow = Light.Green
case h_3
...
heq✝³ : t % 3 = 0
heq✝¹ : (t + 1) % 3 = 2
⊢ Light.Red = Light.Green → ¬Light.Green = Light.Green
case h_4
...
heq✝³ : t % 3 = 1
heq✝¹ : (t + 1) % 3 = 0
⊢ Light.Yellow = Light.Green → ¬Light.Red = Light.Green
... and so on until ...
case h_9
heq✝³ : t % 3 = 2
heq✝¹ : (t + 1) % 3 = 2
⊢ Light.Green = Light.Green → ¬Light.Green = Light.Green
```

`simp` will discharge away all the contradictory cases (where the antecedent is
`False`) or trivial cases (where the implication is `True -> True`), leaving
just one:

```lean4
example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2]
  simp [LTL.always, LTL.not, LTL.atom]
  intro t
  simp [now, drop, FRP.map2, FRP.delay]
  simp [cycling]
  split <;> split <;> simp

1 goal
case h_9
...
heq✝³ : t % 3 = 2
heq✝¹ : (t + 1) % 3 = 2
⊢ False
```

From the values in our context, we can see that the one case that `simp`
could not discharge was when both lights are green.  This is the only case
that matters because it's what our safety property is actually _about_:
every other case is vacuously true because at least one light isn't green.
This is actually kind of nice - the proof naturally focuses our efforts on
exactly the scenario we are trying to guard against.

Since the lynchpin of the proof here involves a contradiction in our context:
`t % 3 = 2` and `(t + 1) % 3 = 2` are impossible, and `lia` can find it.
That closes the final goal and proves safety of our first functional reactive
program!

```lean4
def l1 : □ Light := cycling
def l2 : □ Light := FRP.delay cycling 1
def junction : □ (Light × Light) := FRP.map2 Prod.mk l1 l2

#eval junction 5

def neverBothGreen : Prop :=
  LTL.always (LTL.not (LTL.atom (fun (l1, l2) => (l1 = .Green ∧ l2 = .Green)))) junction

example : neverBothGreen := by
  simp [neverBothGreen, junction, l1, l2]
  simp [LTL.always, LTL.not, LTL.atom]
  intro t
  simp [now, drop, FRP.map2, FRP.delay]
  simp [cycling]
  split <;> split <;> simp
  lia
```

# An `Event` occurs at some point in time

::: margin-note
Might be worth trying to guess if there's an LTL proposition that might be a
good type for `Event`s!
:::
The dual of a `Signal` is an `Event`, which you can think of a stream of values
to be consumed by the system at particular moments in time.  For an interactive
webapp, you might, "right at this moment", send a "click" `Event` to a form
button, which perhaps triggers other events to fire.  Or, maybe, you enqueue an
event to fire some point in the future, like registering a timeout on a network
call or something.  (If you come from an OO background, an `Event` is very much
like an [Observable](https://reactivex.io/documentation/observable.html).)

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

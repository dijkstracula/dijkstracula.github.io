---
layout: post.njk
title: "FRP in Lean: Stateful combinators, safety, and liveness"
date: 2026-05-03
tags: [post, lean, reactive-programming, ltl, frp]
series: lean-ltl
series_title: "FRP: stateful combinators and safety"
inlineCodeLang: lean4
---

<script src="/js/frp/runtime.js"></script>

# Non-pointwise combinators have knowledge of previous timesteps

Up to now, every Signal we've seen has been stateless.  `FRP.map` and
`FRP.map2` from last time apply pure functions to the value at each timestep,
with no memory of what came before.  Real reactive systems have evolving state:
the value at time `t+1` depends on the value at time `t`. 

In this post, we'll build up to `FRP.accumulate`, which is a general-purpose
non-pointwise FRP combinator.  We'll see that the point of these combinators is
to combine a sequence of discrete `Events` at various points in time to
maintain a running Signal that captures those events changing the Signal
value.

## A warmup exercise: a quick equivalence lemma

Last time, we saw how FRP primitives interact with temporal logic types.  In case
it's been awhile since you've read the previous piece, let's warm up with a little
lemma that will fault in a bunch of the material from before, and that'll become
useful shortly.

Suppose I have some `Signal β` - that is, a time-varying value of type `β`.
And, suppose I have some statement `inv` about `β` values, such that at every
time step in the signal, `inv` holds.  Then, `inv` is an _invariant_ over that
Signal.  A bit more formally:

::: margin-note
Quick reminder from previous posts: `StateProp β` is a `β -> Prop`; in other
words, given a value of some type, produce a propositiona about that value. We
used this back in the [intro to LTL](/posts/lean-ltl-3) - it's the type that
an `LTL.atom` consumes.
:::
```lean4
theorem some_lemma {inv : StateProp β} (sig :  □ β) (h : ∀ t, inv (sig t))
    : /- TODO: what can we show? -/ := by /- TODO: how do we show it? -/
```

Can we say anything in temporal logic about how the invariant and the signal
interact?  Hopefully you might say something informal like "it will always be
the case that `inv` holds for `sig`".  Less formally, we'd say `(□ (LTL.atom
inv)) sig`.  Let's prove it!

```lean4
theorem always_atom {inv : StateProp β} (sig :  □ β) : 
  (∀ t, inv (sig t)) → (□ (LTL.atom inv)) sig := by
  intro h t ; -- TODO

β : Sort u_1
inv : StateProp β
sig : □ β
h : ∀ (t : Time), inv (sig t)
t : Nat
⊢ LTL.atom inv (drop t sig)
```

This lets us say, starting from the goal and looking backwards to the
hypotheses, "I want to show that `□ (atom p)` holds; I'll prove `∀ t, p (trace
t)` instead, which is equivalent", or, starting from a hypothesis and looking
ahead to the goal, "I have `∀ t, p (trace t)`; I'll repackage it as `□ (atom
p)` to use other LTL operators."

This isn't too hard to prove, because `□` is just defined under the hood just
like `h`.  With some unfolding of LTL definitions, we end up precisely with
the hypothesis `h`.

::: margin-note
Technically, for this to be an equivalence, you need to show implication in
both directions.  Give that a try and prove the stronger statement
`always_atom_iff`, which we'll make use of in the next post.  To write it,
you'll change `→` to `↔` and use the `constructor` tactic to split the goal
into the two implications.
:::
```lean4
theorem always_atom {inv : StateProp β} (sig :  □ β) : 
  (∀ t, inv (sig t)) → (□ (LTL.atom inv)) sig := by
  intro h t ; simp [LTL.atom, drop, now] ; exact h t

Goals accomplished!
```

this theorem is nice because it collates an infinite number of non-temporal
`inv (sig t)` proofs into a single temporal proof. If we can build Signals
whose values satisfy an invariant at every timestep, then we can use
`always_atom` to automatically lift that invariant into a _safety property_.
We'll get the temporal logic guarantee without explicitly needing to do any
temporal reasoning.  

To build signals that maintain invariants through time, we need a different
kind of combinator. And to derive it from first principles, we'll take a short
detour through a small piece of category-theoretic vocabulary: catamorphisms.

## Catamorphisms and recursors

You already know how to fold over a plain old List in a plain old functional
programming language:
[List.foldr](https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Basic.html#List.foldr)
takes an initial value `β` and a "merge" function `a -> β -> β`, and collapses
the list down into a single result.  For a long time, I thought folds were
somehow intrinsic to `List`s because I'd never seen folds in any other context,
but you can write a fold-like operation over any algebraic datatype.

That operation is called a
[catamorphism](https://ncatlab.org/nlab/show/catamorphism), and relates to
_recursors_ in type theory (which we'll see an example of in a moment).  A
catamorphism for some type replaces each constructor with a corresponding
computation (an “algebra component”) that produces the result type `β`. 

That function consumes:
- the constructor’s **non-recursive** arguments, and
- the constructor’s **recursive** arguments *after they’ve already been folded*.

Let's invent the catamorphism for `List`s from first principles.  Why does
`List.foldr` have the arguments it does?  It stems from the datatype's
constructors. There are two ways to construct a List, as we all know: `Nil :
List a` produces the empty list, and `Cons : a -> List a -> List a` prepends an
element onto a list.  This means that which replaces `Nil : List a` will
be typed `β`, and that which replaces `Cons : a -> List a -> List a` will be
typed `a -> β -> β`.

In other words, `List.foldr` is the catamorphic operation for `List`!  It shows
us how to collapse one constructor layer into a `β`.

### Recursors generalise catamorphisms

If we want more generality than just "given the recursive results of the
subdata in each constructor, produce a value", we'll need a different kind of
algebraic transformation on our datatype.  For example, it isn't clear how we
could write a `Nat.predecessor` or `List.drop_last` function with
catamorphisms. We'd need to choose a richer datatype to fold over, like a
(prev, curr) pair that "remembers" the previous value. A generalisation that
_does_ let us do this without changing the type we're folding over is a
_recursor_.

We could also write a catamorphism for `Nat`s: `Nat` has two constructors,
`Zero : Nat` and `Succ : Nat -> Nat`.  Because the `Zero` constructor takes no
arguments, we provide a constant `β` value for that case, and for `Succ`, a `β
-> β`.

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
def Nat.rec (onZero : β) (onSucc : Nat → β → β) : Nat → β
  | .zero => onZero
  | .succ n => onSucc n (Nat.rec onZero onSucc n)
```

This isn't the catamorphism for `Nat`s: `succ` also consumes the predecessor
argument (that is, the _recursive argument before being folded_).  This is more
general than a catamorphism; it's called a
[paramorphism](https://blog.sumtypeofway.com/posts/recursion-schemes-part-3.html),
and it's built up from a different kind of algebraic structure than
catamorphisms.

(Before continuing, pause and ponder: suppose `Nat.rec` also consumed some
invariant `β -> Prop`.  How might we apply such a function inside the
recursor?)

## Our first non-pointwise combinator: Signaling on the catamorphism for Time

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
Evaluating `scan step init` at time `n` recomputes from init every time, `O(n)`
per evaluation, and so `O(n²)` to evaluate the whole signal. This isn't
dissimilar from the problem we had last time with `Event.latch`, and the
solution's the same: A real FRP runtime would do something smarter like mutate
a value over time to cache previous state(s).
:::
```lean4
def screaming : Signal String := scan (· ++ "a") ""
#eval (List.range 5).map screaming -- ["", "a", "aa", "aaa", "aaaa"]
```

:::tip
<div id="frp-scan"></div>
:::

<script>
(() => {
  const g = FRP.graph();
  g.scan('screaming', s => s + 'a', '');
  FRP.renderTiming(document.getElementById('frp-scan'), g, { ticks: 8 });
})();
</script>

Something interesting to note is that this is our first Signal that isn't
ultimately driven by the tick of the `clock`: we never actually do any
computation based on the internal value of `t` like we did with the UTC
time conversion example.

This should also feel a lot like what we did with stepping state machines back
in the first post!  The difference, of course, is that `vmStep` needed an
action at each step (and a proof it was valid, of course).  `scan` Signals
don't, by contrast; it's an autonomous state machine that just evolves on its
own.  We'll need a richer combinator to start folding in Events into the
mix.

::: tip
Pause and ponder: a generalisation of `scan` could let the step function vary
as a function of time: this means it'd consume a `Signal (β -> β)` instead of
just a `β -> β`.  If you're feeling ambitious: implement this primitive, and
then write `scan` in terms of it.  (Hint: you'll need `FRP.const`.)
:::

## Traffic lights, revisited

Here's where we left off the traffic light example: this retains our original
unfortunate property that the walk signal is on only when the button is pressed.
Not only does this violate liveness (someone can tape the button down and impede
traffic forever), it's also slightly unrealistic in that pedestrians need time
to also cross the crosswalk.

```lean4
inductive WalkSign where 
 | Walk 
 | DontWalk
deriving Repr, DecidableEq

def walkSignal (button : ◇ Unit) : □ WalkSign :=
  fun t => match button t with
    | some () => .Walk
    | none    => .DontWalk

def carLight (button : ◇ Unit) : □ Light :=
  fun t => match button t with
    | some () => .Red
    | none    => cycling t

def pedCrossing (button : ◇ Unit) : □ (Light × WalkSign) :=
  FRP.map2 Prod.mk (carLight button) (walkSignal button)
```

Our goal is now to introduce a stateful value that can encode how many ticks
are left on the crosswalk or how many ticks are left until the button can be
pressed once again.  And, of course, as an inductive type, we can write a
catamorphism for it:

::: margin-note
`CrossingState` isn't a recursive datatype like `Nat` or `List` so maybe it's a
bit strange to write a "fold", since no actual folding happens.  A common
naming convention for this is `elim`, for type _eliminator_.
:::
```lean4
namespace CrossingState
  inductive CrossingState where
    | Idle                             -- Traffic light runs as usual
    | Countdown : Nat → CrossingState  -- N more walk ticks after this one
    | Cooldown  : Nat → CrossingState  -- N more cooldown ticks after this one
  deriving Repr

  def fold (idle : β) (countdown : Nat → β) (cooldown : Nat → β)
      : CrossingState → β
    | .Idle        => idle
    | .Countdown n => countdown n
    | .Cooldown n  => cooldown n
end CrossingState
```

Using our `scan` combinator, we can write a `Signal CrossingState` that steps
itself through time according to a `tick` function: when a `Countdown` reaches
zero, we transition to a `Cooldown`, and when `Cooldown` reaches zero, we
transition to `Idle`.

```lean4
def CrossingState.tick : CrossingState → CrossingState :=
  fold
    (idle := CrossingState.Idle)
    (countdown := fun
      | 0   => CrossingState.Cooldown 3
      | n+1 => CrossingState.Countdown n)
    (cooldown := fun
      | 0   => .Idle
      | n+1 => CrossingState.Cooldown n)

#eval List.range 8 |>.map (FRP.scan CrossingState.tick (.Cooldown 3))
-- output:
[Cooldown 3,
 Cooldown 2,
 Cooldown 1,
 Cooldown 0,
 Idle,
 Idle,
 Idle,
 Idle]
```

This is great!  We can step through our light example through time.  Of course,
what's missing is a way for an Event to inject a change into the fold.
That's what `accumulate` will get us.

## `accumulate` turnsa temporal fold over an Event

The idea of `accumulate` is this: we're going to start with an Event of some
type and produce a Signal of some type.  Since we said that `accumulate`
generalises `scan`, makes sense that we should at least consume an `init`
state - this at least nails down the type of the returned Signal.

::: margin-note
Something interesting is that `accumulate` lets us convert an Event into a
Signal - that's a modality-converting operation!  Down the road we'll see what
it means to convert a Signal into an Event, but you might enjoy spending a
moment or two imagining what such a function might look like.
:::
```lean4
def accumulate /- TODO: what else? -/ (init: β) (ev: ◇ a) : Signal β := 
  sorry -- TODO: what to do?
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

One thing to notice is that so long as the given Event isn't triggering (that
is, when `ev t = none`, this is doing exactly the same thing as our `scan`
combinator.  So, `scan`'s `step` might as well be called `onNone`, since that's
how to just produce a new `β` given the previous one.

```diff-lean4
-def accumulate /- TODO: what else? -/ (init: β) (ev: ◇ a) : Signal β := 
+def accumulate /- TODO: what else? -/ (onNone: β → β) (init : β) (ev: ◇ a) : Signal β := 
   sorry -- TODO
```

Notice that this `onNone` is _not_ the same as the `β` we guessed a moment ago.
The reason is that we're not producing `β`s from scratch, but rather one that
involves the previous `β` state.  So, that value has to be threaded through that
function.  Generally, we say we've _lifted_ `β` into the pure catamorphism.

### ...and when it _is_ firing

This also means we want a `onSome` function, of some `β`-producing type!

```diff-lean4
-def accumulate /- TODO: what else? -/ (onNone: β → β) (init : β) (ev: ◇ a) : Signal β := 
+def accumulate (onSome: ? -> β) (onNone: β → β) (init : β) (ev: ◇ a) : Signal β := 
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

```diff-lean4
-def accumulate (onSome: ? -> β) (onNone: β → β) (init : β) (ev: ◇ a) : Signal β := 
+def accumulate (onSome: a → β → β) (onNone: β → β) (init : β) (ev: ◇ a) : Signal β := 
   sorry -- TODO
```

Before proceeding, you should spend a moment convincing yourself that the wrong
thing to do here would have been to have `accumulate` consume an input,
"background" Signal for when the event's not firing, instead of the `init`
and `onNone` values.  Had we done that, we'd be back to the piecewise
combinator where consequences of the Event firing can't ripple through
subsequent timesteps.

### Implementing `accumulate` with the recursor for Time

OK, how do we actually write this thing?  Since we said earlier that
`accumulate` generalises `scan`, using the recursor for `Nat` seems
like a good idea.  Here's the overall shape we'll be working with:

```diff-lean4
 def accumulate (onSome: a → β → β) (onNone: β → β) (init : β) (ev: ◇ a) : Signal β := 
-  sorry -- TODO
+  fun n => Nat.rec 
+    sorry            -- TODO: what to do at t=0?
+    (fun s => sorry) -- TODO: what to do at t=(n+1)?
+    n
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

When `n=0`, we'll return `init` directly.  `init` is the value at time 0, so
there's no event value to consult yet.  For the `n=(n'+1)` case, we'll pass in
the next time value, and the previous state, which the recursor will
automatically supply for us.

So in conclusion, our final `accumulate` is:

::: margin-note
Notice that our use of `Nat.rec` looks a lot like the body of `scan`.
:::
```diff-lean4
 def accumulate (onSome: a → β → β) (onNone: β → β) (init : β) (ev: ◇ a) : Signal β :=
+  let switch (t: Time) : β → β := match ev t with
+  | none => onNone
+  | some a => onSome a
+
   fun n => Nat.rec 
-    sorry            -- TODO: what to do at t=0?
-    (fun s => sorry) -- TODO: what to do at t=(n+1)?
+    init                          -- n=0
+    (fun n' s => switch (n'+1) s) -- n=(n'+1)
     n
```

Notice that, because we actually _do_ use `n'` in the recursor, in contrast to
`scan`, `accumulate` is genuinely paramorphic!

::: tip
Pause and ponder: If you wrote the time-varying generalization of `scan` in the
previous section, and are _still_ feeling ambitious, implement `accumulate` in
terms of that general combinator, `FRP.map`, and `switch`.  Similarly, can you
write `Event.latch` in terms of `accumulate`?
:::

## Weaving in button presses

At last, we have enough mechanism to actually fold over both ordinary
transitions and inject events into the Signal stream:  Let's define a
button press Event that fires at `t=2` and `t=5`:

::: margin-note
Remember that to make an event truly an "eventually" we need to also supply a
witness that it fires at least once.  `by exists 5` would have been sufficient
as well.
:::
```lean4
def presses : ◇ Unit :=
  let f := fun 
    | 2 | 5 => some () 
    | _ => none
  ⟨ f, by exists 2 ⟩
```

Next, we need to define our `onNone` and `onSome` behaviour.  When the button's
not being pressed, the behaviour is just our usual `tick`.  When it _is_ pressed,
we'll ignore the event unless we're in the `Idle` state:

```lean4
def onNone := tick

def onSome (_ev : Unit)
  | .Idle => .Countdown 3
  | s => tick s
```

Now we can wire all these up!  We'll use `presses` alongside `onNone` and `onSome`,
and some starting state:

```lean4
def crosswalk ev := FRP.accumulate
  (.Cooldown 2) -- init
  CrossingState.onNone
  CrossingState.onSome
  ev

#eval List.range 10 |>.map (fun n => (n, (crosswalk presses) n))

[(0, CrossingState.Cooldown 2),
 (1, CrossingState.Cooldown 1),
 (2, CrossingState.Cooldown 0),  -- t=2: Button press (ignored)
 (3, CrossingState.Idle),
 (4, CrossingState.Idle),
 (5, CrossingState.Countdown 3), -- t=5: Button press (accepted)
 (6, CrossingState.Countdown 2),
 (7, CrossingState.Countdown 1),
 (8, CrossingState.Countdown 0),
 (9, CrossingState.Cooldown 3)]
```

::: tip
<div id="frp-crosswalk"></div>
:::
<script>
(() => {
  function tick(s) {
    if (s.kind === 'Cooldown') {
      return s.n === 0 ? { kind: 'Idle' } : { kind: 'Cooldown', n: s.n - 1 };
    }
    if (s.kind === 'Idle') return { kind: 'Idle' };
    if (s.kind === 'Countdown') {
      return s.n === 0 ? { kind: 'Cooldown', n: 3 } : { kind: 'Countdown', n: s.n - 1 };
    }
    return s;
  }
  function onSome(_ev, s) {
    if (s.kind === 'Idle') return { kind: 'Countdown', n: 3 };
    return tick(s);
  }
  function fmt(s) {
    return s.kind === 'Idle' ? 'Idle' : s.kind + ' ' + s.n;
  }
  const g = FRP.graph();
  const presses = g.eventAt('presses', [2, 5], undefined, { noT0Click: true });
  g.accumulate('crosswalk',
               { kind: 'Cooldown', n: 2 },
               tick, onSome, presses);
  FRP.renderTiming(document.getElementById('frp-crosswalk'), g, {
    ticks: 10,
    format: (v, name, t, node) => {
      if (name === 'crosswalk') return fmt(v);
      return FRP.defaultFormat(v, name, t, node);
    }
  });
})();
</script>

We see precisely what we wanted to: at `t=2`, we're still in the midst of a
cooldown, so that button press is ignored.  However, by the time we reach
`t=5`, we're in the `Idle` state, so the press _is_ accepted.

## An inductive invariant-aware `accumulate`

Way back in [the first post](/posts/lean-ltl) in this series, we created the
dependent type `validStep s a` to ensure that a transition (in a pop machine,
or any other transition system) is valid.  Since `accumulate` feels so much
like driving a state machine, we should come up with a similar mechanism for
"safe accumulation".

With raw dependent types, a `validStep` needed to be proved at every step at
every trace (even if leaning on decidable decision procedures meant that that
proof could be, in practice, `by decide`).  We got a great guarantee from this:
if a precondition wouldn't hold, the whole trace would fail to typecheck, but
total static safety came with a heavy price in terms of ergonomics.  And,
what's more, the proofs we could write about a particular trace could be really
precise: 'on the trace `pay, pay, choose, take, pay`, "you had dropped three
coins in total, terminating in a specific final state"' could be something we
could express easily.

We [then](posts/lean-ltl-2) moved to a monadic API, which had no proof
obligations on the user whatsoever.  The ergonomics of that API were pretty
ideal in that you could just sequence arbitrary steps, but we lost static
guarantees and had to fall back to runtime failures when hitting an invalid
step.

There's a third point in the solution space that we can play with.  Back in
[yet another](posts/lean-ltl-3) post, we introduced _inductive invariants_,
which are predicates that hold at `init` and are preserved on every step.

Rather than validity proofs operating on a _step-by-step_ basis, necessitating
every trace having their own sequence of proofs applied, we can write proofs at
the granularity of the _initial state_ and the _step function itself_.  These
are exactly what we get from an _inductive invariant_: proofs of initiation and
concecution.

### Assume-guarantee reasoning with refinement types

Let's start writing this invariant-aware `accumulate`.  It'll begin with
consuming one additional implicit argument, the invariant itself.  (Making the
argument implicit means the typechecker just infers it from the other
arguments.)

```lean4
def accumulate
  {inv : StateProp β} -- NEW: our inductive invariant, an implicit argument.
  (init : ...)
  (onNone : ...)
  (onSome : ...)
  (ev : ...)
  : ... := -- TODO
```

For `inv` to be an inductive invariant, it has to hold for the `β` `init`
(that's the _initiation_ requirement).  As the caller who supplies `init`,
it'll be our job to provide a proof of this, so the internals of `accumulate`
can assume that it's true.  (Remember, this is an assumption in the formal
logic sense, not in the make-an-ass-out-of-you-and-me sense.)

Up to this point we probably would have passed in an additional `h_init`
argument of type `inv init`.  That'd work!  But, I'm going to do it in a
different way, using a particular kind of dependent type called a _refinement
type_.

::: margin-note
If you're interested in learning more about refinement types, might I be so
bold as to suggest my [Papers We
Love](https://www.youtube.com/watch?v=C5PuBeiWaSA) talk about it?
:::
A refinement type bundles up a plain old type with a proposition that must
always hold for that type to be well-defined.  I love refinement type systems
because they're in practice more restrictive than the full-blown dependent
types that we've been using in Lean, and so, if you design your type system
well, you can have something that feels like dependent types but with type
inference!

::: margin-note
You should pause and ponder about the connections between refinement types and
subtypes.
:::
Our refinement type for `init`, instead of just being a plain old `β`, will now
be a `{ s : β // inv s }`.  You can read this aloud as "a `β` such that `inv
v`".  (Notice that we gave the particular `β` a name, so we could refer to it
in the "such that" qualifier.)  When we want to operate on a value whose type
is a refinement type, just like with dependent pairs, we'll destruct it into a
[record with two
fields](https://lean-lang.org/doc/reference/latest/Basic-Types/Subtypes/#Subtype___mk)
`⟨val, property⟩`.

So that's Initiation.  The other requirement for inductive invariants is
_consecution_, namely, "under the assumption that we're in a valid state,
stepping leaves us in a valid state".  Under our catamorphism we have two ways
to step (either when an event fires, `onSome`, or when it does not, `onNone`),
so we'll have to refine those type arguments, too.

That leaves us with all our arguments to `accumulate` looking like this:

::: margin-note
The standard convention is to name the before state `s` and the after state
`s'`.
:::
```diff-lean4
 def accumulate
   {inv: StateProp β}
-  (init : ...)
-  (onNone : ...)
-  (onSome : ...)
-  (ev : ...)
-  : ... := -- TODO
+  (init : { s: β // inv s})
+  (onNone: { s: β // inv s } → { s': β // inv s' })
+  (onSome: α → { s: β // inv s} → {s': β // inv s'})
+  (ev: ◇ α)
+  : /- TODO: return type? -/ := ... -- TODO: implementation?
```

Previously, `accumulate` returned a `Signal β`.  Stands to reason that it's now
going to be a refinement type `{ sig: (Signal β) // ... }`.  But what's the
proposition that should be true on the return type?

Remember that inductive invariants encode safety properties.  So, whatever that
property is, it better hold for every time step in the returned signal.  That's
an proposition in LTL!  In particular, `(□ (LTL.atom inv))` applied to the
Signal.

So, our final function signature for `accumulate` is:

```diff-lean4
 def accumulate
   {inv: StateProp β}
   (init : { s: β // inv s})
   (onNone: { s: β // inv s } → { s': β // inv s' })
   (onSome: α → { s: β // inv s} → {s': β // inv s'})
   (ev: ◇ α)
-  : /- TODO: return type? -/ := ... -- TODO: implementation?
+  : { sig : (Signal β) // (□ (LTL.atom inv)) sig }  := ... -- TODO: implementation?
```

Notice that this refines the entire Signal, not the `β` inside the signal.
"`(Signal β) // ...`" is saying "here's a Signal and a proof of its safety
property", whereas, if we'd parenthesized it differently, `Signal (β // ...)`
would make a pointwise claim about the `β` available at every timestep.  

::: margin-note
If you're one to push symbols around and see what shakes out, you might wonder,
"what would it mean if we changed the `□` in the return type to `◇`, so it
reads `Signal β // (◇ (LTL.atom inv)) sig`? This would produce, instead of a
safety property, a _liveness property_, proving "eventually, but not now, `inv`
holds".  We're not quite ready to do so yet, but maybe we'll write a combinator
to produce such a Signal down the road.
:::
`sig : (Signal β) // (□ (LTL.atom inv)) sig` is what we get for proving
initiation and consecution: under the assumption that `inv` holds initially,
and its preserved whether or not the Event fires, we'll guarantee that `inv`
holds at all time steps and therefore will guarantee our safety property.

Such "assume-guarantee" reasoning is critical for composing verified code
together: the guarantee out of one function can become an assumption into the
next.  (In the next post, we'll see how assume-guarantee reasoning composes.)

### Coercing a subtype back into a Signal

OK, `accumulate` returns a refinement type-pair of a Signal plus the safety
witness, but in actual uses of `accumulate` we only want the Signal itself.
Let's add a quick coercion, just like we did for Events last time, to treat
the refinement type as callable, itself:

```lean4
instance {P : Signal StateProp β} :
    CoeFun { sig : (Signal β) // P sig } (fun _ => Signal β) where
  coe s := s.val
```

In general, when you have a function bundled with a proof obligation, `CoeFun`
lets the function be used without manual unwrapping.  The safety theorem is
still tagging along, but not in the way when we just want the function.

## Implementing the dependent `accumulate`

OK, let's fix our `accumulate` implementation.  Our goal is first to fix the
type errors that we've introduced by changing the function signatures, and then
decide the shape of the final value that gets produced.

### Fixing `switch` and our recursor

Our `switch` helper is currently operating on raw `β`s and so doesn't typecheck
anymore:

::: warning
```lean4
...
  let switch (t: Time) : β → β := match ev t with
  | none => onNone
  | some a => onSome a
```
```lean4
Type mismatch
  onNone
has type
  { s // inv s } → { s' // inv s' }
but is expected to have type
  β → β
```
:::

Luckily, the hard part is going to be writing `onNone` and `onSome`, not
calling them.  So, it's enough to just change the type signature to ensure
applying those functions is consistent with their types:

::: tip
```diff-lean4
 ...
-  let switch (t: Time) : β → β := match ev t with
-  | none => onNone
-  | some a => onSome a
+   init
    (fun n s => switch (n + 1) s) n
```
```lean4
failed to elaborate eliminator, expected type is not available
```
:::

A slightly more alarming error, that, unlike the previous one, doesn't give us
much to go on.  In essence, `Nat.rec` relies on a type annotation that we've
lost in the refactoring; factoring out `let`-bindings can sometimes require
adding some annotations, especially if the right-hand side of the binding has
weird dependent types like motive types.  Luckily, writing down our intent here
is also simple change - just gotta follow the types:

::: tip
```diff-lean4
-  let step_at := fun n => Nat.rec
+  let step_at : Signal {s: β // inv s} := fun n => Nat.rec
     init 
     (fun n s => switch (n + 1) s) n
```
:::

## Lifting `step_at`'s proofs into a safety property

Notice that `step_at` now returns a _pointwise_ proof: we get back a record `<
val := value_at_i, property := validity_at_i>`: the value after time step `i`,
and a proof that whatever that value is, it satisfies `inv` at time step `i`. 

This is our `Signal (β // ...)` example from before, but we need it to look
like `(Signal β) // ...`" instead.  We'll do this with the theorem we wrote
at the top of this post!  We'll take the infinitely-many pointwise invariant
presevation proofs and collate them into an LTL proposition.  This'll complete
the implementation.

```lean4
theorem always_atom {inv : StateProp β} (sig : Signal β) (h : ∀ t, inv (sig t))
    : (□ (LTL.atom inv)) sig := by
  intro t ; simp [LTL.atom, drop, now] ; exact h t

def accumulate
  -- Given a property over some state ...
  {inv: StateProp β}
  -- an initial state,
  (init : { s: β // inv s})
  -- a transition function when no event fires...
  (onNone: { s: β // inv s } → { s': β // inv s' })
  -- a transition function when an event _does_ fire...
  (onSome: α → { s: β // inv s} → {s': β // inv s'})
  -- and an event...
  (ev: Event α)
  -- ...produce a single refined value, made up of a `Signal β`, and
  -- a safety proof over all time steps.
  : { sig : Signal β // (□ (LTL.atom inv)) sig } :=

  -- `switch` produces the next state, depending on whether the event
  -- fired at the given timestep
  let switch (t: Time) : {s: β // inv s} → {s': β // inv s'} :=
    match ev t with
    | none => onNone
    | some a => onSome a

  -- `step_at` takes `t` steps through `switch`; at each time step, it
  -- produces a β alongside its proof of .preserving `inv`
  let step_at : □ {s: β // inv s} := 
    fun t => Nat.rec 
      init 
      (fun n s => switch (t + 1) s) 
      t
 
  -- Reorganize the signal of refined values into a refined signal.
  let vals : □ β := fun t => (step_at t).vals
  let safety : ∀ t, inv (vals t) := fun t => (step_at t).property
  ⟨ vals, always_atom vals safety ⟩
```

## A safe intersection

OK, let's tie this post off by showing how to prove a traffic light safety
property with `accumulate`.  

::: margin-note
This might sound trivial but an integer overflow was why the Ariane 5 blew
up shortly after launch.
:::
Suppose that the microcontroller inside the traffic light uses a three-bit
counter.  For safety-certified hardware, each gate is audited, and city council
won't pay for re-certifying a wider register. So, a safety property that
prevents ever overflowing our counter registers would be:

::: margin-note
We've seen before that `abbrev`s are "transparent" to the typechecker;
this'll make writing proofs about `bounded` a bit easier.
:::
```lean4
abbrev bounded : CrossingState → Prop
  | .Idle        => True
  | .Countdown n => 0 <= n ∧ n < 8
  | .Cooldown n  => 0 <= n ∧ n < 8
```

(Technically, Lean's `Nat` datatype prevents us underflowing here, but I'll
state the lower bound in the safety property, anyway.)

The design constraints for this particular intersection are well within this
bound, but perhaps, say, for crossing a wider road with more car traffic, city
planners would want both a larger countdown and cooldown value.  Or, perhaps,
those values could be dynamically-scaled up depending on live traffic data that
doesn't know anything about the underlying hardware.  Our goal is to statically
prevent anyone from, in the future, trying to set a value that would overflow
that register.

OK, let's lift our `tick` function into its refinement type version.  Once we
replace all the `sorry`s with a valid proof of `bounded`, we'll be able to wire
it all up to an `accumulate` call and produce a verified FRP program.

Here's the skeleton with our modified `tick` function: since we now consume and
produce the refinement type value, we consume and produce tuples of the
`CrossingState` and proof of `bounded s`.

```lean4
def tick : { s: CrossingState // bounded s } → { s': CrossingState // bounded s' }
  | ⟨.Idle, _ ⟩        => ⟨ .Idle, by sorry ⟩
  | ⟨.Cooldown 0, _ ⟩  => ⟨ .Idle, by sorry ⟩
  | ⟨.Cooldown (n+1), _ ⟩  => ⟨ .Cooldown n, by sorry ⟩
  | ⟨.Countdown 0, _ ⟩     => ⟨ .Cooldown 3, by sorry ⟩
  | ⟨.Countdown (n+1), _ ⟩ => ⟨ .Countdown n, by sorry ⟩
```

### Proving validity of `tick`'s possible arguments

All transitions to `.Idle` are trivial to prove, literally, since `bounded
.Idle = True`.  First two cases sorted without any difficulty.

```lean4
 ...
  | ⟨.Idle, _ ⟩        => ⟨ .Idle, by trivial ⟩  -- NEW
  | ⟨.Cooldown 0, _ ⟩ => ⟨ .Idle, by trivial ⟩  -- NEW
 ...
```

The nonzero `Countdown` and `Cooldown` steps are pretty easy, too. unfolding
the definition of `bounded` means our goal is to prove `0 <= n` and `n < 8`,
given a hypothesis `h` stating the same about `n+1`.  As expected, `lia` will deal with
that inequality without any difficulties.

::: margin-note
If we'd used `def` rather than `abbrev` when defining `bounded`, we would have
needed to first show that our goal was to prove `0 <= n ∧ n < 8`, and then
discharge it with `lia`; as it stands now the tactic can see through the
`abbrev` to its definition`.
:::
```lean4
  ...
  | ⟨.Cooldown (n+1), _   ⟩ => ⟨ .Cooldown n, by lia ⟩
  | ⟨.Countdown 0, _ ⟩      => ⟨ .Cooldown 3, by lia ⟩
  | ⟨.Countdown (n+1), _ ⟩  => ⟨ .Cooldown n, by lia ⟩
  ...
```

::: tip
```diff-lean4
 def tick : { s: CrossingState // bounded s } → { s': CrossingState // bounded s' }
-  | ⟨.Idle, _ ⟩        => ⟨ .Idle, by sorry ⟩
+  | ⟨.Idle, _ ⟩        => ⟨ .Idle, by trivial ⟩
-  | ⟨.Cooldown 0, _ ⟩  => ⟨ .Idle, by sorry ⟩
+  | ⟨.Cooldown 0, _ ⟩  => ⟨ .Idle, by trivial ⟩
-  | ⟨.Cooldown (n+1), _ ⟩  => ⟨ .Cooldown n, by sorry ⟩
+  | ⟨.Cooldown (n+1), _ ⟩  => ⟨ .Cooldown n, by lia⟩
-  | ⟨.Countdown 0, _ ⟩     => ⟨ .Cooldown 3, by sorry ⟩
+  | ⟨.Countdown 0, _ ⟩     => ⟨ .Cooldown 3, by lia ⟩
-  | ⟨.Countdown (n+1), _ ⟩ => ⟨ .Countdown n, by sorry ⟩
+  | ⟨.Countdown (n+1), _ ⟩ => ⟨ .Countdown n, by lia ⟩
```
:::

### Implementing our step functions in terms of `tick`

Here's how our `onNone` and `onSome` functions looked before.  

```lean4
def onNone := tick

def onSome (_ev : Unit)
  | .Idle => .Countdown 3
  | s => tick s
```

Our only change needs to be in `onSome`, when we transition from `Idle` to
`Countdown 3`. `lia` works like magic.

::: tip
```diff-lean4
 def onNone := tick

 def onSome (_ev : Unit)
-  | .Idle => .Countdown 3
+  | ⟨.Idle, h⟩ => ⟨ .Countdown 3, by lia ⟩ 
   | s => tick s
```
:::

### Tying it all together

With one final definition using `accumulate`, our job here is done:

```lean4
def crosswalk (ev : ◇ Unit) : { sig // □ (LTL.atom bounded) sig } := 
  FRP.accumulate
    ⟨CrossingState.CrossingState.Idle, by trivial⟩
    CrossingState.onNone
    CrossingState.onSome
    ev
```

Let's look at the type signature of `crosswalk`: we can give it _any_ sequence
of button presses - a polite button presser, an eager spammer, or some other
sequence you or I haven't thought of yet - and out comes a Signal of states
bundled with a safety proof that the hardware never overflows its counter
register.

Last time, we proved the `walkOnlyWhenRed` safety property, manually, for
a given specific reactive program.  Here, the safety property is encapsulated
in its return type.  This means that any FRP program that makes use of `crosswalk`,
like, say:

```lean4
#eval List.range 10 |>.map (fun n => (n, (crosswalk presses) n))
[(0,  CrossingState.Idle),
 (1,  CrossingState.Idle),
 (2,  CrossingState.Idle),        -- t=2: button pressed!
 (3,  CrossingState.Countdown 3),
 (4,  CrossingState.Countdown 2),
 (5,  CrossingState.Countdown 1), -- t=5: button pressed (ignored...)
 (6,  CrossingState.Countdown 0), 
 (7,  CrossingState.Cooldown 3),
 (8,  CrossingState.Cooldown 2),
 (9,  CrossingState.Cooldown 1),
 (10  CrossingState.Cooldown 0),
 (11, CrossingState.Idle)]
```

... or, a larger reactive program that composes `crosswalk` with other
Signals, or possibly any number of button schedule Events, will carry
through that safety property, holding us in good stead, all held together
by Lean's typechecker.

Next time, we'll looking at composing Signals with different safety
properties: As an example, let's go back to our `spammer` Event and see what
the trace looks like:

```lean4
#eval List.range 12 |>.map (fun n => (n, (crosswalk spammer) n))
[(0,  CrossingState.Idle),        -- t=0: button pressed!
 (1,  CrossingState.Countdown 3), -- t=1: button pressed (ignored)
 (2,  CrossingState.Countdown 2), -- t=2: button pressed (ignored, again)
 (3,  CrossingState.Countdown 1), -- ...and so on, forever ...
 (4,  CrossingState.Countdown 0),
 (5,  CrossingState.Cooldown 3),
 (6,  CrossingState.Cooldown 2),
 (7,  CrossingState.Cooldown 1),
 (8,  CrossingState.Cooldown 0),
 (9,  CrossingState.Idle),        -- t=9: button pressed!
 (10, CrossingState.Countdown 3), -- ...and so on, forever ...
 (11, CrossingState.Countdown 2)]
```

No matter how hard we hammer the button, we'll at least once in awhile
eventually get an `Idle` state for crosswise traffic to flow again.
Back in Part 4, this exact event was the counter-example to liveness; `spammer`
could keep cars from ever proceeding. Under the countdown-and-then-cooldown
protocol, that's no longer possible. The system returns to Idle every 9 ticks,
no matter what, which means cars get their turn even under maximum harassment.
We've essentially fixed the liveness violation from Part 4 by introducing
state!

This is a liveness as well as a _fairness_ property: "always, eventually
`Idle`." But because we have an explicit bound (every 9 ticks), it's actually
expressible as a safety property, via a technique called _liveness-to-safety
reduction_. The trick is to augment the state with a deadline counter and
assert "either we're Idle now, or the deadline is still in the future." That
conjunction is an inductive invariant; accumulate would give us `□` of it for
free.  This post is already too long so I won't show you the details here, but
the takeaway is that bounded liveness is closer to within reach than the
safety/liveness distinction usually suggests.

Next time, we'll start composing reactive components, building more interesting
dependency graphs of Signals where one's output values becomes another's
input, and the output's safety property becomes a precondition for the other.

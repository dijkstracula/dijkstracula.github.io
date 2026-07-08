---
layout: post.njk
title: "FRP in Lean: Reactive Events and LTL.eventually"
date: 2026-04-24
tags: [post, lean, reactive-programming, ltl, frp]
excerpt: "If Signals type to LTL.always, what could type to LTL.eventually?"
series: lean-ltl
series_title: "FRP: Events"
---

<script src="/js/frp/runtime.js"></script>

Last time, we introduced Signals, which are time-varying datatypes: at all
time steps `t`, a `Signal a` produces some value of type `a`.  We also saw that
because an `a` is always available, the type of a `Signal a` is `LTL.always a`.
So, we can write `□ a` to refer _both_ to a `a`-producing Signal, as well
as the universally-quantified temporal proposition.

# An Event occurs at some point in time

The dual of a Signal is an Event, which you can think of a stream of values
to be consumed by the system at particular moments in time.  For an interactive
webapp, you might, "right at this moment", send a "click" Event to a form
button, which perhaps triggers other events to fire.  Or, maybe, you enqueue an
event to fire some point in the future, like registering a timeout on a network
call or something.  (If you come from an OOP background, an Event is very
much like an [Observable](https://reactivex.io/documentation/observable.html).)

## Designing an Event type

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
about Events we need to make sure our data definition is well-formed.

Just like Signal, we'll want the type parameterised on whatever the valid
action space is, so it'll be a polymorphic type for sure, so `def Event α :=
... α` is not a terrible place to start.

Since an action can be taken or not taken at any given moment in time, the
rough shape will be `def Event α := Time → (Option α)`.  That this looks a
lot like the datatype for Signal perhaps indicates to us that we're on the
right track, and maybe that Events are actually just a particular sort of
Signal?  (This is a valid design choice -- Elm originally did just this --
but I'm going to deliberately keep the datatypes distinct here.)

OK!  So, in our traffic light example, an Event that corresponds to our
example might look like the following:

::: margin-note
Maybe, in a later installment, we'll revisit the open-termed version of
Event, where input can come in from the outside world.  It might be worth
meditating on what a good datatype for such an Event would be.
:::
```lean4
def Event α := Time → (Option α)
...
-- A pedestrian presses the button at t=2 and t=7
def pedestrianButton : Event Unit := fun t =>
  match t with
  | 2 | 7 => some ()
  | _ => none
```

What we have here is a completed history - a series of events after the fact. A
running FRP program would, of course, incrementally receive events in real time
from an event loop.

With this Event in place, we can wire up the button to a walk sign - whenever
the button is pressed, the walk sign is on; otherwise, the "no walk" sign is.
Similarly, the traffic light can be overridden to `Red`.

::: margin-note
This is a pointwise transformation of a Signal; the Signal is only modified
so long as the pedestrian is holding the button down.  Of course, in the real
world, a pedestrian crossing button delays the lights long enough for them to
cross the road!  We'll soon see the mechanism that lets us retain the value of
an Event over subsequent time steps, but for now, humour me with this one
here.
:::
```lean4
inductive WalkSign where 
 | Walk 
 | DontWalk
deriving Repr, DecidableEq

def walkSignal (button : FRP.Event Unit) : □ WalkSign :=
  fun t => match button t with
    | some () => .Walk
    | none    => .DontWalk

def carLight (button : FRP.Event Unit) : □ Light :=
  fun t => match button t with
    | some () => .Red
    | none    => cycling t

def pedCrossing (button : FRP.Event Unit) : □ (Light × WalkSign) :=
  FRP.map2 Prod.mk (carLight button) (walkSignal button)
```
```lean4
#eval (List.range 5 : List Time).map (pedCrossing pedestrianButton)
    -- output:
    [(Light.Red,    WalkSign.DontWalk), -- t=0: not pressed
     (Light.Yellow, WalkSign.DontWalk), -- t=1: not pressed
     (Light.Red,    WalkSign.Walk),     -- t=2: pressed! carLight is overridden!
     (Light.Red,    WalkSign.DontWalk), -- t=3: not pressed; cycle continues...
     (Light.Yellow, WalkSign.DontWalk)]
```

<style>
  .frp-light-red    { background: #C33 !important; color: white; }
  .frp-light-yellow { background: #F3B31A !important; color: #222; }
  .frp-light-green  { background: #2A8455 !important; color: white; }
  .frp-walk         { background: #2A8455 !important; color: white; }
</style>

:::tip
Try toggling when a button is pressed by clicking the _button_ cell at time
`t`. You'll see the execution history change to reflect the new inputs.
<div id="frp-pedcrossing-graph"></div>
<div id="frp-pedcrossing"></div>
:::

<script>
(() => {
  const g = FRP.graph();
  const LIGHTS = ['Red', 'Yellow', 'Green'];
  const cycling = g.sig('cycling', t => LIGHTS[t % 3]);
  const button  = g.eventAt('button', [2, 7]);
  const walk    = g.map('walk',
    b => b !== null ? 'Walk' : 'DontWalk',
    button);
  const carLight = g.map2('carLight',
    (b, c) => b !== null ? 'Red' : c,
    button, cycling);
  g.map2('pedCrossing', (l, w) => [l, w], carLight, walk);
  function lightCell(v) {
    if (v === 'Red')    return { text: 'R', className: 'frp-light-red' };
    if (v === 'Yellow') return { text: 'Y', className: 'frp-light-yellow' };
    if (v === 'Green')  return { text: 'G', className: 'frp-light-green' };
    return v;
  }
  function format(v, name, t, node) {
    if (name === 'cycling' || name === 'carLight') return lightCell(v);
    if (name === 'walk') {
      return v === 'Walk' ? { text: 'W', className: 'frp-walk' } : '·';
    }
    if (name === 'pedCrossing') return v[0][0] + ',' + v[1][0];
    return FRP.defaultFormat(v, name, t, node);
  }
  const gv = FRP.renderGraph(document.getElementById('frp-pedcrossing-graph'), g,
                             { ticks: 12, format });
  const tv = FRP.renderTiming(document.getElementById('frp-pedcrossing'), g,
                              { ticks: 12, format, controls: true });
  tv.subscribe(t => gv.setTick(t));
})();
</script>

## The Curry-Howard correspondence for Events...sort of...

Given that `Signal T` guarantees a `T` at all time steps, and an `Event T` is
really about the moments of time in which `T` holds, you might naturally
conclude that the LTL type that corresponds to an Event is `eventually`:
after all, this is clearly true of `pedestrianButton`: It's clearly eventually
pressed twice!

```lean4
namespace LTL
  prefix:max "◇ " => eventually  -- Prop: ∃ t, p (drop t trace)
end LTL

namespace FRP
  notation "◇ " α => Event α -- Type: Time → Option α
end FRP
```

The interpretation of `◇ α` very well _ought_ to be "there exists a time when α
holds", but this correspondence doesn't _quite_ work for our formulation.  Think
about an event that never fires!  As currently defined, there's nothing stopping
us from writing:

```lean4
-- never typechecks as an Event...
def never : FRP.Event α := fun _ => none

-- ...but the corresponding ◇ proposition is false:
theorem neverFires : ¬ (∃ t : Time, (never (α := α) t).isSome) := by
  intro ⟨t, hSome⟩ -- "<" and ">" destructures the existential
  simp [never] at hSome

```

For `◇ α` to be strictly-speaking well-typed, we would need to provide a
_witness_ that proves it will eventually fire, no matter what the current
timestamp is.  (If you remember the last post in this series, providing a
witness with the `exact` tactic was precisely how we did it!).  What we really
have here is ` □ (Option α)`; `◇` only emerges when you additionally prove `∃
t, (e t).isSome`.

Come to think of it, being able to state that proposition is broadly useful,
so let's give it a name:

```lean4
def fires (e : Time → Option α) : Prop := ∃ t, (e t).isSome
```

The more exact version of an Event would bundle the event with a proof that
it will, in fact, eventually fire.  

:::margin-note
Just like with respect to Signals: in Agda, we would get this for free.
:::
```diff-lean4
 namespace FRP
   structure Event (α : Type) where
     f : Time → Option α
+    live : fires f

   notation "◇ " α => Event α
 end FRP

 def pedestrianButton : ◇ Unit := ⟨
+ -- As before, we fire at t=2 and t=7...
  (fun t =>
    match t with
    | 2 | 7 => some ()
    | _ => none),
+ -- ...but unlike before, we provide a witness that we
+ -- fire at least once.
+ ⟨2, by simp⟩⟩ 
```

## A few Event typeclass instances

Just like how we implemented some typeclasses on Signals last time, we can do
the same with Events.

### Making an Event callable with `CoeFun`

`CoeFun` is a typeclass that makes a type "callable" with function application
syntax, like `Fn` in Rust or `operator()` in C++.  A `CoeFun (Event a)` just
passes along the argument to the `.f` field.

```lean4
namespace FRP
  ...
  instance : CoeFun (Event α) (fun _ => Time → Option α) where
    coe e := e.f
end FRP

#eval (List.range 5 : List Time).map (pedCrossing pedestrianButton)
    -- output, just like before:
    [(Light.Red, WalkSign.DontWalk),
     (Light.Yellow, WalkSign.DontWalk),
     (Light.Red, WalkSign.Walk),
     (Light.Red, WalkSign.DontWalk),
     (Light.Yellow, WalkSign.DontWalk)]
```

### Making an Event a `Functor`

Next, just like how we made Signal a `Functor`, so too can we with Event.
I'm not sure we'll necessarily need this, but it's pretty easy to imagine a map
operation over an Event, changing the event payload when it fires (but not
changing when it, itself fires).  `Functor` is a good typeclass for that.
And, as it happens, implementing this is good practice for wrangling our new
proof-carrying version of Event anyway.

OK, here's the skeleton for a `Functor`:

```lean4
instance : Functor Event where
  map f ev := ... -- TODO
```

In our non-proof carrying Event, this would be super-straightforward:
we'd just produce a new function that consumes a `t`, applies it to `ev`
to get an `Option α`, and then applies `f` to that if it's a `some`:

```lean4
instance : Functor Event where
  map f ev := 
    let ev' := fun t => Option.map f (ev t)
    ev
```

Sadly this isn't enough for us, because what we _actually_ need to do is
produce that new function, but also with a proof that _it, too_ eventually
fires!

```diff-lean4
 instance : Functor Event where
   map f ev :=
-    let ev' := fun t => Option.map f (ev t)
-    ev
+    let f' := fun t => Option.map f (ev t)
+    have staysLive : fires f' := by 
+      sorry -- TODO: what's the _actual_ proof?
+    ⟨f', staysLive⟩
```

It shouldn't be too hard to convince yourself that this is a true statement.
After all, this is a pointwise transformation on `ev`: we know that _it_ fires
(because it contains a proof, `ev.live : fires ev.f` that states as such),
and we're never removing or adding `Option.some` out of the event stream.
Let's prove the `live` proposition formally!

```lean4
have staysLive : fires f' := by

1 goal
α✝ β✝ : Type
f : α✝ → β✝
ev : Event α✝
f' : Time → Option β✝ := fun t => Option.map f (ev.f t)
⊢ fires f'
```

We can see from our proof state that `f'` is the right type: it's a `Time →
Option β`.  Now, we don't have to explicitly do this, but I think it's nice
to state clearly that already have a proof that the previous Event fired:

```diff-lean4
 have staysLive : fires f' := by
+  have wasLive : fires ev.f := ev.live

 1 goal
 α✝ β✝ : Type
 f : α✝ → β✝
 ev : Event α✝
 f' : Time → Option β✝ := fun t => Option.map f (ev.f t)
+wasLive : fires ev.f
 ⊢ fires f'
```

Notice the symmetry between the goal we're trying to prove, and the `wasLive`
assumption in our context.  Let's unfold both uses of `fires` and `f'`.

```diff-lean4
 have staysLive : fires f' := by
   have wasLive : fires ev.f := ev.live
+  unfold fires at * ; unfold f'

 1 goal
 α✝ β✝ : Type
 f : α✝ → β✝
 ev : Event α✝
 f' : Time → Option β✝ := fun t => Option.map f (ev.f t)
-wasLive : fires ev.f
+wasLive : ∃ t, (ev.f t).isSome = true
-⊢ fires f'
+⊢ ∃ t, (Option.map f (ev.f t)).isSome = true
```

The goal is looking extremely close to wasLive!  The only difference is that
we're now applying `Option.map f`.  Our intuition told us earlier that
`Option.map` should preserve all the `some` values, and indeed [there's a
theorem that says just
that](https://github.com/leanprover/lean4/blob/0eb80e34a660f54b88002b33c4d93965651c71cb/src/Init/Data/Option/Lemmas.lean#L297):

```diff-lean4
 have staysLive : fires f' := by
   have wasLive : fires ev.f := ev.live
   unfold fires at * ; unfold f'
+  simp [Option.isSome_map]

 1 goal
 α✝ β✝ : Type
 f : α✝ → β✝
 ev : Event α✝
 f' : Time → Option β✝ := fun t => Option.map f (ev.f t)
 wasLive : ∃ t, (ev.f t).isSome = true
-⊢ ∃ t, (Option.map f (ev.f t)).isSome = true
+⊢ ∃ t, (ev.f t).isSome = true
```

Now our goal is exactly the same as `wasLive`, so either `assumption` or `exact
wasLive` will complete the goal.  Since `Option.isSome_map` is marked as
`@simp`, if we change our unfoldings to just simplifications, and apply `ev.live`
directly instead of giving it its own name, we can simplify the proof down.

```diff-lean4
 have staysLive : fires f' := by
-  have wasLive : fires ev.f := ev.live
-  unfold fires at * ; unfold f'
-  simp [Option.isSome_map]
+  simp [fires, f', Option.isSome_map] at * 
+  exact ev.live

-1 goal
-α✝ β✝ : Type
-f : α✝ → β✝
-ev : Event α✝
-f' : Time → Option β✝ := fun t => Option.map f (ev.f t)
-wasLive : ∃ t, (ev.f t).isSome = true
-⊢ ∃ t, (ev.f t).isSome = true
+Goals accomplished!
```

With the proof completed, we can complete our `Functor` implementation

::: margin-note
Don't forget that, while I'm using anonymous constructor syntax, you could
specify the fields in an Event directly, by writing `{f := f', live :=
staysLive}` instead of `⟨f', staysLive⟩`.
:::
```diff-lean4
 instance : Functor Event where
   map f ev :=
     let f' := fun t => Option.map f (ev t)
     have staysLive : fires f' := by
-      sorry -- TODO: what's the _actual_ proof?
+      simp [fires, f', Option.isSome_map] at *
+      exact ev.live
     ⟨f', staysLive⟩
```

## A few Event combinators: `merge`

Let's write a few more small combinators that we might need in later posts,
before returning to the traffic light example.  

`merge` takes two Events and "unions" them together:

```lean4
def Event.merge (e1: Event α) (e2 : Event α) : Event α := 
  let f := fun t => ... -- TODO 
  let fires : fires f := by sorry -- TODO
  ⟨f, fires⟩
```

Implemeting the `a`-producing function is straightforward enough: we'll take
check whether `e1 t` produces a `some` value, or defer to `e2 t` if not. We can
use `Option.orElse`, or the
[Alternative](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/#Alternative___mk)
typeclass's `<|>` operator.

```diff-lean4
 def Event.merge (e1: Event α) (e2 : Event α) : Event α := 
-  let f := fun t => ... -- TODO 
+  let f := fun t => e1 t <|> e2 t
   let fires : fires f := by sorry -- TODO
   ⟨f, fires⟩
```

To prove `fires`, we'll proceed in the same way as before, simplifying
away `fires` and `f'`.

```lean4
let fires : fires f := by
  simp [fires, f]

1 goal
α : Type
e1 e2 : Event α
f : Time → Option α := fun t => e1.f t <|> e2.f t
⊢ ∃ t, (e1.f t).isSome = true ∨ (e2.f t).isSome = true
```

::: margin-note
`exists_or` is a _biconditional_, not just an ordinary one-way implication.
The proof term has two fields, depending on which way you want the proof to go:
when you want the left-to-right implication, extract it with `.mp` (for modus
ponens); for the right-to-left, use `.mpr`.
:::
Using the
[exists_or](https://github.com/leanprover/lean4/blob/master/src/Init/PropLemmas.lean#L314)
lemma, we can factor out the `exists` such that we're left with two existential
disjunctions.

```diff-lean4
 let fires : fires f := by
   simp [fires, f]
+  apply exists_or.mpr

 1 goal
 α : Type
 e1 e2 : Event α
-f : Time → Option α := fun t => e1.f t <|> e2.f t
+f : Time → Option α := ⋯
-⊢ ∃ t, (e1.f t).isSome = true ∨ (e2.f t).isSome = true
+⊢ (∃ x, (e1.f x).isSome = true) ∨ ∃ x, (e2.f x).isSome = true
```

This is great because `(∃ x, (e1.f x).isSome = true)` is precisely `e1.live`,
and `(∃ x, (e2.f x).isSome = true)` is `e2.live`!  To satisfy the disjunction
we just need to show one side, so let's choose `left` followed by `exact e1.live`,
closing the goal and completing the combinator.

```diff-lean4
 def Event.merge (e1: Event α) (e2 : Event α) : Event α :=
   let f := fun t => e1 t <|> e2 t
   let fires : fires f := by
     simp [fires, f]
     apply exists_or.mpr
+    left ; exact e1.live
   ⟨f, fires⟩

Goals accomplished!
```

::: tip
<div id="frp-event-merge"></div>
:::
<script>
(() => {
  const g = FRP.graph();
  const p1 = g.eventAt('press1', [2, 8]);
  const p2 = g.eventAt('press2', [4, 8]);
  g.merge('press1 <|> press2', p1, p2);
  FRP.renderTiming(document.getElementById('frp-event-merge'), g, { ticks: 10 });
})();
</script>

## Bridging Events and Signals with a stateful Signal

here's one more combinator that might come in handy for us.  Suppose we'd like
a way to "retain" the most recent `a` that was fired by a `Event a` at some
point in time.  We'll call this combinator `latch`:  It'll consume that `Event a`
and produce the corresponding `Signal a`, which you can think of as a constant
Signal in between different events firing.

To make the signal well-defined, the user will supply an initial value that the
Signal will produce before the first firing.

```lean4
def Event.latch (init: α) (e: Event α) : Signal α :=
  fun t => ...
```

When `t=0`, we either produce `e 0` if it happened to fire, or else `init`.
When `t=(n+1)`, we either produce `e (n+1)` if _it_ happened to fire, or else
recurse.  Easy enough to write via structural recursion on the input `Time`:

::: margin-note
`getD` produces a default value if the supplied `Option` is `none`; it's a
special form that only lazily evaluates the default argument.
:::
```lean4
def Event.latch (init: α) (e: Event α) : Signal α
  | 0 => (e 0).getD init
  | (n + 1) => (e (n + 1)).getD (latch init e n)
```

::: tip
<div id="frp-latch"></div>
:::

<script>
(() => {
  const g = FRP.graph();
  const beep = g.event('beep', t => {
    if (t === 1) return 'A';
    if (t === 4) return 'C';
    if (t === 7) return 'E';
    return null;
  });
  g.latch('lastNote', '—', beep);
  FRP.renderTiming(document.getElementById('frp-latch'), g, { ticks: 10 });
})();
</script>

This is our first example of a Signal whose value is not a straightforward
computation from the given timestep, but relies on past values.  In the next
post, we'll have a lot to say about stateful Signal combinators.

## Proving a safety property involving events

Last time we discussed safety properties, which are propositions that must
always hold for a Signal.  Let's see what happens when Events get mixed
into a reactive program with a safety property.

There's a pretty clear safety property for our traffic light example: when the
walk sign is on, the traffic light better be red!

```lean4
def walkOnlyWhenRed (button : ◇ Unit) : Prop :=
  LTL.always
    (LTL.atom (fun (traffic, ped) => ped = .Walk → traffic = .Red))
    (pedCrossing button)

theorem walkSafe (button : ◇ Unit) : walkOnlyWhenRed button := by 
  -- TODO

1 goal
button : FRP.Event Unit
⊢ walkOnlyWhenRed button
```

We'll proceed as before: first we'll simplify the domain-specific definitions
for the traffic light problem, and then simplify away the LTL and FRP primitives.

```diff-lean4
-theorem walkSafe (button : ◇ Unit) : walkOnlyWhenRed button := by 
-  -- TODO
+theorem walkSafe (button : ◇ Unit) : walkOnlyWhenRed button := by
+  simp [walkOnlyWhenRed, pedCrossing]
+  simp [LTL.always, LTL.atom, now, drop, FRP.map2]
+  simp [carLight, walkSignal]

 1 goal
 button : FRP.Event Unit
-⊢ walkOnlyWhenRed button
+⊢ ∀ (i : ℕ),
+  (match button i with
+      | some PUnit.unit => WalkSign.Walk
+      | none => WalkSign.DontWalk) =
+      WalkSign.Walk →
+    (match button i with
+      | some PUnit.unit => Light.Red
+      | none => cycling i) =
+      Light.Red
```

Now we can introduce our time value and split on the possible values of `button i`:

```diff-lean4
 theorem walkSafe (button : FRP.Event Unit) : walkOnlyWhenRed button := by
   simp [walkOnlyWhenRed, pedCrossing]
   simp [LTL.always, LTL.atom, now, drop, FRP.map2]
   simp [carLight, walkSignal]
+  intro t
+  split <;>

-1 goal
+2 goals
-⊢ ∀ (i : ℕ),
-  (match button i with
-      | some PUnit.unit => WalkSign.Walk
-      | none => WalkSign.DontWalk) =
-      WalkSign.Walk →
-    (match button i with
-      | some PUnit.unit => Light.Red
-      | none => cycling i) =
-      Light.Red
+case h_1
 button : FRP.Event Unit
+t : ℕ
+x✝ : Option Unit
+heq✝ : button t = some PUnit.unit
+⊢ WalkSign.Walk = WalkSign.Walk → Light.Red = Light.Red
+case h_2
+button : FRP.Event Unit
+t : ℕ
+x✝ : Option Unit
+heq✝ : button t = none
+⊢ WalkSign.DontWalk = WalkSign.Walk → cycling t = Light.Red
```

`simp` is enough to discharge both these goals, so `split <;> simp` completes
the safety proof.  Our final proof:

```lean4
theorem walkSafe (button : ◇ Unit) : walkOnlyWhenRed button := by
  simp [walkOnlyWhenRed, pedCrossing]
  simp [LTL.always, LTL.atom, now, drop, FRP.map2]
  simp [carLight, walkSignal]
  intro t
  split <;> simp
```

You might be tempted to say, "ah, we've proven a safety property, but liveness
is also trivial: a pedestrian can _always_ press the button and cross, so "a
good thing will always happen" is similarly trivial.  The more interesting
liveness property is actually about _cars_: is it the case that the traffic
light will ultimately go green, allowing vehicle traffic to move again?

Not if we press the button _every clock tick_!

```lean4
def spammer : ◇ Unit := ⟨fun _ => some (), ⟨0, by simp⟩⟩

#eval (List.range 5 : List Time).map (pedCrossing spammer)
-- output:
[(Light.Red, WalkSign.Walk),
 (Light.Red, WalkSign.Walk),
 (Light.Red, WalkSign.Walk),
 (Light.Red, WalkSign.Walk),
 (Light.Red, WalkSign.Walk)]
```

Indeed, we can prove that our liveness property does _not_ hold here:
pedestrians will starve out motorists.

```lean4
def carsEventuallyGreen (button : ◇ Unit) : Prop :=
  LTL.always (LTL.eventually (LTL.atom (· = .Green)))
    (carLight button)

example : ¬ carsEventuallyGreen spammer := by
  simp [carsEventuallyGreen, spammer]
  simp [LTL.always, LTL.eventually, LTL.atom, now, drop]
  unfold carLight; simp
```

::: margin-warning
If you're not yet like me, might I suggest [Life After Cars: Freeing Ourselves
From The Tyranny of the Automobile](https://www.lifeaftercars.com/)?

Maybe a more sympathetic starvation example might be [my neighbourhood
drawbridge](https://en.wikipedia.org/wiki/Fremont_Bridge_(Seattle)) that
periodically needs to raise itself, preventing the flow of pedestrians,
cyclists, AND motorists, whenever a ship needs to sail through the canal. Since
marine traffic has legal priority, without a cooldown protocol, the bridge
could be left perpetually raised.
:::
This is not a problem if, like me, you hate how cars have ruined cities and
have no moral objection to ceding this intersection entirely to pedestrians
and cyclists. However, proving fairness is pretty important in other contexts:
we might want a _fair OS scheduler_ to always, eventually, schedule a
ready-to-run job, or a _fair mutex_ to always, eventually, cede the critical
section to a waiter.

## Fairness ensures (eventual) progress

Let's consider two problems in one here: first, the pedestrian button should
light the walk sign for more than just one timestep; and, we should have a
cooldown period where pressing the button doesn't actually trigger a light
change, to let vehicles, ugh, progress for a bit.

```lean4
structure CrossingState where
  countdown : Nat -- How many ticks remain for the walk light
  cooldown  : Nat -- How many ticks until the button works again
deriving Repr
```

So, for instance, if some `Signal CrossingState` had a cooldown of `4` at some
time `t`, we'd expect the value at `t+1` to be `3`, and so on.

More broadly: our goal is to move towards a traffic light policy where, in
order for a pedestrian button Event to actually affect the light cycle,
`cooldown` must be zero; and, the Walk sign must be lit up until `countdown`
goes to zero.

Clearly we need to transform an `Event Unit` into a `Signal CrossingState`.
However, we've only seen _pointwise Signal transformations_ like `map`, and
that isn't expressive enough for us.  In order to implement a `Signal
CrossingState` that correctly counts down, we need to be able to look backwards
into previous states (otherwise, how would we know the previous countdown
values to subtract from?)

Next time, we'll look into extending our FRP API to accomplish just that.

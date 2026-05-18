---
layout: post.njk
title: "FRP in Lean: Reactive Signals and LTL.always"
date: 2026-04-17
tags: [post, lean, reactive-programming, ltl, frp]
excerpt: "So if propositions are types, and LTL are propositions, what programs are well-typed by LTL?"
series: lean-ltl
series_title: "Intro to FRP: Signals"
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
Notice that this is the same type as our execution traces!  That's not entirely
a coincidence.  The _interpretation_ of a signal is different, though.
Earlier, a `Trace` was an artifact of running some computation; it was in some
sense an "output".  You can poke at the trace by writing theorems about it, but
it otherwise just sits there; running the system through our monadic API
produced it, and then we use Lean's theorem proving capabilities to inspect it.

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

::: margin-note
`delay` is the usual term for this, but it's really more of an `advance`, if you
think about it.
:::
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

```lean4
def map (f: α → β) (s : Signal α) : Signal β := 
  fun t => f (s t)  

def map2 (f: α → β → γ) (s1 : Signal α) (s2 : Signal β) : Signal γ := 
  fun t => f (s1 t) (s2 t)
```

These map functions are called _pointwise_ because they only operate on a
signal at the "present moment" (that is, whatever the value of `t` is). You
could imagine a _time-dependent transformation_ that somehow involves other
values of `t` (say, computing the finite difference of `t` and `t-1`) but we
can't do that with `map`.  We'll write a combinator for such time-dependent
operations in the [next post](/posts/lean-ltl-5), though, so stay tuned.

### `const`, `map` and `map2` give us `Functor`s and `Applicative`s

Implementing the `Functor` typeclass for `Signal` is straightforward: it only
requires one definition, `map: (α → β) → f α → f β`, and that's exactly what
our `map` does.  This means we can use the `<$>` operator to map a function
through a `Signal`.

```lean4
instance : Functor Signal where
  map := FRP.map -- AKA <$>
```

::: margin-note
Should perhaps `Signal`s also be Monads?  Stay tuned for the tradeoffs.
:::
If you're a type zoologist, you might recognise that `const` and `map2`
mean that `Signal` is an applicative functor (which are more expressive than
ordinary functors but not as expressive as a Monad - we have defined `map` but
not `bind`).  For a `Signal` to be an `Applicative`, we need to define two
operations on it, `pure`, which lifts a value into the `Applicative`, and `seq`,
which sequences the 

If you're _not_ a type zoologist, `Applicative`s can be thought of as
"sequencing"

The definition for `Applicative.pure : α → f α` is `const` - it's kind of the
only thing that makes sense for the type signature.  

::: margin-note
`seq` is typically defined as `f (α → β) → f α → f β`; the second argument
being a thunk lets `seq` choose whether to actually produce the `f a` or not.
In Haskell, where everything is lazily-evaluated, that's never a concern.
:::
`Applicative.seq : f (α → β) → (Unit → f α) → f β` is the gnarlier one. `seq sf
sx` says "Produce a `Signal` that samples the _function_ from `sf` at time `t`,
samples the value from `sx` at the same time (after forcing the thunk), and
applies the former to the latter". That's a lot of words, but it's not a lot of
code if we use `map2` for this, since what combines its arguments is function
application.

```lean4
instance : Applicative Signal where
  pure := FRP.const
  seq sf sx := FRP.map2 (fun f x => f x) sf (sx ())  -- AKA <*>
```

It's probably not obvious why it makes sense to talk about a `Signal (a -> β)`,
but in the next section we'll see how they can come about.

## Our first reactive program

OK, here's our first reactive program.  Suppose we have a bunch of
sensors that measure temperatures over time: modeling those as `Signal`s
is a great idea since temperatures are of course time-varying:

```lean4
-- A list of temperature sensors, one per zone:
def bedroom : Signal Float := fun t => 20.0 + Float.sin t.toFloat
def kitchen : Signal Float := fun t => 21.0 + Float.cos t.toFloat
def lvingrm : Signal Float := fun t => 19.5 + 0.5 * Float.sin (2 * t.toFloat)

#eval (bedroom 42, kitchen 42, lvingrm 42) -- (19.083478, 20.600015, 19.866595)
```

Using `map`, we can convert these Celsius signals into Fahrenheit, by mapping
over a conversion function, for our American friends:

```lean4
def ctof (sc : Signal Float) : Signal Int32 := 
  (fun c => (c * 9./5. + 32).round.toInt32) <$> sc

#eval ctof bedroom 3 -- 68 (comfy!)
```

If we wanted to separate out the rounding and truncation into their own functions,
we could certainly do that too: notice that we read this right-to-left: we start
with the input `Signal`, first apply the conversion function, and _then_ apply
the rounding and integer conversion function.

```lean4
def ctof (sc : Signal Float) : Signal Int32 :=
  (·.round.toInt32) <$> (· * 9./5. + 32) <$> sc
```

Suppose we want to approximate the hallway temperature by taking the average of
the bedroom and kitchen sensors.  Since `avg` is a function of two arguments,
we can't use `map` aka `<$>` directly. `map2`, though, does let us write this:

```lean4
def avg (x y : Float) : Float := (x + y) / 2.0
def hallway : Signal Float := map2 avg bedroom kitchen
```

Since we defined `Applicative.seq` in terms of `map2`, it stands to reason that
we should be able to use `<*>` to implement `hallway`, too.  And indeed we can!
In applicative style, we'd map, using `<$>`, first over `bedroom`: since `avg :
Float -> Float -> Float` and `bedroom : Signal Float`, we end up with a curried
`Signal (Float -> Float)`.  That's a `Signal` of a function that takes in a
`Float` and averages it with the current value of `bedroom`!

If we then use `<*>` to apply `kitchen` inside the `Signal`, we end up with the
expected `Signal Float`.

::: margin-note
There's a way to write `hallway` using only `<*>`, and the Applicative laws
guarantee that it'll do the same thing.  Can you find it?
:::
```lean4
def hallway : Signal Float := avg <$> bedroom <*> kitchen
```

Next: we might want to collect all the `Signal`s on hand here into a `List`.
For instance, maybe we want to average all the current temperatures or report
the coldest room or something.

```lean4
def sensors : List (Signal Float) := [bedroom, kitchen, lvingrm, hallway]
```

The problem is that all those operations would require a `Signal (List Float)`,
instead of the `List (Signal Float)` that we've actually got.  Good news
though! Using
[List.mapA](https://github.com/leanprover/lean4/blob/0eb80e34a660f54b88002b33c4d93965651c71cb/src/Init/Data/List/Control.lean#L76),
which for some `Applicative m`, has type `List (m α) -> m (List α)`, we can do
just that inversion.

::: margin-note
Haskellers might note that if `Signal` was a monad, we could use the more
common `mapM` combinator in place of `mapA`.
:::
```lean4
-- At each tick, gather all readings into a list:
def readings : Signal (List Float) := List.mapA id sensors

#eval readings 42 -- [19.083478, 20.600015, 19.866595, 19.841747]
```

Now any list aggregation just maps over the sequence`Signal:

```lean4
def avgTemp : Signal Float := (fun rs => rs.sum / rs.length) <$> readings
def minTemp : Signal Float := List.minimum <$> readings

def alertIfHot : Signal Bool := (fun rs => rs.any (· > 30.0)) <$> readings
```

A note about the first argument to `List.mapA`: as the name suggests, this
function maps over a list of `Signal`s before collating them into a single
`Signal (List β)`.  We passed in the identity function when defining
`readings`, but we can compose surprisingly interesting things with only
a small code change:

::: margin-note
Looking at the docs, `mapA` takes a function of type `a -> Signal b` in this
context.  Neither `id` nor `ctof` are obviously shaped like this function,
though.  If you're familiar with unification in the context of type inference,
you might find it interesting to trace how Lean would typecheck this.
:::
```lean4
def alertIfHotF : Signal Bool :=
  (fun rs => rs.any (· > 90)) <$> List.mapA ctof signals
```

You might say that this is not the most realistic program, but nonetheless I
think it nicely shows what makes FRP cool.  Before proceeding, pause and ponder
how you might write this program in your favourite language of choice, and I
imagine you'll conclude that FRP has some nice design properties.

## A new domain: a traffic intersection

Sensor data is a nice example of continuous-valued FRP. Let's now look at a
discrete-valued Signal, a traffic light, that'll set up our running example for
injecting external events into the system in the next post.

Here's a silly data definition for that traffic light.  Let's write a signal
that defines how a value of this type could change over time, say, where the
colour changes once per time step:

::: margin-warning
Technically the `panic!` won't typecheck here, but, we're going to improve
this immediately, anyway.
:::
```lean4
inductive Light where | Red | Yellow | Green
deriving Repr

def cycling : Signal Light := 
  fun n => 
    match n % 3 with 
    | 0 => .Red
    | 1 => .Yellow
    | 2 => .Green
    | _ => panic! "impossible: forall n, 0 <= n % 3 < 3"

#eval cycling 42 -- Light.red
```

Not the most realistic definition of a traffic light, but whatever.  

### Matching on a value and proof to eliminate imposible branches

A quick diversion into how dependent types can help us write simple programs
more easily:

::: margin-note 
Maybe in a future blog series, we'll look at how typecheckers implement their
exhaustiveness checker...
:::
In Lean and other functional languages that have _exhaustiveness checking_, we,
to make the pattern matching well-formed for all possible values of `n`, have a
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
value?". The pair in the first match arm would be `0 : Nat, 0 < 3 : Prop` (the
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

::: margin-note
Because Lean's elaborator is type-aware, when multiple syntactically-equivalent
notations could be chosen, it can use type information from context to pick the
right one.  In principle, this means we can just write `□ ...` and Lean will
do the rest!
:::
```lean4
namespace LTL
    ...
    prefix:max "□ " => always    -- Prop: ∀ t, p (drop t trace)
end LTL
namespace FRP
    notation "□ " α => Signal α  -- Type: Time → α
end FRP
```

::: warning
In Lean, we have to be a bit careful: in a previous article we discussed that
`Prop`s and `Type`s differ: one lives in "the logical world" and the other "the
computational world".  The LTL-types-FRP paper is implemented in Agda, another
dependently-typed language but one that doesn't have this division.  

So, in Agda, we could simply define `□` once and use it in both contexts:
"write a well-typed FRP program" is _literally_ "prove an LTL property".  In
Lean, a `Signal α` is a function `Time → α` that produces a value at every time
step, and a proof of `□ p` is a function `forall t: Time, proof` that produces
evidence at every time step.  Here we are tacitly leaning on the Curry-Howard
correspondence between function types and universal quantifiers.  (This
language design choice on the part of Lean buys some ergonomic simplicity but
at the expense of expressiveness, which we can see when comparing our
implementation to how it's done in Agda.)
:::

On its own, this isn't all that interesting, because so far the `α` type parameters
we've seen for Signal (`Int`, `String`, `Light`) themselves aren't all that
interesting as logical propositions.  If you told a Java programmer
"`String.valueOf(i)` proves `String` given a proof of `Int`, isn't type theory
amazing??", they probably wouldn't be impressed; similarly, "A `Signal Int`
always makes an `Int` available" isn't super profound on its own either.  We
need a second fundamental FRP primitive to add reactivity to FRP systems, which
we'll introduce soon enough.

But anyway, here're the new type signatures with their LTL-inspired typings:

```lean4
-- The current time is always available
def now : □ Time := fun t => t

-- If I always have an α, I can always transform it into a β.
def map (f: α → β) (s : □ α) : □ β := 
  fun t => f (s t)  

-- ...and if I always have both an α and a β, can do the same to always have a γ
def map2 (f: α → β → γ) (s1 : □ α) (s2 : □ β) : □ γ := 
  fun t => f (s1 t) (s2 t)
```

## Proving a safety property about an FRP program

Recall from last time that `□`-statements form _safety properties_, of the
form "it's always the case that a bad state is never reached."  A traffic
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

example : neverBothGreen := by -- TODO

1 goal
⊢ neverBothGreen
```

Right now the goal is pretty opaque, so let's unfold the definitions of `neverBothGreen`
and `junction` so we actually have something to work with:

```diff-lean4
-example : neverBothGreen := by -- TODO
+example : neverBothGreen := by
+  simp [neverBothGreen, junction, l1, l2]

 1 goal
-⊢ neverBothGreen
+⊢ □ (LTL.not (LTL.atom fun x => x.1 = Light.Green ∧ x.2 = Light.Green)) 
+    (FRP.map2 Prod.mk cycling (FRP.delay cycling 1))
```

Great, that gives us something to actually work with now.  Next, let's unfold
our relevant LTL primitives.  That will give us a quantifier over `Time` that
we can also introduce into the context.

```diff-lean4
 example : neverBothGreen := by
   simp [neverBothGreen, junction, l1, l2]
+  simp [LTL.always, LTL.not, LTL.atom]
+  intro t

 1 goal
+t : ℕ
-⊢ □ (LTL.not (LTL.atom fun x => x.1 = Light.Green ∧ x.2 = Light.Green)) 
-    (FRP.map2 Prod.mk cycling (FRP.delay cycling 1))
+⊢  (now (drop t (FRP.map2 Prod.mk cycling (FRP.delay cycling 1)))).1 = Light.Green →
+  ¬(now (drop t (FRP.map2 Prod.mk cycling (FRP.delay cycling 1)))).2 = Light.Green
```

So far so good; that seems like a nice theorem to prove.  Now let's unfold our
FRP operators like we did the LTL ones.

::: margin-note
Don't forget that both `l1` and `l2` were defined in terms of `cycling`, hence
we see two occurrences of it in this simplified form.  You might find it
interesting to reimplement `l1` and `l2` with distinct implementation to see
how the form of the proof might change.
:::
```diff-lean4
 example : neverBothGreen := by
   simp [neverBothGreen, junction, l1, l2]
   simp [LTL.always, LTL.not, LTL.atom]
   intro t
+  simp [now, drop, FRP.map2, FRP.delay]

 1 goal
 t : ℕ
-⊢  (now (drop t (FRP.map2 Prod.mk cycling (FRP.delay cycling 1)))).1 = Light.Green →
-  ¬(now (drop t (FRP.map2 Prod.mk cycling (FRP.delay cycling 1)))).2 = Light.Green
+⊢ cycling t = Light.Green → ¬cycling (t + 1) = Light.Green
```

After all that, we can finally unfold `cycling` and get down to the crunchy
modular arithmetic that makes up the lights' behaviour.

::: margin-note
You might be tempted, since there's an implication here, to `intro` the antecedent as a
`h_green_now` theorem or something.  The problem with doing that is that we'll need to
eventually case-split on `t % 3`.  You might find it amusing/annoying to try introing
it and seeing where you get stuck.
:::
```diff-lean4
 example : neverBothGreen := by
   simp [neverBothGreen, junction, l1, l2]
   simp [LTL.always, LTL.not, LTL.atom]
   intro t
   simp [now, drop, FRP.map2, FRP.delay]
+  simp [cycling]

 1 goal
 t : ℕ
-⊢ cycling t = Light.Green → ¬cycling (t + 1) = Light.Green
+⊢ (match t % 3, ⋯ with
+    | 0, x => Light.Red
+    | 1, x => Light.Yellow
+    | 2, x => Light.Green) = Light.Green →
+  ¬(match (t + 1) % 3, ⋯ with
+      | 0, x => Light.Red
+      | 1, x => Light.Yellow
+      | 2, x => Light.Green) = Light.Green
```

So now let's `split` on the antecedent `match`, leaving us with three
cases depending on the value of `t % 3`, noting that `h_1` and `h_2`
could immediately be discharged away:

```diff-lean4
 example : neverBothGreen := by
   simp [neverBothGreen, junction, l1, l2]
   simp [LTL.always, LTL.not, LTL.atom]
   intro t
   simp [now, drop, FRP.map2, FRP.delay]
   simp [cycling]
+  split

-1 goal
+3 goals
+case h_1
 ...
-t : ℕ
-⊢ (match t % 3, ⋯ with
-    | 0, x => Light.Red
-    | 1, x => Light.Yellow
-    | 2, x => Light.Green) = Light.Green →
-  ¬(match (t + 1) % 3, ⋯ with
-      | 0, x => Light.Red
-      | 1, x => Light.Yellow
-      | 2, x => Light.Green) = Light.Green
+heq✝¹ : t % 3 = 0
+⊢ Light.Red = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
+case h_2
+...
+heq✝¹ : t % 3 = 1
+⊢ Light.Yellow = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
+case h_3
+...
+heq✝¹ : t % 3 = 2
+⊢ Light.Green = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
```

For each of these three cases, we have three more possibilities, so let's
`split` on _those_, too:

```diff-lean4
 example : neverBothGreen := by
   simp [neverBothGreen, junction, l1, l2]
   simp [LTL.always, LTL.not, LTL.atom]
   intro t
   simp [now, drop, FRP.map2, FRP.delay]
   simp [cycling]
-  split
+  split <;> split

-3 goals
+9 goals
 case h_1
 ...
 heq✝³ : t % 3 = 0
+heq✝¹ : (t + 1) % 3 = 0
-⊢ Light.Red = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
+⊢ Light.Red = Light.Green → ¬Light.Red = Light.Green
 case h_2
 ...
 heq✝³ : t % 3 = 0
+heq✝¹ : (t + 1) % 3 = 1
-⊢ Light.Red = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
+⊢ Light.Red = Light.Green → ¬Light.Yellow = Light.Green
 case h_3
 ...
 heq✝³ : t % 3 = 0
+heq✝¹ : (t + 1) % 3 = 2
-⊢ Light.Red = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
+⊢ Light.Red = Light.Green → ¬Light.Green = Light.Green
+case h_4
+...
 heq✝³ : t % 3 = 1
+heq✝¹ : (t + 1) % 3 = 0
-⊢ Light.Yellow = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
+⊢ Light.Yellow = Light.Green → ¬Light.Red = Light.Green
+... and so on until ...
+case h_9
 heq✝³ : t % 3 = 2
+heq✝¹ : (t + 1) % 3 = 2
-⊢ Light.Green = Light.Green → ¬(match (t + 1) % 3, ⋯ with ...) Light.Green
+⊢ Light.Green = Light.Green → ¬Light.Green = Light.Green
```

`simp` will discharge away all the contradictory cases (where the antecedent is
`False`) or trivial cases (where the implication is `True -> True`), leaving
just one:

```diff-lean4
 example : neverBothGreen := by
   simp [neverBothGreen, junction, l1, l2]
   simp [LTL.always, LTL.not, LTL.atom]
   intro t
   simp [now, drop, FRP.map2, FRP.delay]
   simp [cycling]
-  split <;> split
+  split <;> split <;> simp

 1 goal
 case h_9
 heq✝³ : t % 3 = 2
 heq✝¹ : (t + 1) % 3 = 2
-⊢ Light.Green = Light.Green → ¬Light.Green = Light.Green
+⊢ False
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

```diff-lean4
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
+  lia
```

Even though this is a silly program, proving mutual exclusion is super
important for all sorts of programs, ranging from a simple spinlock, through to
a database's concurrency controller, up to distributed systems like
[Chubby](https://static.googleusercontent.com/media/research.google.com/en//archive/chubby-osdi06.pdf).
Knowing that you've got a provable safety property is critical for each of
these pieces of code!

## Next time

We don't really have a way for our reactive programs to, well, _react_ to anything
just yet.  Next time, we'll introduce the other fundamental FRP primitive, _events_,
that can modify the behaviour of `Signals` over time.  And, of course, we'll see
what the LTL <-> FRP correspondence is for that datatype too...

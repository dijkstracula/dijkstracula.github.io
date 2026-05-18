---
layout: post.njk
title: "FRP in Lean: Proof-transforming combinators and spreadsheets"
date: 2026-05-03
tags: [post, lean, reactive-programming, ltl, frp]
series: lean-ltl
series_title: "FRP: proof-transforming combinators"
inlineCodeLang: lean4
draft: true
---

Last time we designed a mechanism to accumulate stateful computation on
`Signal`s and `Event`s.  This design ended up looking a lot like a tiny version
of the step-based reactive systems we designed in part 1, so some of you may
have been wondering what the point of doing that is.  We'll answer that today:
in this post we'll see how we can _compose_ such proof-carrying computations
using the FRP combinators we already know and love.

Let's do some light refactoring.  At the moment, our `FRP` namespace is
polluted with both ordinary, non proof-checking combinators (like, `FRP.map`)
as well as ones that _do_ make statements about, say, safety properties (like
`FRP.accumulate`).  Let's create a sub-namespace to isolate the more
complicated proof-carrying ones.

```lean4
namespace FRP
...
namespace Refining

def accumulate
  {inv: StateProp β}
  (init : { s: β // inv s})
  (onNone: { s: β // inv s } → { s': β // inv s' })
  (onSome: α → { s: β // inv s} → {s': β // inv s'})
  (ev: Event α)
  : { sig : Signal β // (□ (LTL.atom inv)) sig } :=
  let switch (t: Time) : {s: β // inv s} → {s': β // inv s'} :=
    match ev t with
    | none => onNone
    | some a => onSome a

  let step_at : □ {s: β // inv s} := fun n => Nat.rec init (fun n s => switch (n + 1) s) n

  let vals : □ β := fun t => (step_at t).vals
  let safety : ∀ t, inv (vals t) := fun t => (step_at t).property

  ⟨ vals, (always_atom_iff vals).mp safety ⟩

end Refining

/- Our non-refining combinators can now be implemented in terms
   of the refining ones, just with trivial propositions -/
...

def accumulate
  (init : β) (onNone: β → β) (onSome: α → β → β) (ev: Event α)
    : Signal β := Refining.accumulate
   ⟨init, by trivial⟩
   (fun s => ⟨onNone s, by trivial⟩)
   (fun e s => ⟨onSome e s, by trivial⟩)
   ev

end FRP
```

Note that I'm using `always_atom_iff`, which I encouraged you to write in the
previous post.  If you haven't yet, no better time than the present!  This
theorem's type is `{inv : StateProp β} (sig : Signal β) : (∀ t, inv (sig t)) ↔
(□ (LTL.atom inv)) sig`; a biconditional, which we've discussed in previous
installments.

## Warmup: better notation for refined `Signal`s.

In the previous post, our program was littered with gnarly-looking `Signals`.
For instance, `accumulate`'s return type was:

```lean4
def accumulate
  ...
  : { sig : (Signal β) // (□ (LTL.atom inv)) sig }
```

This type refines `Signal β` with a safety property. A value of this type is
made up of two parts: A value of type `Signal β` and then the safety property
that the `Signal` has been proven to maintain. In our `Refining` namespace,
we could redefine it as such.

```lean4
namespace Refining 
...
abbrev RSignal (inv : StateProp α) :=
  { s : Signal α // (□ (LTL.atom inv)) s }
```

If we were free to make up notation for an `RSignal`, we might write something
like `(□ α) // inv`.  Structurally, it's what we said before: the whole `Signal`
is refined by the safety invariant `inv`.

What would it mean if we balanced the parentheses differently, say, `□ (α //
inv)`?  This "pushes ths invariant" inside each time step: rather than a pair
containing a `Signal α` and a global property, it's a `Signal` that, at each
time step, produces a pair containing a `α` and a _local_ proof of the
invariant for that time step.

Rather than using `RSignal` everywhere, let's construct some new notation:

::: margin-note
Why am I powerless in the presence of metaprogramming?  I blame my Scheme
upbringing.
:::
```lean4
notation      "□ "       α     " // " inv      => RSignal α inv
notation "( " "□ "       α ")" " // " inv      => RSignal α inv
notation      "□ " " ( " α "     // " inv " )" => Signal { s : α // inv s }
```

(Notice that `(□ β) // inv` is the same as `□ β // inv`, owing to operator
precedence, so I've written new syntax for both.  I'll endeavour to be explicit
when it's significant or otherwise appropriate to do so.)

Now, `accumulate` can return a `(□ β) // inv`, and inside the function, the
`step_at` helper can be typed as `□ (β // inv)`.

```lean4
def accumulate
  ...
  : (□ β) // inv := 
  ...
  let step_at : □ (β // inv) := fun n => Nat.rec init (fun n s => switch n s) n

  let vals : □ β := fun t => (step_at t).vals
  let safety : ∀ t, inv (vals t) := fun t => (step_at t).property

  ⟨ vals, (always_atom_iff vals).mp safety ⟩
```

## Splitting and collecting refined Signals

With this new notation, it's easier to see what `accumulate` is doing
internally: with `step_at`, we collate together all our refined values, across
all time steps, into a `□ (β // inv)`. Once we've got that, we turn all the
individual local proofs of `inv` holding into a global safety property,
producing a final refined signal of type `(□ β) // inv`.

As I worked on an earlier draft of this post, I found myself not only repeating
this operation, but also performing the _inverse_ operation, which takes a
single `(□ β) // inv` and "shards out" its safety property to produce a `□ (β
// inv)`.  This suggested to me that there was some sort of underlying
primitive that I'd missed in previous posts.

Indeed!  If we construct a way to go between `(□ β) // inv` and `□ (β //
inv)`s, we can simplify a lot of the FRP combinators we need.

Here's the skeleton of what we're after in this section:

::: margin-note
My original plan was to call these "fork" and "join", but if we keep this
series going long ehough, we might find a better use for those terms :-)
:::
```lean4
-- forks a signal with a global safety property into one where
-- the invariant is proved locally at each time step.
def Signal.split   : (□ β) // inv -> □ (β // inv) :=
  sorry -- TODO

-- collates a signal's local invariant proofs into a signal that
-- maintains the invariant as a global safety property.
def Signal.collect : □ (β // inv) -> (□ β) // inv :=
  sorry -- TODO
```

### `Signal.split` shards out a safety property into pointwise statements

The rough shape of `split` will be the following: at every time step, we
somehow produce a `β` and a proof that that `β` satisfies the invariant, and
then glue them together to make a refined value.

```lean4
def Signal.split (sig: (□ β) // inv) : □ (β // inv) :=
  fun t => -- TODO something like:
    let vals : β := sorry 
    let safety : inv s := sorry
    ⟨s, prf⟩
```

How can we construct an `s`?  It has to come out of `sig` somehow, since that's
the only way for us to produce `β`s.  Recalling that `sig.val` is a `□ β`,
getting a `β` just from applying `t` seems like as good an idea as any!

Similarly, `sig.property` is our safety property, ensuring `inv` will always
hold over `vals`: concretely, `∀ t, inv (vals t)`.  Remember the definition
of `LTL.always`:

```lean4
def always (p : Trace σ → Prop) (t : Trace σ) : Prop :=
  ∀ i, p (drop i t)
```

This is a proof that our LTL formula holds at every timestep.  The beauty of
the LTL-FRP correspondence is that by Curry-Howard, `(□ (LTL.atom inv)) vals`
is a _function_ we can call with some timestep `i`, to get a proof that `p`
holds at `t=i`.  This is exactly the same "interface" as a `Signal`!

```diff-lean4
 def Signal.split (sig: (□ β) // inv) : □ (β // inv) :=
+  let vals : □ β := sig.val
+  let safety : ∀ t, inv (vals t) := sig.property
   fun t => -- TODO something like:
-    let vals : β := sorry 
-    let safety : inv s := sorry
-    ⟨s, prf⟩
+    ...
+    ⟨sorry, sorry⟩
```


Hopefully it's not too hard to see that `vals t` produces the `β` that we need,
so we know what we need to do there. `safety t` _almost_ produces the proof
that we need: it gives us a `LTL.atom inv (drop t vals)`, the global safety
property, but what we in fact need is the pointwise proof at time `t`.
Luckily, that's what `always_atom_iff` gives us! `fun t => (always_atom_iff
vals).mpr sig.property t` first converts the safety property into its pointwise
form, and then applies `t` to it.  (If you're feeling fancy you can write this
as a point-free function composition as I've done below).

So, our final `split` is:

```diff-lean4
 def Signal.split (sig: (□ β) // inv) : □ (β // inv) :=
   let vals : □ β := sig.val
-  let safety : ∀ t, inv (vals t) := sig.property
-  fun t => 
-    ...
-    ⟨sorry, sorry⟩
+  let safety : (∀ t, inv (vals t)) := (always_atom_iff vals).mpr $ sig.property
+  fun t => ⟨ vals t, safety t ⟩
```

### `Signal.collect` compiles a `Signal` with a safety property

Let's write the operation that does the opposite: given a `Signal` where a safety
proof is paired with its value at every time step, collect that infinite
sequence of proofs into a safety propery.

```lean4
def Signal.collect (sig: □ (β // inv)) : (□ β) // inv := 
  let vals : □ β := sorry 
  let safety : (□ (LTL.atom inv)) vals := sorry 
  ⟨s, safety⟩
```

(Note that a nice contrast between `split` and `collect` is that `split` needed
to return a top-level `Signal` and thus the returned expression was a `fun t =>
...`, whereas the refinement is the top-level construct for `collect.)

We'll proceed in the same way as before: we'll extract a `□ β` and a `∀ t, inv
(vals t)` from the input signature.  We'll apply `always_atom_iff`, in the
left-to-right direction this time to transform the latter from a quantified
statement to an LTL proposition.

```diff-lean4
-def Signal.collect (sig: □ (β // inv)) : (□ β) // inv := 
-  let vals : □ β := sorry 
-  let safety : (□ (LTL.atom inv)) vals := sorry 
-  ⟨s, safety⟩
+def Signal.collect (sig : □ (β // inv)) : (□ β) // inv :=
+  let vals : □ β := 
+    fun t => (sig t).val
+  let safety : (□ (LTL.atom inv)) vals := 
+    (always_atom_iff vals).mp (fun t => (sig t).property)
+  ⟨ vals, safety ⟩
```

Notice that `accumulate` can be nicely simplified with `collect`; we construct
the pointwise `Signal` using the recursor for `Nat`, and then glue it all
together with `collect`.

```lean4
def accumulate
  ...
  : (□ β) // inv :=
  let switch (t: Time) : {s: β // inv s} → {s': β // inv s'} :=
    match ev t with
    | none => onNone
    | some a => onSome a

  let step_at : □ (β // inv) := fun n => Nat.rec
    init
    (fun n s => switch n s) n

  Signal.collect step_at
```

## Refined combinators with assume-guarantee reasoning

Now that we have a syntactic separation between non-refined and refined
FRP combinators, let's port some of the `FRP` combinators to their refined
counterparts.

### `const` is a collection

Let's warm up by porting `FRP.const` into the refined world.  Here's the
original implementation:

```lean4
def Signal.const (v: α) : □ α := fun _ => v
```

Pretty simple: at all time steps `t`, produce that constant value.  By
contrast, `RSignal.const` will consume a single value paired with a
refinement - a `{ a : α // inv a }` - and produce a `□ α // inv`.

Here's our function signature with that in mind:  It'll now take an implicit
`inv : StateProp α`, and the `a` value is now a refinement type that makes use
of our `inv`.

```
def RSignal.const {inv: StateProp α} (a : { a : α // inv a } ) : □ α // inv :=
  -- TODO
```

The _wrong_ thing to do is to simply produce the constant `Signal` `(fun _ =>
a)` like before.  Reason is: that's a _pointwise refinement_: it produces
`<val, proof>`  pairs at every `t`, whereas what we want is a single, global
`<val, proof>` pair.

Luckily, though, we just wrote a combinator to turn one into the other!
`Signal.collect` really does all the heavy lifting here.

```diff-lean4
 def RSignal.const {inv: StateProp α} (a : { a : α // inv a } ) : □ α // inv :=
-  -- TODO
+  let sig : □ (α // inv) := (fun _ => a)
+  Signal.collect sig
```

### `map` splits, then collects

Okay, let's do `Signal.map` next.  Here's the original signature.

```lean4
def RSignal.map (f: α → β) (s : □ α) : □ β := fun t => f (s t)
```

As with `const`, we'll begin by introducing two invariants over `α` and `β`:

```lean4
def RSignal.map
  {inv_a: StateProp α} {inv_b: StateProp β}
  (f: α → β) (s : □ α) 
  : □ β := ...
```

And like before, `inv_a` becomes the safety property for the input `Signal`, as
well as a refinement on the argument to `f`; `inv_b` becomes the refinement on
the _return value_ of `f`, and thus the safety property of the `Signal` that we
return!

OK, so in summary, our signature looks like this:

```diff-lean4
 def RSignal.map
   {inv_a: StateProp α} {inv_b: StateProp β}
-  (f: α → β) (s : □ α) 
-  : □ β := ...
+  (f: {a: α // inv_a a} → {b : β // inv_b b}) (s: □ α // inv_a) 
+  : (□ β) // inv_b := ...
```

Let's write the body of `map`.  Roughly, our goal is going to be: "decompose
the input `Signal` into its piecewise parts, apply the function on each part,
and recombine into a new refined `Signal`.

`Signal.split s` gives us a `□ (α // inv_a)`, which `f` can be applied to at
every timestep.  `fun t => f (Signal.split s t)` gives us a `□ (β // inv_b)`,
and then `Signal.combine` stitches the pointwise invariants back into a
safety property.  So, we're left with functionally a one-liner:

```diff-lean4
 def RSignal.map
   {inv_a: StateProp α} {inv_b: StateProp β}
   (f: {a: α // inv_a a} → {b : β // inv_b b}) (s: □ α // inv_a) 
-  : (□ β) // inv_b := ...
+  : (□ β) // inv_b :=
+  Signal.collect (fun t => f (Signal.split s t))
```

::: warning
Annoyingly, only when writing this implementation did I realise that Lean's
`Functor` implementation is, depending on how you look at it, too demanding or
not demanding enough, to accept `RSignal.map`.  The whole point of a functor is
that it provides a way to map between _any two_ types (which you can see in the
[typeclass
definition](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Functor)) - in `(α → β) → F α → F β`, `α` and `β` can be _any_ type.
The problem here is that our definition of `RSignal.map` constrains us
specifically to _refined types_, so Lean rejects it as being insufficiently
general for `Functor`'s purposes.
:::

`RSignal.map2` is not fundamentally different, either.

::: margin-warning
If `RSignal.map` does not get us to a `Functor`, then `RSignal.map2`
_extremely_ does not get us to an `Applicative`.  For `Applicative`, `pure : α
→ F α` has to produce a refined value out of nothing but an `α`, there's no
`inv_a` lying around to use as the proof term, and a `StateProp` is too rich of
a dependent type to be inferred from context by Lean.  Alas!

You should email me if you have thoughts on how to make this better.
:::
```lean4
def map2
  {inv_a: StateProp α} {inv_b: StateProp β} {inv_c: StateProp γ}
  (f: {a: α // inv_a a} → {b : β // inv_b b} → {c : γ // inv_c c})
  (s1: □ α // inv_a) 
  (s2: □ β // inv_b)
  : □ γ // inv_c :=
  (fun t => f (Signal.split s1 t) (Signal.split s2 t)) |> Signal.collect
```

## Connecting refined `Signals` is composing invariants

## tA reactive spreadsheet

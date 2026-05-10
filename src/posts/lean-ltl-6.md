---
layout: post.njk
title: "Reactive Programming in Lean Part 6: Incremental computation, accumulation, and spreadsheets"
date: 2026-05-03
tags: [post, lean, reactive-programming, ltl, frp]
series: lean-ltl
series_title: "Part six: incremental spreadsheets"
inlineCodeLang: lean4
---

Last time we designed a mechanism to accumulate stateful computation on
`Signal`s and `Event`s.  This design ended up looking a lot like a tiny version
of the step-based reactive systems we designed in part 1, so some of you may
have been wondering what the point of doing that is.  We'll answer that today:
in this post we'll see how we can _compose_ such locally-stateful computations
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
  {inv: β → Prop}
  (init : { s: β // inv s})
  (onNone: { s: β // inv s } → { s': β // inv s' })
  (onSome: α → { s: β // inv s} → {s': β // inv s'})
  (ev: Event α)
  : { sig : Signal β // (□ (LTL.atom inv)) sig } :=
  let switch (t: Time) : {s: β // inv s} → {s': β // inv s'} :=
    match ev t with
    | none => onNone
    | some a => onSome a

  let step_at : Signal {s: β // inv s} := fun n => Nat.rec
    init
    (fun n s => switch (n + 1) s) n

  let vals : Signal β := fun t => (step_at t).1
  let prfs : ∀ t, inv (vals t) := fun t => (step_at t).2

  ⟨ vals, (always_atom_iff vals).mp prfs ⟩

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
previous post.  If you haven't yet, no better time than the present!  

This theorem's type is `{inv : β → Prop} (sig : Signal β) : (∀ t, inv (sig t))
↔ (□ (LTL.atom inv)) sig`, which is a _biconditional_, not just an ordinary
implication.  The proof term has two fields, depending on which way you want
the proof to go: when you want the left-to-right implication, extract it with
`.mp` (for modus ponens); for the right-to-left, use `.mpr`.

## Warmup: better notation for refined `Signal`s.

In the previous post, our program was littered with gnarly-looking `Signals`.
For instance, `accumulate`'s return type was:

```lean4
def accuulate
  ...
  : { sig : (Signal β) // (□ (LTL.atom inv)) sig }
```

A value of this type is made up of two parts: A value of type `FRP.Signal β`
and then the safety property that the `Signal` has been proven to maintain.
In our `Refining` namespace, let's redefine it as such, and give a nicer
notation for it:

```lean4
namespace Refining 
...
abbrev Signal (α : Type) (inv : α → Prop := fun _ => True) :=
  { s : FRP.Signal α // (□ (LTL.atom inv)) s }

notation "□ " α " // " inv => Signal α inv

def accumulate
  ...
  : □ β // inv := ...
```

I think overloading `//` in the context of a refinement type `Signal` is kind
of cute. Now, `accumulate` can be implemented with a cleaner type signature
where we don't have to worry about all the refinement type boilerplate.  From
now on, we'll read `□ β // inv` to mean "a time-varying `β`, where `inv` always
holds", and, with the help of the `always_atom_iff` bridging theorem, we can
interpret `inv` as being true for values at all time steps. 

## Splitting and collecting refined Signals

TODO

## `FRP.map` with assume-guarantee reasoning

Now that we have a syntactic separation between non-refined and refined
FRP combinators, let's port `FRP.map` from the former to the latter.
Here's the original implementation:

```lean4
def map (f: α → β) (s : □ α) : □ β :=
  fun t => f (s t)
```

We'll begin by introducing two invariants over `α` and `β`:

```lean4
def map
  {inv_a: α → Prop}
  {inv_b: β → Prop}
  (f: α → β) (s : □ α) : □ β := ...
```

Where does it make sense for `inv_a` and `inv_b` to be used?  Certainly, in the
places where `α` and `β` are.  `inv_a` becomes the safety property for the 
input `Signal`, as well as a refinement on the argument to `f`; `inv_b` becomes
the refinement on the _return value_ of `f`, and thus the safety property of
the `Signal` that we return!

OK, so our signature looks like this:

```lean4
def map
  {inv_a: α → Prop}
  {inv_b: β → Prop}
  (f: {a: α // inv_a a} → {b : β // inv_b b})
  (s: □ α // inv_a) : □ β // inv_b := ...
```

And since we're returning a refined `Signal`, the shape of the return
expression needs to be that tuple, comprised of the `Signal β` and its
universally-quantified safety property.  This takes the same shape as the
returned expression in `accumulate`.

```lean4
def map ... :=
  ⟨ fun t => ... , by ... ⟩
```

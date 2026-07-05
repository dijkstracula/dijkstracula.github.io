---
layout: post.njk
title: "FRP in Lean: Composing invariant-transforming combinators"
date: 2026-06-10
tags: [post, lean, reactive-programming, ltl, frp]
series: lean-ltl
series_title: "FRP: Composing verified Signals"
inlineCodeLang: lean4
excerpt: "How do our proofs change as we execute an FRP program?"
---

::: margin-note
Sorry that it's been awhile since my last post!  Big life stuff happening
over here!
:::
Last time we designed a mechanism to accumulate stateful computation on
Signals and Events.  This design ended up looking a lot like a tiny version
of the step-based reactive systems we designed in part 1, so some of you may
have been wondering what the point of doing that is.  We'll answer that today:
in this post we'll see how we can _compose_ such proof-carrying computations
using the FRP combinators we already know and love.  

Before we do that, though, let's do some light refactoring.  At the moment, our
`FRP` namespace is polluted with both ordinary, non proof-checking combinators
(like, `FRP.map`) as well as ones that _do_ make statements about, say, safety
properties (like `FRP.accumulate`, which was the meat of the previous post
in this series).  Let's create a sub-namespace to isolate the more complicated
proof-carrying ones.

::: tip
```lean4
namespace FRP
...
def Refining.accumulate
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

  -- `switch t` produces the next state, depending on whether the event
  -- fired at the given timestep
  let switch (t: Time) : {s: β // inv s} → {s': β // inv s'} :=
    match ev t with
    | none => onNone
    | some a => onSome a

  -- `step_at` takes `t` steps through `switch`; at each time step, it
  -- produces a β alongside its proof of .preserving `inv`
  let step_at : □ {s: β // inv s} := 
    fun t => Nat.rec init (fun n s => switch (t + 1) s) t
 
  -- Reorganize the signal of refined values into a refined signal.
  let vals : □ β := fun t => (step_at t).val
  let safety : ∀ t, inv (vals t) := fun t => (step_at t).property
  ⟨ vals, (always_atom_iff vals).mp safety ⟩

/- Our non-refining combinators can now be implemented in terms
   of the refining ones, just with trivial proofs of `fun t => True` 
 -/

def accumulate
  (init : β) (onNone: β → β) (onSome: α → β → β) (ev: Event α)
    : Signal β := Refining.accumulate
    ⟨init, by trivial⟩
    (fun s => ⟨onNone s, by trivial⟩)
    (fun e s => ⟨onSome e s, by trivial⟩)
    ev

end FRP
```
:::

Note that I'm using `always_atom_iff`, which I encouraged you to write in the
previous post.  If you haven't yet, no better time than the present!  This
theorem's type is `(sig : Signal β) : (∀ t, inv (sig t)) ↔
(□ (LTL.atom inv)) sig`; a biconditional that states "making a statement about
a Signal at every time step is interchangeable with making the equivalent
statement in temporal logic".

## Warmup: better notation for refined Signals.

In the previous post, we introduced using Lean's refinement type system,
and used them to make statements about properties of Signals.  Last time,
we said, strictly informally:

1. "`(Signal β) // inv`" is saying "here's a Signal that produces `β`s, and a
proof of a safety property `inv`; we might call this "a refined Signal";
2. "`Signal (β // inv)`" is saying "here's a Signal that produces `(β // inv)`s;
that is to say, at every time step, we get a value and a proof of some property
about that time step's value.  We might call this "a Signal of refinements".

Syntactically, though, it was a bit of a mess. Our program was littered with
gnarly-looking Signal types.  For instance, `accumulate`'s return type was:

```lean4
def accumulate
  ...
  : { sig : (□ β) // (□ (LTL.atom inv)) sig }
```

(This type refines a `Signal β` with an LTL safety property, so it's an example
of the first type of refined signal.)  Let's create a type alias for this
refined signal to make this a bit less convoluted-looking.

```diff-lean4
+ abbrev RSignal (α : Type) (inv : StateProp α) := { s : Signal α // (□ (LTL.atom inv)) s }

 def accumulate
   ...
-  : { sig : (□ β) // (□ (LTL.atom inv)) sig }
+  : RSignal β inv
```

This is already cleaner, but we've lost the `//` operator and thus the connection
to refinement types.  That's where Lean's macro system can once again help us out.

### A syntax transformer for `RSignal`s

One of the things I really like about Lean is that we are free to make up
notation!  When we introduced the LTL <-> FRP correspondence, we used the
`notation` special form to imbue `□` with meaning.  We _also_ saw that Lean's
macro system is richer than, say, C's, since it was smart enough to choose the
right `□` syntax depending on whether the type context was in LTL-land or
FRP-land.

Here's how we might write a syntax transformer for refined signals and signals
of refinements using that `notation` directive:

::: margin-note
Truly, why am I powerless in the presence of metaprogramming?  I blame my
Scheme upbringing.
:::
```diff-lean4
 notation:max  "□ "       α:max                       => Signal α
+notation      "□ " " ( " α:51     " // " inv:51 " )" => Signal { s : α // inv s }
+notation      "□ "       α:51     " // " inv:51      => RSignal α inv
+notation "( " "□ "       α:51 ")" " // " inv:51      => RSignal α inv

 def accumulate
   ...
-  : RSignal β inv := ...
+  : □ β // inv := ...
```

In addition to `accumulate` returning a `(□ β) // inv`, inside the body of that
function, the `step_at` helper can be typed as `□ (β // inv)`.

```diff-lean4
 def accumulate
  ...
  : (□ β) // inv := 
  ...
- let step_at : □ {s: β // inv s} := 
+ let step_at : □ (β // inv) := 
    fun t => Nat.rec init (fun n s => switch (t + 1) s) t

  let vals : □ β := fun t => (step_at t).vals
  let safety : ∀ t, inv (vals t) := fun t => (step_at t).property

  ⟨ vals, (always_atom_iff vals).mp safety ⟩
```

When I made this transformation, it hinted at something deeper that I'd missed
before: seems like if we agree that the syntax of `(□ β) // inv` is close to
that of `□ (β // inv)`, then perhaps we could agree that the _semantics_ of the
two are related, too.

### Metaprogramming our way to a better syntax

Before we do that, though, let's tidy up our syntax transformation. 

::: note
If you're _truly_ uninterested in the finer points of hygenic macros, I wouldn't
fault you for skipping to the next section in this post.
:::

If the above note didn't dissuade you: hello, fellow metaprogramming enjoyer!
Okay, in Lean, the `notation` form auto-generates three things for us: 

1) A `syntax` directive that, essentially, adds a new kind of AST node
to Lean's parser;
2) A `@[macro]` directive that specifies the _semantics_ of what expanding
this new piece of syntax should mean;
3) An unexpander to pretty-print the syntax, for error reporting and such.

Notice that `(□ β) // inv` is the same as `□ β // inv`, owing to operator
precedence, so I've written new syntax for both.  I'll endeavour to be explicit
when it's significant or otherwise appropriate to do so, since we'll see some
combinators where it's really worth seeing `(□ β) // inv` versus `□ (β // inv)`
on the page.

In yacc or bison or another traditional parser generator, we might express this
like so:

```bison
  /* All four productions live in the `term` non-terminal */
  term
    : '□' a                    { Signal a }         /* standalone */
    | '□' '(' a '//' inv ')'   { Signal { x : a /​/ inv x } }  /* pointwise */
    | '□' a '//' inv           { RSignal a inv }    /* refined */
    | '(' '□' a ')' '//' inv   { RSignal a inv }    /* parens-refined */
    | ... ;
```

This expresses both the syntax and semantics of our notation.  Since a
traditional parser operates at compile-time, we typically wouldn't expect the
parser generator to give us an unexpander.

This notation ... kind of works, but it's kind of brittle.  The problem is that
we've actually introduced an ambiguity in our syntax.  If you're familiar with
shift/reduce errors in classical parsing, it's not totally dissimilar: Both `□
X` and `□ X // inv` share a common prefix; when Lean parses `□ X`, should it
commit to a `Signal X` right away, or should we keep lexing in case it should
actually expand to an `RSignal` with an invariant?

What we'd prefer to have instead is a new non-terminal: 

```bison
  sig : '□' term ;              /* an unambiguous production for □ */
```

And then express our grammar in terms of that new "kind of AST":

```bison
  term
    : sig                   { Signal α }
    | "□" "(" a "//" p ")"  { Signal { x : α /​/ p x } }
    | sig "//" inv          { RSignal α inv }
    | "(" sig ")" "//" inv  { RSignal α inv }
    | ... ;

```

We'll tell Lean's parser about our new non-terminal with
[`declare_syntax_cat`](https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html),
instruct it to treat it as "a kind of term", and then specify all the different
syntactic forms that a signal AST can take.

```lean4
declare_syntax_cat signalTree
syntax (name := signalRaw) "□ " term:max : signalTree
syntax (name := signalLift) signalTree : term

syntax (name := pointwiseRefined) "□ " "(" term:51        " // " term    ")" : term
syntax (name := refinedSig)                signalTree     " // " term:51     : term
syntax (name := outerRefinedSig)       "(" signalTree ")" " // " term        : term
```

We gave each piece of syntax a name, so we can refer to them in their
respective `macro` directives.  Each of those are straightforward to
implement once you look up the syntax for Lean's syntax transformers:

```lean4
macro_rules (kind := signalLift)
  | `(□ $α) => `(Signal $α)

macro_rules (kind := refinedSig)
  | `(□ $α // $inv) => `(RSignal $α $inv)

macro_rules (kind := outerRefinedSig)
  | `((□ $α) // $inv) => `(RSignal $α $inv)

macro_rules (kind := pointwiseRefined)
  | `(□ ($α // $inv)) => `(Signal { x : $α // $inv x })
```

We can now use our syntax in place of Signal and `RSignal` in the way
we would expect!

::: tip
```lean4
#check  □ Int  // (· > 0)   -- RSignal Int fun x => x > 0 : Type
#check (□ Int) // (· > 0)   -- RSignal Int fun x => x > 0 : Type
#check  □ (Int // (· > 0))  -- Signal { x // (fun x => x > 0) x } : Type
```
:::

## Splitting and collecting refined Signals

With this new notation, it's easier to see what `accumulate` is doing
internally: with `step_at`, we collate together all our refined values, across
all time steps, into a `□ (β // inv)`.  (That's a "signal of refinements").
Once we've got that, we turn all the individual local proofs of `inv` holding
into a global safety property, producing a final refined signal of type `(□ β)
// inv` (a refined signal).

As I worked on an earlier draft of this post, I found myself not only repeating
this operation, but also performing the _inverse_ operation, which takes a
single `(□ β) // inv` and "shards out" its safety property to produce a `□ (β
// inv)`.  This suggested to me that there was some sort of underlying
primitive that I'd missed in previous posts.

Indeed!  It turns out that if we construct a way to go between `(□ β) // inv`
and `□ (β // inv)`s, we can simplify a lot of the FRP combinators we need.

Here's the skeleton of what we're after in this section:

::: margin-note
My original plan was to call these "fork" and "join", but if we keep this
series going long enough, we might find a better use for those terms :-)
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

The rough shape of `split` will be the following: We consume a refined
Signal, and produce a new Signal such that at every time step, we somehow
produce a `β` and a proof that that `β` satisfies the invariant, and then glue
them together to make a "signal of refinements".

```diff-lean4
  def Signal.split (sig: (□ β) // inv) : □ (β // inv) :=
-    sorry -- TODO
+    fun t => ⟨...val, prf⟩ -- TODO: something roughly like:
```

How can we construct a `val`?  It has to come out of `sig` somehow, since that's
the only way for us to produce `β`s.  Recalling that `sig.val` is a `□ β`,
getting a `β` just from applying `t` seems like as good an idea as any!

```diff-lean4
  def Signal.split (sig: (□ β) // inv) : □ (β // inv) :=
+    let vals : □ β := sig.val
-    fun t => ⟨...val, prf⟩ -- TODO: something roughly like:
+    fun t => ⟨vals t, prf⟩ -- TODO: something roughly like:
```

Similarly, `sig.property` is our safety property, ensuring `inv` will always
hold over `vals`.  This is a proof that our LTL formula holds at every
timestep.  

The beauty of the LTL-FRP correspondence is that by Curry-Howard, a proof of
`(□ (LTL.atom inv)) vals` is a _function_ we can call with some timestep `i`,
to get a proof that `p` holds at `t=i`!  So, the body of `always` is identical
to `fun i => p (drop i t)`. This means `sig.property` can be applied:
`sig.property i` gives us a proof that the invariant holds at time `i`.

```diff-lean4
 def Signal.split (sig: (□ β) // inv) : □ (β // inv) :=
   let vals : □ β := sig.val
+  let safety : (□ (LTL.atom inv)) := sig.property
-  fun t => ⟨vals t, prf⟩ -- TODO something like:
+  fun t => ⟨vals t, safety t⟩
```

Bad news, though, it doesn't work!

::: warning
```lean4
Type mismatch
  sig.property
has type
  □ (LTL.atom inv) sig.val
but is expected to have type
  ∀ (t : Time), inv (vals t)
```
:::


Argh, but feels like we're close.  `safety t` _almost_ produces the proof that
we need: it gives us a `LTL.atom inv (drop t vals)`, the global safety
property, but what we in fact need is the pointwise proof at time `t`. Luckily,
that's what `always_atom_iff` gives us! `fun t => (always_atom_iff vals).mpr
sig.property t` first converts the safety property into its pointwise form, and
then applies `t` to it.  (If you're feeling fancy you can write this as a
point-free function composition as I've done below).

So, our final `split` is:

::: tip
```diff-lean4
 def Signal.split (sig: (□ β) // inv) : □ (β // inv) :=
   let vals : □ β := sig.val
-  let safety : (□ (LTL.atom inv))  := sig.property
+  let safety : (∀ t, inv (vals t)) := (always_atom_iff vals).mpr sig.property
   fun t => ⟨ vals t, safety t ⟩
```
:::

### `Signal.collect` compiles a Signal with a safety property

Let's write the operation that does the opposite: given a Signal of
refinements, collect that infinite sequence of proofs into a refined Signal.

```lean4
def Signal.collect (sig: □ (β // inv)) : (□ β) // inv := 
  let vals : □ β := sorry 
  let safety : (□ (LTL.atom inv)) vals := sorry 
  ⟨vals, safety⟩
```

(Note the asymmetry between `split` and `collect`'s bodies: `split` needed to
return a top-level Signal and thus the returned expression was a `fun t =>
...`, whereas the refinement pair is the top-level construct for `collect`.)

We'll proceed in the same way as before: we'll extract a `□ β` and a `∀ t, inv
(vals t)` from the input signature.  We'll apply `always_atom_iff`, in the
left-to-right direction this time to transform the latter from a quantified
statement to an LTL proposition.

::: tip
```diff-lean4
 def Signal.collect (sig: □ (β // inv)) : (□ β) // inv := 
-  let vals : □ β := sorry 
-  let safety : (□ (LTL.atom inv)) vals := sorry 
+  let vals : □ β := fun t => (sig t).val
+  let safety : (□ (LTL.atom inv)) vals := 
+    (always_atom_iff vals).mp (fun t => (sig t).property)
   ⟨ vals, safety ⟩
```
:::

Notice that `accumulate` can be nicely simplified with `collect`; we construct
the pointwise Signal using the recursor for `Nat`, and then glue it all
together with `collect`.

```diff-lean4
def accumulate
   ...

-  let vals : □ β := fun t => (step_at t).val
-  let safety : ∀ t, inv (vals t) := fun t => (step_at t).property
-
- ⟨ vals, (always_atom_iff vals).mp safety ⟩
-
+  Signal.collect step_at
```

## Lifting unrefined functions into refined Signals

The Signal boundary can also be where proofs about ordinary, non-verified
functions can reside. Here's a silly, and probably wildly-bad, pseudo-random
number generator.  You might implement this function in any programming
language: it's just a function from `Int`s to `Int`s, no proofs, no dependent
types, utterly pedestrian ;-)

```lean4
def lcg (x : Int) : Int := (5 * x + 17) % 256
```

If you remember our first combinator, `scan`, we can lift this into an old
school, unrefined Signal if we also supply it a starting seed value:

::: margin-note
I notice that in this case we always flip-flop between even and odd numbers,
suggesting that we should probably not use this for cryptographic purposes
anytime soon.
:::
```lean4
def prng : Signal Int := FRP.scan lcg 97
#eval List.range 10 |>.map prng -- [97, 246, 223, 108, 45, 242, 203, 8, 57, 46]
```

Hopefully you will not push back too hard on me if I asserted that every
random number will be nonnegative but not to exceed 256.  We could formalise
this by lifting `prng` into a signal-of-refinements!

```diff-lean4
+ abbrev unsignedMax (K : Int) : StateProp Int := fun x => 0 ≤ x ∧ x < K

- def prng : Signal Int := FRP.scan lcg 97
+ def prng : □ (Int // unsignedMax 256) := 
+   FRP.scan (fun ⟨x, hx⟩ => ⟨lcg x, by sorry⟩) 
+            ⟨97, by sorry⟩
```

Might be worth making sure you understand all our `sorry` placeholders before
proceeding: `FRP.scan` now consumes and produces a refined pair of type `Int //
unsignedMax 256` in its first argument, and needs to consume an initial such
pair in its second argument.

Filling out the initial argument isn't that hard: we'll give it our seed value,
and `trivial` is enough to prove that `0 <= 97 < 256` right out the gate.

```diff-lean4
  def prng : Signal Int := FRP.scan lcg 97
  def prng : □ (Int // unsignedMax 256) := 
    FRP.scan (fun ⟨x, hx⟩ => ⟨lcg x, by sorry⟩) 
-            ⟨97, by sorry⟩
+            ⟨97, by trivial⟩
```

The proof that `lcg x` is within bounds is pretty easy to solve, too: we
just have to unfold the definitions of `unsignedMax` and `lcg` to get at
the raw `0 ≤ (5 * x + 17) % 256 ∧ (5 * x + 17) % 256 < 256` goal, and then
`lia` kills it for us.

```diff-lean4
  def prng : Signal Int := FRP.scan lcg 97
  def prng : □ (Int // unsignedMax 256) := 
-   FRP.scan (fun ⟨x, hx⟩ => ⟨lcg x, by sorry⟩) 
+   FRP.scan (fun ⟨x, hx⟩ => ⟨lcg x, by simp [unsignedMax, lcg]; lia ⟩) 
             ⟨97, by trivial⟩
```

And of course we know how to turn this into a refined signal!  Just pipe
the whole thing into `Signal.collect`

```diff-lean4
- def prng : □ (Int // unsignedMax 256) := 
+ def prng : □ Int // unsignedMax 256 := 
    FRP.scan (fun ⟨x, hx⟩ => ⟨lcg x, by sorry⟩) 
    FRP.scan (fun ⟨x, hx⟩ => ⟨lcg x, by simp [unsignedMax, lcg]; lia ⟩) 
             ⟨97, by trivial⟩
+   |> Signal.collect
```

This is great, we have a nice tight safety property for `prng`; we're also free
to change the implementation of `lcg` to have different constant values, and so
long as we never introduce the possibility of generating larger values, `prng`
will still typecheck.

## Refined versions of FRP combinators

Now that we have a syntactic separation between non-refined and refined FRP
combinators, and a bit of experience splitting and collecting `RSignal`s, let's
port some of the `FRP` combinators to their refined counterparts.

### `const` is a collection

Let's warm up by porting `FRP.const` into the refined world.  Here's the
original implementation:

```lean4
def Signal.const (v: α) : □ α := fun _ => v
```

Pretty simple: at all time steps `t`, produce that constant value.  By
contrast, `RSignal.const` will consume a single value paired with a
refinement - a `{ a : α // inv a }` - and produce a `□ α // inv`.

Here's our function signature with that in mind:  It'll now take a _refined
value_, and produce a _refined signal_ with the same property.

```lean4
def RSignal.const (a : { a : α // inv a } ) : □ α // inv :=
  -- TODO
```

The _wrong_ thing to do is to simply produce the constant Signal `(fun _ =>
a)` like before.  Reason is: that's a _pointwise refinement_: it produces
`<val, proof>`  pairs at every `t`, whereas what we want is a single, global
`<val, proof>` pair.

Luckily, though, we just wrote a combinator to turn one into the other!
`Signal.collect` really does all the heavy lifting here.

```diff-lean4
 def RSignal.const {inv: StateProp α} (a : { a : α // inv a } ) : □ α // inv :=
-  -- TODO
+  Signal.collect (fun _ => a)
```

### Choosing good invariants for a `RSignal.const`

Here's how we use `RSignal.const` in practice: suppose I have a constant hex
value I want to lift into a refined Signal.  What's the type of `RSignal.const
⟨0xFFFF, by lia⟩`?

::: margin-note
I'll tell you later why I decided to call this `ss`.
:::
```lean4
def ss : □ Int // sorry /- TODO? -/ := RSignal.const ⟨0xFFFF, by lia⟩
```

Really, the invariant can be anything that `lia` is able to prove for us,
because we let `inv` be an implicit parameter to the function itself, and
that proposition needs to be discharged by `lia`.  

The least interesting `inv` is the `StateProp` that says nothing at all: "no
matter what the state value is, produce the proposition `True`".  This is the
_weakest_ of all `StateProp`s.  It's a bit like just using the unrefined `FRP.const`
combinator; it's also a bit like, in OOP, assigning some object to a variable
of type `Object`, in that all information about the type is thrown out.

```diff-lean4
- def ss : □ Int // sorry /- TODO? -/     := RSignal.const ⟨0xFFFF, by lia⟩
+ def ss : □ Int // Function.const _ True := RSignal.const ⟨0xFFFF, by lia⟩
```

::: margin-note
There's a nice parallel with stats here.  Just like how `Fun.const True` admits
all values, the uniform distribution over all values, assigns equal weights to
all hypotheses is the least useful prior.  By contrast, `x = 0xFFFF` admitting
exactly one value is like a Dirac function putting all its mass on a single
outcome.
:::
Two more interesting invariants: we could also assert the fact that the value
always is the constant we gave it.  This is the _strongest_ of all `StateProp`s
that we could reasonably expect `lia` to prove for us; whereas `Function.const
_ True` "admits everything", this invariant admits one fact, that the constant
value never deviates.

```diff-lean4
- def ss : □ Int // Function.const _ True := RSignal.const ⟨0xFFFF, by lia⟩
+ def ss : □ Int // fun i => i = 0xFFFF   := RSignal.const ⟨0xFFFF, by lia⟩
```

Here's one that I'm actually going to use later on in this post: it's
definitely the case that `0 <= i < 0xFFFF`, so we could assert that this value
would always fit into a 16-bit hardware register.

```diff-lean4
+ abbrev signedHalf (B : Int) : StateProp Int := fun x => -B ≤ x ∧ x < B
+ abbrev unsignedMax (M : Int) : StateProp Int := fun x => 0 ≤ x ∧ x < M

- def ss : □ Int // fun i => i = 0xFFFF := RSignal.const ⟨0xFFFF, by lia⟩
+ def ss : □ Int // unsignedMax (2^16)  := RSignal.const ⟨0xFFFF, by lia⟩
```

Wouldn't it be great if Lean could infer which invariant is most useful for us
given the context in which we use it?  Sadly, this goes back to the fact that
dependent type inference is undecidable.  But, having to think about what
the right invariant is isn't really the end of the world.

### `map` splits, applies, then collects

::: margin-warning
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
Okay, let's do `Signal.map` next.  Here's the original signature.

```lean4
def Signal.map (f: α → β) (s : □ α) : □ β := fun t => f (s t)
```

We'll now have _two_ invariants: a _precondition_ that must hold for the input
type, and a _postcondition_, that does the same for the output type.  `pre` and
`post` will appear not just in the input and output Signals but in the
mapping function: `f` will _assume_ that `pre` holds, and under that
hypothesis, guarantee that `post` will hold.

OK, so in summary, our signature looks like this:

```diff-lean4
 def RSignal.map
+  {pre: StateProp α}
+  {post: StateProp β}
-  (f: α → β) 
-  (s : □ α) 
-  : □ β := ...
+  (f: {a: α // pre a} → {b : β // post b}) 
+  (s: □ α // pre) 
+  :   □ β // post := 
   ...
```

Let's write the body of `map`.  Roughly, our goal is going to be: "decompose
the input Signal into its piecewise parts, apply the function on each part,
and recombine into a new refined Signal.

`Signal.split s` gives us a `□ (α // inv_a)`, which `f` can be applied to at
every timestep.  `fun t => f (Signal.split s t)` gives us a `□ (β // inv_b)`,
and then `Signal.combine` stitches the pointwise invariants back into a
safety property.  So, we're left with functionally a one-liner:

```diff-lean4
 def RSignal.map
   {pre: α → Prop}
   {post: β → Prop}
   (f: {a: α // pre a} → {b : β // post b})
   (s: □ α // pre)
   : □ β // post :=
+  Signal.collect (fun t => f (Signal.split s t))
```

### Transforming values and properties, pointwise

What can we do with a refined `map` that we couldn't before?  Let's suppose we
wanted to take our `prng` signal from earlier, which we proved was always going
to return a value on `[0, 256)`.  Suppose this is actually an 8-bit pointer
into an 8-bit ROM bank, like you'd see on NES or Game Boy hardware.  Fixing the
ROM base address as some constant, we want to consume a signal that gives us
the offset into the bank and produces the full 16-bit pointer value.

We'll implement this using `RSignal.map`: the only question is what the
body of the function passed to it should be.

```lean4
def bankedMemory (page : {p : Int // unsignedMax (2^8) p})
  : (□ Int // unsignedMax (2^8)) → (□ Int // unsignedMax (2^16)) :=
  RSignal.map 
    (fun ... /- TODO -/) 
```

Let's follow the types. `f` is a pointwise transformation of the input value
and proof, so it'll take a tuple as argument...

```diff-lean4
def bankedMemory (page : {p : Int // unsignedMax (2^8) p})
  : (□ Int // unsignedMax (2^8)) → (□ Int // unsignedMax (2^16)) :=
  RSignal.map 
-     (fun ... /- TODO -/) 
+     (fun ⟨off, h_off⟩ => sorry /- TODO -/)
```

... and similarly produce a tuple with the right padding, and a proof.  (It's
worth pausing and pondering here to make sure you can express the types for
`off` and `h_off`.)

Some simple arithmetic will do the bitwise- padding job, and `lia` is smart
enough to prove that we've stayed within `2^16`.  (You should definitely try
changing the value of `unsignedMax` and changing the bitwise operation and see
if Lean starts complaining!)

```diff-lean4
def bankedMemory (page : {p : Int // unsignedMax (2^8) p})
  : (□ Int // unsignedMax (2^8)) → (□ Int // unsignedMax (2^16)) :=
    RSignal.map 
-     (fun ⟨off, h_off⟩ => sorry /- TODO -/)
+     (fun ⟨off, h_off⟩ => ⟨page * 256 + off, by lia⟩)
```

## `RSignal.map2` joins two values and two proofs

`RSignal.map2` is not fundamentally different, either, just now with _three_
invariants: two assumptions for the two input Signals and one postcondition for
the output Signal.  Similarly, the mapping function can assume both conditions
are true.

::: margin-warning
If `RSignal.map` does not get us to a `Functor`, then `RSignal.map2`
_extremely_ does not get us to an `Applicative`.  For `Applicative`, `pure : α
→ F α` has to produce a refined value out of nothing but an `α`, there's no
`inv_a` lying around to use as the proof term, and a `StateProp` is too rich of
a dependent type to be inferred from context by Lean.  Alas!

You should email me if you have thoughts on how to make this better.
:::
```lean4
def RSignal.map2
  (f: {a: α // inv_a a} → {b : β // inv_b b} → {c : γ // inv_c c})
  (s1: □ α // inv_a) 
  (s2: □ β // inv_b)
  : □ γ // inv_c :=
  (fun t => f (Signal.split s1 t) (Signal.split s2 t)) |> Signal.collect
```

::: margin-note
Even after we got proper virtual address spaces and memory protection,
segmentation was still used for things like thread-local storage (so on each
thread switch, a different base pointer, for the new thread's TLS segment,
would be swapped in.

Also: In one of my favourite examples of "use what ya got", when researchers
started figuring out how to virtualise x86 - that is, to run entire OSs under a
hypervisor on an architecture that did not actually support virtualisation -
they reused those segment registers to isolate the hypervisor from the guest
OSes.
:::
Let's try and use `map2` to implement, of all things, segmentation for
real-mode on early x86 processors.  Segmentation can be thought of as an early
predecessor to virtual memory: the Intel 8086 chipset had a 20-bit address
space (with 1MiB of addressable memory), so the bus would have 20 data lines,
labeled `A0` through to `A19`.  However, its registers could only hold 16-bit
values, and so therefore pointers could nominally only point to 64KiB of memory
space. So, to increase the addressability of the hardware, pointers were in
fact actually 16 bit _offsets_ into a 16-bit _segment_, where the base address
of the segment was stored in a separate register. 

Because segments were all aligned on a 4-bit boundary, mapping a segment-offset
pair to a final memory address involved shifting the segment left by 4 bits to
get the true 20 bit base pointer, to which the offset pointer is added.

So, our `map2` signal ought to consume two `□ Int // unsignedMax (2^16)`s, one
for the segment register's value and the other for the pointer (the offset into
that segment), and ultimately produce a `□ Int // unsignedMax (2^20)`.
Unfortunately, Lean won't let us prove this, and with good reason - it's not
correct!  

When `lia` tries to discharge the proof that `base * 16 + off < 2^20`, it's
going to use properties of both input arguments (namely, `base < 2^16` and `off
< 2^16`).  Problem is, these two propositions contradict the thing we want to
prove.  Here's the output we get from the `lia` solver:

::: warning
``` lean4
def segment_8086 : (□ Int // unsignedMax (2^16)) →
                   (□ Int // unsignedMax (2^16)) →
                   (□ Int // unsignedMax (2^20)) :=
  RSignal.map2 (fun ⟨base, hb⟩ ⟨off, ho⟩  => ⟨base * 16 + off, by lia⟩)
```
```lean4
`grind` failed
base : Int
off : Int
val : Int
val_1 : Int
⊢ False
...
linear constraints ▼
      [assign] base := 61441
      [assign] off := 65520
      [assign] val := 0
      [assign] val_1 := 0
      [assign] 「2 ^ 16」 := 0 "
```
:::

We're not used to seeing counterexamples in Lean, but `lia`'s solver lets us
see one! From the return type, no matter what values of `base` and `off` we
have, our computation must be `< 0x100000`; however, `base = 0xF001` and `off =
0xFFFF`, and critically, `61441 * 16 + 65520 = 0x100000`!  `lia`'s solver
found us the minimum counterexample. 

What's the _maximum_ counterexample?  When `base = 0xFFFF` and `offset =
0xFFFF`, highest possible 16-bit values for the base and offset pointers almost
make up for a full additional segment; `0x10FFEF` is just 16 bytes short of a
that additional 2^16.  Of course, neither `0x100000` nor `0x10FFEF` are valid
addresses on the 8086; in both cases we'd wrap around to `0x00000` and
`0x00FFEF`, respectively.

We can widen the return type to account for this additional `2^16 - 16` term,
and see that `lia` now discharges our proof, even though of course the hardware
didn't have that additional segment to address.

::: tip
```diff-lean4
  def segment_8086 : (□ Int // unsignedMax (2^16)) →
                     (□ Int // unsignedMax (2^16)) →
-                    (□ Int // unsignedMax (2^20) :=
+                    (□ Int // unsignedMax (2^20 + 2^16 - 16)) :=
    RSignal.map2
    (fun ⟨base, hb⟩ ⟨off, ho⟩ => ⟨(base * 16 + off), by lia⟩)
```
:::

We can certainly model that real-world wraparound behaviour, since we know that
`lia` knows all about modular arithmetic:

```lean4
def segment_8086 : (□ Int // unsignedMax (2^16)) →
                   (□ Int // unsignedMax (2^16)) →
                   (□ Int // unsignedMax (2^20)) :=
  RSignal.map2
  (fun ⟨base, hb⟩ ⟨off, ho⟩ => ⟨(base * 16 + off) % (2^20), by lia⟩)
```

Here, by specifying the implementation more precisely, we were able to be
looser about the type signature of the output of `map2`.

## `weaken` "downcasts" a Signal's invariant

Something that's nice about our refined Signal formulation is that we don't
just compose transformations on data as values flow through the reactive
program, but we can also transform _proofs_ about those values.  Let's wrap
this post up with a final combinator that lets us start with a signal that
maintains a strong invariant, and safely loosens it.

### Modeling the 286's A20 line

We can also model the design change that went into the 80286.  That CPU now let
us address 24-bits of memory (a whole 16 MiB's worth, wowee zowee!)  So, we now
have four more bus lines, `A20` through to `A23`.

So now, our signal will consume that 24-bit base address from the GDT, and
a standard 16-bit pointer which forms the offset into the segment.

::: margin-warning
You should start getting itchy about potential overflows about now.
:::
```lean4
def segment_286_ish : (□ Int // unsignedMax (2^24)) →
                      (□ Int // unsignedMax (2^16)) →
                      (□ Int // unsignedMax (2^24)) := ...
```

The problem was this: The curse of designing a followup to a successful CPU is
that you'll have tons of existing software that can't break on the new design.
(Unless you're Apple, I guess, in which case, just move everybody off Motorola
and then PowerPC and then Intel anyway!) So, Intel had to carry the burden of
maintaining backwards compatibility with software that [assumed that we'd wrap
around on address
`0x100000`](https://www.os2museum.com/wp/the-a20-gate-fallout/).

A classic DOS programming trick involved overflowing the segment + offset
calculation to compute pointers at the top of the address space.
([This](https://www.os2museum.com/wp/who-needs-the-address-wraparound-anyway/)
post covers why you might want to actually do this in practice.) Wrap-around
worked on the 8086, until suddenly we had a larger address space with the 286!

```lean4
example : (0xF01D * 16 + 0xFEF0) % 2^20 = 0x000C0 := by lia
example : (0xF01D * 16 + 0xFEF0)        ≠ 0x000C0 := by lia
```

The bus line that carried bit 20 (and thus enables addresses like `0x100000`)
was, on the 286 (and, frankly, on [chipsets up until
Haswell](https://forum.osdev.org/viewtopic.php?t=29410)) had to be manually
enabled.  This way, legacy software could still have the wrap-around semantics
maintained, while new software could opt-into the larger address space.  (In
practice, enabling that wire is one of the first things any semi-modern OS
would do when it first boots.)

Here's what it means for the A20 line to be in its initial disabled state
and in its raised state:

::: margin-note
Note that `a20Disabled` doesn't say anything about constraining the
highest-order bits 21, 22, or 23.  But that's okay: There's no way that
`segment_8086` could ever touch those bits.
:::
```lean4
-- when A20 is up, the full address space is accessible
abbrev a20Enabled (ptr : Int) : Prop := unsignedMax (2^24) ptr

-- when A20 is down (legacy mode), bit 20 will always have to be 0
-- but other bits are passed through unaltered.
abbrev a20Disabled (ptr : Int) : Prop :=
  unsignedMax (2^24) ptr ∧ (ptr / 2^20) % 2 = 0
```

### Proving bus behaviour equivalence between the 8086 and the 286

The whole point of being able to toggle the A20 line on and off is that the
same bus signals ought to be identical to to the 8086, when it's off.  In other
words, we should be able to take a `□ Int // unsignedMax (2^20)` and use it
where we expect a `□ Int // a20Disabled`, in the same way that we should be
able to take an object of type `Dog` and use it where we expect an `Animal`.

Unfortunately, this sort of "downcast" of a signal's safety property is too
nontrivial for Lean to just let us do automatically:

::: warning
```
def a2o_masked_from_8086 : (□ Int // a20Disabled) := segment_8086 ss ss

Type mismatch
  segment_8086 ss ss
has type
  RSignal Int (unsignedMax (2 ^ 20))
but is expected to have type
  RSignal Int a20Disabled
```
:::

This is annoying because it stands to reason that `lia` or some other arithmetic
tactic _could_ demonstrate this to Lean, but there's no way to slot that proof
in anywhere.  `RSignal.weaken` is the combinator that lets us do that.

OK, so `weaken` is going to consume and produce an `RSignal` of the same base
type, but with a different safety property.  

```lean4
def RSignal.weaken 
  {P Q : StateProp α}
  (s : □ α // P) 
  :    □ α // Q := sorry --TODO
```

For this combinator to be well-formed, how do `P` and `Q` need to relate? Well,
anything that needs to be true about `P`, the property we are given, needs to
also be true with respect to `Q`, the property we're returning.  (For instance,
for numbers for which `0 <= a < 256` is true, `0 <= a < 2048` is also true). In
other words, for every `a`, if `P a`, then `Q a`; we need to know this implication
holds!

```diff-lean4
 def RSignal.weaken 
   {P Q : StateProp α}
+  (h : ∀ a, P a → Q a)
   (s : □ α // P) 
   :    □ α // Q := sorry --TODO
```

The body of weaken is not hard to see once you remember that `map` lets us
manipulate the local safety proof as well as the value itself, and that `h`'s
universal quantifier means we can apply an `a` to it like a function call:

```diff-lean4
 def RSignal.weaken 
   {P Q : StateProp α}
   (h : ∀ a, P a → Q a)
   (s : □ α // P) 
   :    □ α // Q :=
+   RSignal.map (fun ⟨val, p⟩ => ⟨val, h val p⟩)
```

And just as we expect, `lia` will let us weaken an 8086 address-producing
signal to one that the 286 can dereference.

::: tip
```lean4
def a20_off_is_8086 (sig : □ Int // unsignedMax (2^20)) : □ Int a20Disabled :=
  RSignal.weaken (by lia) sig
```
:::

What we _can't_ do is go the other way: an arbitrary physical address for a 286
may not be well-defined on the 8086, and `lia` is happy to give us a counterexample
to show us one such address:

::: warning
```lean4
def i8086_from_286 (sig_286 : □ Int // a20Disabled) : □ Int // unsignedMax (2^20) :=
  RSignal.weaken (by lia) sig_286

`grind` failed
linear constraints ▼
    [assign] a := 2097152
```
(The counterexample, 2097152, is 2^21, aka `0x200000` aka
`0b1000000000000000000000`, which is, indeed, a value that doesn't fit into 20
bits, and yet still has bit 20 unset.)
:::

We _also_ can't, once we've enabled the A20 line, get back to the 8086-compatible
address by weakening it either.  For this to happen, we'd need to be able to prove
that bit 20 is zero, which of course may or may not be true for some arbitrary
24-bit value.

::: warning
```lean4
def a20_down_from_a20_up (sig_286 : □ Int // a20Enabled) : □ Int // a20Disabled :=
  RSignal.weaken (by lia) sig_286

`grind` failed
linear constraints ▼
    [assign] a := 1048576
```
(Here, the counterexample Lean generates for us is literally 2^20, which
certainly has the 20th bit set!)
:::

We _could_, of course, enforce that bit 20 is always zero, in which case the
proof _does_ go through.

::: tip
```lean4
def a20_down_from_a20_up (sig_286 : □ Int // a20Enabled) : □ Int // a20Disabled :=
  RSignal.map (fun ⟨ptr, inv⟩ =>
    -- ptr && !(1 << 20)
    ⟨ptr - 2^20 * (ptr / 2^20 % 2), by lia⟩)
    sig_286
```
:::

## Next time

Phew!  I think I can safely say I have cornered the market on Lean blog posts
that model pre-ia32 Intel architecture semantics :-)

OK, that was a lot of fun.  Thanks for making it all the way to the end.

We're on the home stretch of this series, I think!  We should have enough
mechanism built to actually start writing interesting reactive programs. The
plan for next time is, inspired by
[this](https://www.dwarkesh.com/p/reiner-pope-2) podcast I listened to
last week, to implement  _Hoare logic_, which is a classic way of modeling
stateful, imperative programs formally, and seeing how connectives in hoare
logic map to FRP (and thus LTL).  We'll use hoare logic to implement a simple
systolic array in our FRP library, and prove some hopefully interesting
properties about it.

See you then.

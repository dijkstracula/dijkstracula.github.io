---
layout: post.njk
title: "Reactive programming in Lean part 3: Linear Temporal Logic"
date: 2026-04-02
tags: [post, lean, reactive-programming]
excerpt: "Specifications that move through time"
series: lean-ltl
series_title: "Part three - LTL"
---

In the previous posts, we saw how dependent types let us enforce that every
step our reactive program took was valid, and how our monadic API gives us a
nice way to sequence those steps (even if we lose static guarantees in the
process).

However, we hit the limits of what we could express in terms of propositions
over our system's traces.  It's straightforward enough to write statements
about an individual moment in an execution, but stating things about how
the system needs to move through time feels like we'll need additional mechanism.

Today, we'll define temporal logic and _linear temporal logic_, which is a
common logical system used by model checkers like TLA+ and SPIN, and embed it
into Lean's existing logical system. We'll then see how to specify how our
vending machine should behave over time, with an eye to writing "real reactive
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
with the returned `Flavour` (the result of the computation), all the states
we stepped through, and the final state:

```lean4
#eval getOrange.run init 

Except.ok (
   -- The `Flavour` returned by the computation
  (LemonLime,

   -- The execution trace observed by running the computation
  [{ coins := 0, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 1, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 2, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 0, dispensed := some LemonLime, numOrange := 5, numLL := 4 }]),

   -- The final state following the computation
 { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```

There are all sorts of propositions we could write about the final state:
maybe we want to be assured that the machine successfully ate all the coins
in the hopper, or that we didn't accidentally decrement `numOrange` versus
`numLL`.  We could also write and prove the statement `validStep <final state>
.DropCoin`, or write and _refute_ `validStep <final state> .TakeItem`.

We could also write a proposition related to the output `Flavour` or previous
steps in the trace: for instance, if we're handed back a `LemonLime` at the end
of the computation, we could ensure that at time step `t=3` we had dispensed a
`LemonLime`.

These kind of aren't terribly _interesting_ propositions, though, and this
makes sense becaue what makes reactive programs interesting is that they change
over time, so our logical propositions also need to be able to talk about
change over time.

# LTL is linear temporal logic

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
protocol.  (Maybe we'll build up to one of those examples down the road!)

## The syntax of an LTL formula

OK, we have the notion of time, and the notion of traces, but we don't have the
nouns and verbs defined to state a temporal propsition.

::: margin-note
A _deep embedding_, by contrast, would involve implementing a syntax tree
definition for our logic, and an "interpreter" that does computation on those
syntax trees.  If you've ever implemented a language interpreter, it's a lot
like that; the world of "your host language" and "the language you're
interpreting in the host language" are sort of cleaved in two.
:::
Let's start implementing a _shallow embedding_ of LTL in Lean.  A shallow
embedding of a logic defines that logic in terms of an existing one, which
will be Lean's dependent type system.  That means that a temporal property
will, in the end, just be a `Prop`, so we will end up proving them in exactly
the same way that we'd prove any other theorem in Lean.

I'm going to put all our relevant LTL definitions in their own namespace,
just to organize things a bit better than what we've been doing so far.

```lean4
namespace LTL
  -- TODO: for each temporal modality, write a funciton that
  -- function that returns an appropriate Prop.
end LTL
```

### `LTL.atom` states something about the current moment

Logicians wouldn't really call this a modality, but "something about the
present moment" is certainly something we need to be able to make statements
about.  For example, we might define a `Prop` that expresses whether the
pop machine's coin hopper is empty:

```lean4
def hopperEmpty (s: VMState) : Prop := s.coins = 0
```

If we weren't programming in a dependently-typed language, this would probably
be a predicate function that consumes a state and returns a boolean.  Here,
though, we're not evaluating a conditional expression but intead returning the
expression (of type `Prop`, remember) itself, for a given state.  This is 
an important enough datatype that we can give it a name:

```lean4
abbrev StateProp σ := σ → Prop
```

And, this means `LTL.atom` will want to consume such a function, for an
arbitrary state type sigma:

```lean4
    def atom (p : StateProp σ) ... : Prop := ... -- NEW
```

Since we're making a statement about a particular trace, `atom` needs to know
what trace that is:

```lean4
    def atom (p : StateProp σ) (t : Trace σ) : Prop := ... -- NEW
```

So that's the statement we want to assert and over what execution we want to
assert it.  We can now define what `atom` means: it's an assertion that the
proposition holds at the current moment.  Using our `now` helper from last
time, we can finish the definition.

To make use of `LTL.atom`, we use it as part of a `theorem`, just like any
other proposition in Lean.  

```lean4
namespace LTL
   def atom (p : StateProp σ) (t : Trace σ) : Prop := p (now t)
end LTL
```
::: margin-note
`rfl` is enough to discharge the proof of this theorem, but we can make a
more general statement: _for every_ trace where `t 0` is `init`, the hopper
starts out empty.  Can you state this formally and prove it?
:::
```lean4
def hopperEmpty (s : VMState) : Prop := s.coins = 0
def isCurrentlyEmpty := LTL.atom hopperEmpty

theorem startsEmpty : isCurrentlyEmpty (getFragment init getOrange) := by rfl
```

### `eventually` and `always` make claims over entire traces

The first of the real modalities is `eventually`, which states that at some
point in the future, some statement holds.  The second, `always`, makes the
claim about a statement holding now and at every future time step.

```lean4
namespace LTL
    ...
    def always     -- TODO
    def eventually -- TODO
end LTL
```

`eventually` is an _existential_ proposition because it's saying _there exists_
some point in time where the statement is true, and dually, `always`
universally quantifies over _all_ subsequent points in time.  You could imagine
that `\exists` and `\forall` will likely appear somewhere in them, and indeed
that's the case:

```lean4
    def always     : Prop := ∀ i, p (drop i t)
    def eventually : Prop := ∃ i, p (drop i t)
```

As before, these definitions will take some `p` and `t` as argument.  `t` isn't
surprising: it's our `Trace σ`.  

```lean4
    def always     (p : ???) (t : Trace σ) : Prop := ∀ i, p (drop i t)
    def eventually (p : ???) (t : Trace σ) : Prop := ∃ i, p (drop i t)
```

But, `p` clearly can't consume just an
individual state `σ` as it did in `atom`, because `drop` produces a whole new
`Trace σ`.  So, this is a predicate over _entire traces_; this is the key to
being able to write specifications that straddle multiple points in time.

```lean4
namespace LTL
    ...
    abbrev TraceProp σ := (Trace σ → Prop)
    ...

    def always (p : TraceProp σ) (t : Trace σ) : Prop := 
      ∀ i, p (drop i t)
    def eventually (p : TraceProp σ) (t : Trace σ) : Prop := 
      ∃ i, p (drop i t)
end LTL
```

::: margin-note
"the diamond operator is a box that will _eventually_ fall over, whereas a
square operator will _always_ lie flat on the floor"?  I donno.
:::
`eventually` is sometimes abbreviated to the somewhat-opaque `F` (for _F_uture)
and the very-opaque `⋄`, and `always` to `G` (for _G_lobal) and `□`.  I will
suffer `F` and `G` since I kind of have a mnemonic for them, but "the diamond
operator" and "the square operator" will forever be utterly impossible for me
to keep straight.  Maybe writing this blog post will help, so let's create
new Lean syntax to accommodate them.  The `prefix:max` directive indicates that
they're prefix operators, bound as tightly as possible.

```lean4
namespace LTL
    ...

    prefix:max "□ " => always
    prefix:max "◇ " => eventually
end LTL
```

### `until` generalises `eventually` and `always`

Here's a more exotic modality: `p1 until p2` states that `p1` holds up to
some indeterminate point in the future, upon which `p2` will start to hold.

```lean4
namespace LTL
    ...
    def until_then (p1 : TraceProp σ) (p2 : TraceProp σ) (t : Trace σ) : Prop :=
      ∃ n, 
        (∀ i, i < n → p1 (drop i t)) ∧ 
        p2 (drop n t)

    infixr:25 " U " => LTL.until_then
end LTL
```

`until` is in fact a more general form of `always` and `eventually` (in fact,
we could have written `always` and `eventually` in terms of `until`).  (In a
bit, we'll prove that this is true!)

### `LTL.next` looks ahead one step

Here's our final true temporal modality: Given a trace, we can make a statement
about one unit of time in the future with the `next` (abbreviated `X` or
sometimes `○`) operator: after `U`, it's not that goofy looking:

```lean4
namespace LTL
    ...
    def next (p : TraceProp σ) (t : Trace σ) : Prop := p (drop 1 t)

    prefix:max "○ " => LTL.next
end LTL
```

## The semantics are LTL are the semantics of Prop

Having spent so much time defining the syntax of LTL, you might expect we need
to spend as much time describing the _meaning_ of the syntax.  But, because we
defined LTL's connectives as functions that ultimately return `Prop`s, the
semantics of LTL ends up being "whatever Lean's propositions" means. (An
earlier draft of this post, by contrast, did a _deep embedding_, where we build
up a syntax tree of LTL formulas and also implement an evaluation function that
crunches down the formula down to a final prop.)

What's cool about shallow embeddings is that it's trivial to prove identities
about LTL in Lean's proof system.  (In a deep embedding, we'd have to reason
about LTL in terms of how its evaluation function interprets those LTL
propositions.)

For instance, we said earlier that `until` is a generalisation of `eventually`
and `always`: if that's true, we should be able to express those two modalities
in terms of ` U `.  Indeed we can!


```lean4
-- Two helpers to make the statements a bit nicer to read:

-- 1. "True" as a trace predicate: holds for any trace, at any time
-- "True" as a trace predicate: holds for any trace, at any time
@[simp]
def true : σ → Prop := (fun _ => True)

-- 2. "Not" negates `p` at every step in the trace.
def not (p : TraceProp σ) : TraceProp σ := (fun t => ¬ p t)

-- OK, our derived equivalences:

-- Eventually p means things are trivially true up until some point, after 
-- which p holds
example : ◇ p = true U p := by 
  unfold eventually; unfold until_then; unfold true
  simp

-- always p means it's not the case that eventually, not p
example : □ p = not (true U not p) := by
  unfold always; unfold until_then; unfold not
  simp
```

With a shallow embedding, it's pretty trivial to prove this, since we're just
operating on Lean functions and `Prop`s!  A deep embedding would require first
writing a bunch of theorems about that formula-to-prop evaluation function.

# Safety and Liveness

LTL is the workhorse logic for two broad classes of propositions: _safety_
properties, which ensures that a system never fails to behave according to its
specification (`□ ¬bad`), and _liveness_ properties, which ensures that some
desired property will always eventually happen (`◇ good`).

Let's wrap this post up by looking at one of each kind of property.

## Safety properties can be proven for arbitrary (valid) traces

A brief reminder: a system `s` can step with action `a` if the type `validStep
s a` is inhabited.  In other words, it encodes what has to be true about `s`
before `a` happens.

It might feel as though any safety property is inherent in the definition of
our `validStep` type.  But safety properties might not be a precondition on
taking a step.  They could be a property on the step itself, or on the initial
state of the system.  They could even be a property over all three (a special
kind of invariant called an _inductive invariant_; if you're into model
checking then you're always on the hunt for inductive invariants, or ways to
turn a non-inductive invariant into an inductive one).

Extending `validStep` to traces, an entire trace is valid if we start from a
valid trace (a property called _initialization_), and we only step from a valid
state to another one (_consecution_).

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

Here's an important property of making a profitable pop machine: it should
always be the case that if the user hasn't put enough money in the machine, no
can should be subsequently dispensed.

::: margin-note
As it happens, `noFreeLunch` happens to not be inductive because it's not a
predicate on states that's preserved by every step, but rather a conditional
property of the form "if we look like this now, we'll look like this next". 

We'll see the consequences of this when we start proving it.
:::
```lean4
-- Helper definition for implication in LTL
def implies (p q : TraceProp σ) : TraceProp σ := fun t => p t → q t

-- ...and an operator for LTL implication, typed as \nat_trans 
infixr:20 " ⟹  " => implies
```
```lean4
-- If the user hasn't paid enough, we will never dispense a can
def noFreeLunch : TraceProp VMState :=
  □ ((atom (fun s => s.dispensed.isNone ∧ s.coins < 2)) ⟹
    (○ (atom (fun s => s.dispensed.isNone))))
```

This says: "if, right now, the dispenser is empty, and you've not paid enough,
then in the next step the dispenser is still empty."  Note that this works
because `validAction` for `Choose` requires `coins >= 2`, and you can't jump
from `coins < 2` to `dispensed.isSome` in one step.)

### Proving safety properties over arbitrary traces

Let's prove that this theorem holds not just for our `getOrange` trace but _for
all valid traces_.  That we can do this for safety properties (in particular,
for inductive invariants) is critical to verifying real-systems; if we can
state our system's specifications in terms of inductive invariants then the
claims we can make about the design are strong.

```lean4
theorem noFreeLunch_holds : ∀ (t : Trace VMState) (hv : validTrace t), noFreeLunch t := by
  intro t HValid
  -- TODO: what next?

1 goal
t : Trace VMState
HValid : validTrace t
⊢ noFreeLunch t
```

### Inline destructuring of a conjunction with `<` and `>`

Remember that our proof that `t` is a `validTrace` falls back to a proof of
initialization (that is, `t 0 = init`) _and_ of consecution (`∀ (i : Nat), ∃ a
h, t (1 + i) = vmStep (t i) a h`).  Proving an inductive invariant always means
wanting to reason about both of those sub-pieces individually.

We _could_ write `have ⟨h_init, h_cons⟩ := HValid` to pattern-match out the two
pieces of the conjunction (recall that `have` is like `let` but for the proof-world).
But, we can actually do that pattern-match right in the intro step, saving us
a step and emphasizing that what's important are the two components of the
statement.

```lean4
theorem noFreeLunch_holds : ∀ (t : Trace VMState) (hv : validTrace t), noFreeLunch t := by
  intro t ⟨h_init, h_cons⟩
  -- TODO: OK, what now??

1 goal
t : Trace VMState
h_init : t 0 = init
h_cons : ∀ (i : Nat), ∃ a h, t (1 + i) = vmStep (t i) a h
⊢ noFreeLunch t
```

### Getting to the heart of the theorem

As usual, let's introduce our variables into the context (remember, this is
like stating "let `t` be some trace and assume `t` is a `validTrace`" in an
English-language proof.  A lot of machinery is hidden behind `noFreeLunch`, so
let's unfold that definition, and also simplify away all the LTL connectives
that make up the definition:

```lean4
theorem noFreeLunch_holds : ∀ (t : Trace VMState) (hv : validTrace t), noFreeLunch t := by
  intro t ⟨h_init, h_cons⟩
  simp [noFreeLunch, always, implies, next, atom, now, drop]

1 goal
t : Trace VMState
h_init : t 0 = init
h_cons : ∀ (i : Nat), ∃ a h, t (1 + i) = vmStep (t i) a h
⊢ ∀ (i : Nat), (t i).dispensed = none → (t i).coins < 2 → (t (1 + i)).dispensed = none
```

Before proceeding, you should make sure that you're convinced that our goal
is still stating the no-free-lunch theorem.

OK, We now have a new universal and two hypotheses, so let's pull them into the context too.

```lean4
theorem noFreeLunch_holds : ∀ (t : Trace VMState) (hv : validTrace t), noFreeLunch t := by
  intro t ⟨h_init, h_cons⟩
  simp [noFreeLunch, always, implies, next, atom, now, drop]
  intro i h_empty h_unpaid

1 goal
t : Trace VMState
h_init : t 0 = init
h_cons : ∀ (i : Nat), ∃ a h, t (1 + i) = vmStep (t i) a h
i : Nat
h_empty : (t i).dispensed = none
h_unpaid : (t i).coins < 2
⊢ (t (1 + i)).dispensed = none
```

### Specializing a universally-quantified proof is like calling a function

Great progress, but it might not be clear how to proceed from here.  The key is to
notice that `h_cons` is universally quantified over all timesteps and so it's really
a function from any given `i` to a proof about that step.  And as it happens,
we have an `i` timestep in our context!

`h_cons i` _specializes_ `h_cons` from talking about all `Nat`s universally to
the specific `i` we have in scope now.  It gives us the concrete witness we
want: the action taken, its proof of validity, and the equation relating `t i`
to `t (i+1)`.

Since everything in these series boils down to Curry-Howard: under the
propositions-as-types reading, a universal quantifier is a function, and
instantiating a universal is function application.  (If this feels funny, think
about how parametric polymorphism is _also_ a universal quantification over
type parameters, and so, say, instantiating `List` with `Int` looks just like
function application too.)

```lean4
theorem noFreeLunch_holds : ∀ (t : Trace VMState) (hv : validTrace t), noFreeLunch t := by
  intro t ⟨h_init, h_cons⟩
  simp [noFreeLunch, always, implies, next, atom, now, drop]
  intro i h_empty h_unpaid
  have ⟨a, h_valid, h_step⟩ := h_cons i

1 goal
t : Trace VMState
h_init : t 0 = init
h_cons : ∀ (i : Nat), ∃ a h, t (1 + i) = vmStep (t i) a h
i : Nat
h_empty : (t i).dispensed = none
h_unpaid : (t i).coins < 2
a : VMAction
h_valid : validAction (t i) a
h_step : t (1 + i) = vmStep (t i) a h_valid
⊢ (t (1 + i)).dispensed = none
```

All this work has just gotten us to the following point: we need to prove that
no matter which step we took at `t i`, consecution is preserved.  So, having
the actual definition of a `validAction` at that time, for our given
`VMAction`, unfolded for us is probably going to be useful.  However, when we
do that unfolding, we end up with a real dog's breakfast in our context:

```lean4
...
  unfold vmStep at h_step

...
h_step : t (1 + i) =
  match a, h_valid with
  | VMAction.DropCoin, H =>
    { coins := (t i).coins + 1, dispensed := (t i).dispensed, numOrange := (t i).numOrange, numLL := (t i).numLL }
  | VMAction.TakeItem, H =>
    { coins := (t i).coins, dispensed := none, numOrange := (t i).numOrange, numLL := (t i).numLL }
  | VMAction.Choose Flavour.Orange, H =>
    { coins := (t i).coins - 2, dispensed := some Flavour.Orange, numOrange := (t i).numOrange - 1,
      numLL := (t i).numLL }
  | VMAction.Choose Flavour.LemonLime, H =>
    { coins := (t i).coins - 2, dispensed := some Flavour.LemonLime, numOrange := (t i).numOrange,
      numLL := (t i).numLL - 1 }
  | VMAction.Restock, H => init
...
```

Reflexively trying to simplify this with `simp at h_step` doesn't work because
we don't know anything about which `a` we're talking about here.  So, we'll have to
break up the proof by the different possible actions, and then simplify.

```lean4
  ...
  cases a <;> simp at h_step 

4 goals
...
⊢ (t (1 + i)).dispensed = none
```

Once we prove consecution for each of the four actions, we'll be done with our
liveness proof.

### Immediately closing a contradictory goal

Before proceeding, you should pause and think about which action is outright impossible to
step to given the propositions in our context.  (Hint: it relates to `h_empty`.)

::: margin-note
Despite looking similar, they do different things:

- `simp at h_step` simplifies the hypothesis itself: it reduces the match
  expression inside h_step now that a is concrete, turning the big match into a
  simple equation like `t (1 + i) = { dispensed := (t i).dispensed, ... }`.
- `simp [h_step]` simplifies the goal using `h_step` as a rewrite rule: it
  substitutes that equation into the goal `(t (1 + i)).dispensed = none`,
  replacing `(t (1 + i)).dispensed` with `(t i).dispensed`.
:::
If you said something to the effect of, "`validAction` for `TakeItem` requires
`(t i).dispensed.isSome`, but `h_empty` says `(t i).dispensed = none`", then
well done!  So `h_valid` is contradictory with `h_empty`, and `simp [h_step]`
finds the contradiction automatically.  We're now ready to proceed with the
remaining subproofs:

```lean4
  cases a <;> simp at h_step <;> simp [h_step]
  case Restock =>  sorry --TODO
  case DropCoin => sorry --TODO
  case Choose f => sorry --TODO

3 goals
...
⊢ (t i).dispensed = none
```

### `Restock` and `DropCoin` don't change the state of the dispenser

When we focus in on the `Restock` case, our goal becomes `⊢ init.dispensed =
none`  This is a fact that can be trivially proved!  So `rfl` closes the goal.
Similarly, in the `DropCoin` case, our goal becomes `(t i).dispensed = none`,
which is already in our context.  So, `assumption` closes the goal.

```lean4
...
  case Restock => rfl
  case DropCoin => assumption
```

### `Choose` wouldn't have been a valid action anyway

We know that since `t` is a valid trace, we are statically blocked from
choosing `Choose`ing any flavour.  So, that tells us that we're looking
for a contradiction here.  And indeed, it's not hard to get to a `False`
goal no matter which flavour is chosen:

```lean4
  case Choose f => 
    cases f <;> simp

2 goals
...
h_unpaid : (t i).coins < 2
h_valid : validAction (t i) (VMAction.Choose Flavour.Orange)
...
⊢ False
```

Where's the contradiction going to lie?  Well, it's got to be somewhere in
`validAction` when we choose `Choose`.  `simp at h_valid` unfolds the
definition and gets to the heart of the problem: `h_valid : 2 ≤ (t i).coins ∧ 0
< (t i).numOrange` is our precondition for choosing Orange (and similarly for
LemonLime), but this contradicts `h_unpaid`.  `lia` knows enough about
arithmetic inequalities to prove this final step.

Here it is, our final proof!

```lean4
theorem noFreeLunch_holds : ∀ (t : Trace VMState) (hv : validTrace t), noFreeLunch t := by
  intro t ⟨h_init, h_cons⟩
  simp [noFreeLunch, always, implies, next, atom, now, drop]
  intro i h_empty h_unpaid
  have ⟨a, h_valid, h_step⟩ := h_cons i
  unfold vmStep at h_step
  cases a <;> simp at h_step <;> simp [h_step]
    case Restock => rfl
    case DropCoin => assumption
    case Choose f => 
      cases f <;> simp <;> simp at h_step <;> simp at h_valid <;> lia
```

## Liveness properties can't be proven for arbitrary traces

Here's something else that's worth stating:

```lean4
def mustPayFirst : Trace VMState → Prop :=
  (LTL.atom (·.dispensed = none)) U (LTL.atom (·.coins ≥ 2))
```

Applying this proposition to our sample trace isn't as scary as it might look:

```lean4
theorem allPaidUp : mustPayFirst (getFragment init getOrange) := by --TODO

1 goal
⊢ mustPayFirst (getFragment init getOrange)
```

First, let's unfold a bunch of our definitions (using `simp` so we can one-line it):

```lean4
theorem allPaidUp : mustPayFirst (getFragment init getOrange) := by
  simp [mustPayFirst, LTL.U, LTL.atom]

1 goal
⊢ ∃ n,
  (∀ (i : ℕ), i < n → (now (drop i (getFragment init getOrange))).dispensed = none) ∧
    2 ≤ (now (drop n (getFragment init getOrange))).coins
```

The goal is asking us to provide us with the point in the trace that satisfies
the `until`.  Because we know this particular trace, we know it's at index 2,
and that's enough to satisfy Lean.

```lean4
theorem allPaidUp : mustPayFirst (getFragment init getOrange) := by
  simp [mustPayFirst, LTL.U, LTL.atom]
  exists 2

0 Goals
Goals accomplished!
```

We might want to be able to do something more powerful: prove that a liveness
property like this holds for all valid traces!  Sadly, in general this is
impossible: a user who just drops in coins without choosing, or a janitor who
just keeps restocking the machine, or any number of other valid traces wouldn't
satisfy this constraint. 

::: margin-note
Pause and ponder: What assumptions could you put on the environment to find a
lasso in the pop machine's states?
:::
For making general claims about liveness, you either need additional constraints
(sometimes called "fairness" constraints) assumed in the environment, or to prove
that eventually all infinite traces end up looping back to a previous state,
essentially making the number of possible states in the system finite.  (This
is called _lassoing_ and is really important for model checkers to verify
interesting systems.)

## Our LTL operators, summarised:

Here's where we ended up today:

```lean4
  -- A property of a single state (no temporal structure)
  abbrev StateProp (σ : Type) := σ → Prop

  -- A property of a trace (can involve temporal structure)
  abbrev TraceProp (σ : Type) := Trace σ → Prop

  atom       : StateProp σ → TraceProp σ      -- lifts state to trace
  always     : TraceProp σ → TraceProp σ      -- trace in, trace out
  eventually : TraceProp σ → TraceProp σ
  next       : TraceProp σ → TraceProp σ
  until_then : TraceProp σ → TraceProp σ → TraceProp σ
```

We could do what we did in the first two sections, writing reactive programs
and tying their behaviour to a separate LTL specification.  But, if we redesign
our program around a few well-chosen types, we can get all the benefits of an
LTL spec that integrate directly into our program's types.  See you next time,
when we make just this happen.

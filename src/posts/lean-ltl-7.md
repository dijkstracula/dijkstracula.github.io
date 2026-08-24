---
layout: post.njk
title: "FRP in Lean: LTL modalities as FRP algebraic structures"
date: 2026-07-30
tags: [post, lean, reactive-programming, frp]
excerpt: "Squaring the circle to support every LTL connective in an FRP type"
series: lean-ltl
inlineCodeLang: lean4
series_title: "Intermezzo: modalities as algebras"
draft: true
---

<script src="/js/frp/runtime.js"></script>

## Welcome back!

Last time we implemented a series of combinators that transformed not just data
values that might flow through a functional reactive program, but invariants
about that data.  We introduced a _signal of refinements_, where at each time step
we bundle the signal's value with a local proof that that timestep-dependent
value maintains a given property:

{% lean "Examples/Ltl7.lean", "rsignal-review-sig-of-refinements" %}

We also saw _refined signals_, where instead of each time step producing a
pair, the signal itself is a pair of a signal and a _global_ safety property,
asserting the property is true at all time steps:

{% lean "Examples/Ltl7.lean", "rsignal-review-refined-sig" %}

Lastly, we saw that `RSignal.split` and `RSignal.collect` were the bridges
between these two worlds: `split` shards a refined signal into a signal of
refinements, and `collect` goes the other way.

{% lean "Examples/Ltl7.lean", "rsignal-review-split-collect" %}

It certainly feels like there's some underlying algebraic structure here. In
this post, we're going to do a generalisation exercise to uncover just that
structure.  The intention here is, at the end of the exercise, for us to have
"mined" a correct and complete FRP library API from that underlying structure,
so that in future posts we can start writing _really_ interesting programs.

## Warmup: Faking `RSignal` as a Functor

We discussed last time that we can't make `RSignal` an instance of the
typeclass `Functor`, because `RSignal` has a dependent type `(α : Type) →
(StateProp α) → Type`, which won't fit `Functor`'s single-argument `Type →
Type` shape.  (We broadly say that `RSignal` is _indexed_ on `StateProp`.)

::: margin-note
If we were more intolerable, we might say that `RSignal` is not an endofunctor
on `Type`.
:::
The intuition here is that when we map over a plane old `Signal`, we expect to
be able to transform the base type (say, mapping over a `Signal Float` with
`round` to yield a `Signal Int`), and so `Functor`'s `Type → Type` shape makes
sense.  But an `RSignal` also expects to be able to change the `(StateProp α)`
invariant, which isn't captured in the `fmap` signature `(α → β) → f α → f β`,
which only speaks about the base type.

We can at least, though, add a custom operator to replace the `<$>` we don't
get to actually define:

```diff-lean4
+ infixr:100 " <$$> " => RSignal.map
```

Going forward, I'll use our "dependent fmap" operator `<$$>` in place of
`RSignal.map` whenever possible.

### Two readings of `<$$>`

Remember that `<$$>` transforms signal values in a pointwise manner: for
a dependent function `f` and a refined signal `s`, `f <$$> s` means that at
each timestep, `s i` gets turned into `f (s i)`.   

This is a _transformed signal_: whatever refinement `pre` that `s` had previous
to the application is replaced by `post`, the refinement of `f`.

::: margin-note
Remember that the dot in `f <$$> ·` is an anonymous function
argument, so this expression is the same as `fun s => f <$$> s`. 
:::
Here's another view that moves up a level of abstraction: let's put aside
`<$$>` for a moment and look at the larger expression `f <$$> ·`, without a
particular `s`.  This is a _signal transformer_.

What type does a signal transformer have?  Let's fix some particular `f` and
take a look:

```lean4
def incr : (i : {i : Int // i ≥ 0}) → {i : Int // i > 0} := fun i => ⟨i.val + 1, by lia⟩
#check (incr <$$> ·) -- (□ Int // ⌜· ≥ 0⌝) → (□ Int // ⌜· > 0⌝)
```

Here, `LTL.atom (· ≥ 0)` is our _precondition_ and `LTL.atom (· > 0)` our
_postcondition_, with `(incr <$$> ·)` the bridge between the two.  Functors
don't have to be the only bridge structure, though:

## Signals, Comonads, and Tralfamadorians

We've seen earlier in this series -- and you've almost certainly seen elsewhere
in the world -- that monads are values that you can put into a computational
context, and sequence.  (To be a proper monad, you also need to behave like
one, by always following the _monad laws_.  The devil's always in the details.)

::: margin-note
Embedded proofs of satisfying algebraic laws are also part of Lean's [lawful
variants](https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Laws/#LawfulMonad___mk).
:::
{% lean "LtlFrp/Structures.lean", "monad" %}

Because FRP programs that we compose together with `Signal`'s functorial
primitives like `<$$>` propagate their values "instantaneously", we don't
really have a notion of discrete "this; then, that" steps like the original
vending machine example.  (You can see that it's instantaneous because `<$$>`
is pointwise; whatever changes dependent signals makes at time `t` affect all
downstream signals at that same moment.)

So, it kind of makes sense that we never tried to make `Signal`s monadic.  In
fact, what a `Signal` really is is the _dual_ of a monad: it's a
[comonad](https://bartoszmilewski.com/2017/01/02/comonads/)!

A dual of a thing is like the opposite of that thing.  So, to figure out what
the dual of a monad might be, let's take `pure` and `bind`, and flip the
direction of its function type arrows.  So, a function `α → (β → γ) → δ`
becomes `δ → (γ → β) → α`.

## `extract` is the dual of `pure`

The dual of `pure : α → M α` just reverses one arrow, yielding `M α → α`.
Intuitively: if `pure` injects a value into a monad, its dual extracts a value
out of a comonad. So, let's name this function `extract`: a comonad must always
have a notion of a "current value", and it's `extract` that lets us read 
that value out whenever we please.

Does `Signal` have a function that looks like that?  Certainly!  `Signal.now`
produces the signal's value at the current time step.

{% lean "LtlFrp/FRP/Simple.lean", "now" %}

So, `Signal.now` is our `extract`: this was the easy one, both in terms of
playing our arrow-flipping game but also interpreting what the function
signature must mean.

## `duplicate` is the dual of `join`

::: margin-note
Of course, you should take a minute and think about how you might implement
`bind` in terms of `join`.
:::
`join` isn't strictly part of the definition of a monad, but it's certainly
adjacent: `join` has type `M (M α) → M α` and is a "flattening" operation:
given two nested monads, product a single one.  (You can see how this might be
used in `bind`, given that that function is sometimes called `flatMap`!)

The dual of `join` would have to be typed `M α → M (M α)` by our arrow-flipping
rule.  Here we are "un-flattening" the comonad by having a "comonad-producing
comonad".

Do we have anything like a "signal-producing signal"?  Not exactly as written,
and it's not even necessarily clear what that might mean at first glance.

Luckily, because a `Signal a` is so generic a type, there's really one one
direction we can go to produce a `Signal (Signal a)` out of one.  `a` is some
arbitrary type, so by
[parametricity](https://www.khoury.northeastern.edu/home/cmartens/Courses/7400-f24/readings/theorems-for-free.pdf) we have to leave those elements alone (what can we do with an arbitrary
value of an arbitrary type?)

What _isn't_ an arbitrary type, though, is `Time`: What if our
signal-of-signals produced a `Signal` that somehow varied in time?  Take a look
at `Signal.drop`:

{% lean "LtlFrp/FRP/Simple.lean", "drop" %}

As written, this consumes an offset and a `Signal`, and skews that `Signal` by
the given offset.  But remember that this offset, being a `Nat`, can also be
interpreted as a `Time`!  This _is_ kind of a "signal-producing machine, given
an input timestep", and so by rearranging the `Nat` argument we can write this
as a signal of signals:

{% lean "LtlFrp/FRP/Simple.lean", "drop_v2" %}

These two functions are identical but their interpretations are very different:
`drop` now produces a sort of "time-varying time-varying value": at each `t`,
produce the `Signal` shifted backwards by `t`.  So, `Signal.drop` is our
`duplicate`.

::: note
You might wonder if `Signal.drop` is the unique conclusion we could draw from
the type signature `Signal a → Signal (Signal a)`.  For instance, we could
imagine writing a silly implementation of `duplicate` whose signal-of-signals
just returns the input `Signal` at all time steps; this feels "wrong" but still
typechecks.  Stay tuned.
:::

Just one more to go and then we'll be convinced that `Signal` is comonadic.

## Deriving the dual of `bind`

The dual of `bind: M α → (α → M β) → M β` is a bit more annoying to reverse, but
we end up with `M β → (M β → α) → M α` when we do so.  Let's rename `α` and `β`
just so they still represent "the input type" and "the output type" respectively.
This leaves us with some function `cobind: M α → (M α → β) → M β`.  Notice that
the only difference between `bind` and this "`cobind`" dual is the type of the
transformation function we pass it (the second argument).  

### Comparing `bind` and "`co-bind`"'s function arguments

Let's compare those second arguments:

`bind`'s argument, `(α → M β)`, consumes the "unwrapped" `α` value from the
monad and then uses it in the construction of a fresh monad.  In short, "value
in; context out".  We can also think of a bind operationally, in terms of
"`map` and then `join`": mapping over a monad `M a` with a `(α → M β)` produces
a nested `M (M β)`, which we can flatten down with `join` into a final `M β`.
So, `bind m f = join (map m f)` (or `bind f = join ∘ map f` if you're feeling
point-free).

Here, on the comonadic side, a `(M α → β)` function consumes the comonad
directly, producing a single unwrapped value that then gets rewrapped into the
comonad on the way back out.  In short, "context in, value out".  

### Implementing "`cobind`" in terms of `duplicate`

Okay, we have a rough idea of what the types for `cobind` mean.  How do we
write this function down?  The key's in using `duplicate` and playing the "flip
the arrows" game once more with our operational interpretation: 

We said earlier that `bind` is "`map` and then `join`".  Flip this around and
substitute `join`'s dual: we're left with a guess that `cobind` is "`duplicate`
and then `map`". Let's see if the types work out:  

Starting with a `M α`, we `duplicate` into a `M (M α)`.  We then `map` over all
the duplicated `M a`s, and for each one, producing a single `β`.  `map` will
then lift each `β` back up into a final `M β`.

So, we could write this function as `cobind cm f = map f (duplicate cm)` - hey,
if we flipped the order of `cm` and `f`, then we have `cobind f cm = map f
(duplicate cm)`, which is `cobind f = map f ∘ duplicate`!  That's an extremely
satisfying dual to `bind f = join ∘ map f`, just as we had hoped.

Okay, but what does this function _mean_?  The use of `duplicate` gives us,
like we discussed earlier, an infinite series of offset-in-time `Signal`s, each
of which is handed to our `f` to summarize down to a single value, queryable in
its own fresh `Signal`.

For this reason we call "`comonad`" `extend`.  With `extend`, we can look at a
local neighbourhood around each point in time, and compute a new value based on 
that context.

## Deriving the comonad laws from our one weird trick

All right, let's bundle this up into a Lean typeclass as we did with `Monad`
above - for the propositions about left and right identity, and associativity,
play the "invert the arrows" game three final times:

{% lean "Examples/Ltl7.lean", "comonad_v0" %}

`rid` is kind of my favourite here:  The monadic version says "sequence a pure
lifting step into a monad `ma` and you get back the original monad".  The
comonadic version says "extend a comonad `wa` out to infinity by just
performing the point-read extraction and you get back the original `wa`".

What _is_ annoying though is that we call these "identity" and "associativity",
the propositions don't actually look at all like statements about identities
and associativity.  We might have expected the laws to look like "`<something>
⊕ f = f`", "`f ⊕ <something> = f`", and "`f ⊕ (g ⊕ h) = (f ⊕ g) ⊕ h`", for any
well-typed `f`, and well-chosen `<something>`s and `⊕`s.

## You could have invented the coKleisli category

Kleis-_what_?  Categ-_who_??  Ok never mind, let's just solve for the way to
write these laws more tidily.

Our goal for this section is to be able to write `lid`, `rid`, and `assoc`
in terms of some operator `⊕`, for which those theorems really do look like
identity and associativity.

Our strategy is going to be this: notice that the shape of the laws with `⊕` in
the previous section don't actually mention a comonad `wa`, but only how
functions in the `Comonad` typeclass and some function `f` interact.  This
is in contrast to our current laws have `wa` sprinkled around on both sides of
the equality.  So, not only will our "new and improved comonad laws" actually
look like the algebraic properties they're supposed to express, but they'll in
some sense be more general since by writing them without `wa` we'll be
"removing a degree of freedom" from the propositions.

Of course, the comonad laws actually _do_ need to talk about a `wa`, so we're
going to banish it from our laws by partial application: if we can figure out
how to write, say, `(f ⊕ <something>) wa = f wa`, we can drop the argument on
both sides and leave things written in a point-free manner.

### Sketching `⊕` with the identity laws

Since `rid` is my favourite of the two identity laws, let's start with seeing
how we can banish `wa` from `extend wa extract = wa`.  If this could be
slightly rearranged to `<something> wa = wa`, then we could "cancel `wa` on
both sides", so we'd be left with `<something> = id`.  Problem is, of course,
`wa` is in the middle of a larger expression, and while function application
has many properties commutativity isn't one of them.

What we _could_ do, though, is implement some new `extend'` function that simply
flips its two input arguments: Then, we'd truly have `extend' extract wa = wa`
and we'd be well on our way.

{% lean "Examples/Ltl7.lean", "extend'" %}

OK, cool!  Written in this form, `rid: extend' extract wa = wa` is our new
right identity; we're now free to drop `wa` on both sides, which leaves us
as `extend' extract = id`.  That in itself is a neat property.

Here's one last thing we can do: compose both sides with a given `f`: now we
have `f ∘ extend' extract = f`.  This is exactly the shape we are after!  We
started wanting `f ⊕ <something> = f` and we've figured out both unknowns:
`<something>`, written a bit more explicitly, is `fun wa => extend wa extract`,
and `⊕` is going to involve applying `∘`, the function composition operator,
with that `<something>`.

What about `lid`?  It's `extract (extend' f wa) = f wa`, which is shockingly
convenient, since we can already peel off the `wa` on both sides and solve for
`f` on the right-hand side: `extract extend' f = f` is what we're left with!

## Proving that (non-refined) `Signals` are comonads

OK, Let's instantiate `FRP.Signal` (that is, our non-dependent `Signal`) as a
`Comonad`.  We'll begin with the function implementations: `extract` is just
literally `now`, and we can define `extend` in terms of `drop`, which is our
`duplicate`:

```lean4
instance : Comonad Signal where
  extract := now
  extend cm f := f <$> (drop cm)

Fields missing: `lid`, `rid`, `assoc`
```

::: margin-note
While I endeavour to write all these posts on my own, I admit that an LLM is a
great way to have a fuzzy search engine for the Lean documentation.
:::
Three annoying gotchas about discharging `lid`, `rid`, and `assoc`, that I
admit took me forever to figure out, all involving function application inside
the proof goal:

### left identity proof: `simp` may not match partial applications

The left identity, as you recall, says `extract (extend wa f) = f wa`. Here's
the proof state for left identity after we `intro` all our definitions:

```lean4
  lid := by intro α sig β f;

1 goal
α : Type
sig : Signal α
β : Type
f : Signal α → β
⊢ now (f <$> drop sig) = f sig
```

Clearly the thing to do is unfold some definitions (`now`, `drop`, `<$>`) to
get to a point where we can simplify our proof.  If we `unfold drop` as the
next tactic, the goal makes progress: the call to `drop sig` gets replaced
with the function definition, just as we'd expect.

```lean4-diff
- lid := by intro α sig β f; 
+ lid := by intro α sig β f; unfold drop

 1 goal
 α : Type
 sig : Signal α
 β : Type
 f : Signal α → β
- ⊢ now (f <$> drop sig) = f sig
+ ⊢ now (f <$> fun n n' => sig (n + n')) = f sig
```

For definition unfolding we've been using `unfold foo` and `simp [foo]`
interchangeably. `unfold drop` performs _delta conversion_ on the `drop`
identifier, replacing `drop sig` with `(fun s => fun n n' => s (n + n')) sig`
wherever the identifier appears.  Then, beta reduction can proceed naturally,
producing `fun n n' => sig (n + n')` as we see in the goal.

But, `simp [drop]` yields a `'simp' made no progress` error and the goal
remains unchanged.  My mental model was that `simp [drop]` was sugar for
`unfold drop; simp`, but clearly not.  

::: margin-note
Since you can think of `simp` as holding a set of possible simplifications, the
order that one lists the additional steps within the brackets doesn't in fact
matter.
:::
What it _actually_ does is add `drop s n n' = s (n + n')` as a possible
simplification step, which the tactic will use internally to try and pare down
the goal.  But, we're only partially-evaluating `drop sig`, so the rewrite
fails without concrete `n` and `n'` arguments, and so `simp` leaves us stuck.

So, here's my complete implementation of the `lid` proof, which uses `unfold`
for `drop` but `simp` elsewhere, and concludes with simplifying a `0 + n`
subexpression:

```lean4
  lid := by intro α sig β f; unfold drop; simp [now, Functor.map, Nat.zero_add]
```

### right identity proof: point-free equality proofs need `funext`

Okay, what about the _right identity_?  We are meant to prove `now <$> drop sig
= sig`.  Since `sig` is a `Signal`, which is implemented in terms of a
function, we musn't forget to use _functional extensionality_ in order to turn
a "prove functions equal" proof into a "for all inputs to the functions, their
outputs are equal" one.

So, so far we have:

```lean4
  rid := by intros α sig; funext t

1 goal
α : Type
sig : Signal α
t : Time
⊢ (now <$> drop sig) t = sig t
```

As before, we have a partial evaluation of `drop` in the goal, so at a first
glance one might think we would be stuck in the same way as before.  However!
Take a look at some intermediary simplifications:

* If we simplify away the `<$>`, `(now <$> drop sig) t` becomes `now (drop sig t)`;
* If we simplify `now`, `now, (drop sig t)` becomes `drop sig t 0`.

This proof can simplify down to a call to `drop` that _isn't_ a partial application!
So, if we simplify `drop`, we're left with `sig (t + 0) = sig t`, which a another
theorem about the `Nat`s will discharge.

```lean4
  rid := by intros α sig; funext t; simp [now, Functor.map, drop, Nat.add_zero]
```

### associativity proof: `rw` pattern matching doesn't work on bound variables

Okay, the final one: `extend (extend wa f) g = extend wa (fun wa' => g (extend
wa' f))`.  

* To use the `rw` tactic, which consumes an equality theorem and rewrites one
side of the equation with another, all variables in the rewrite need to be _free_
and not bound as function arguments.

## Bridging refinements with indexed (co-)monads

Let's put aside `Functor` for the moment and think about monadic stateful
programs, like we did at the start of the series.  Here's how I might implement
a plain old monad typeclass:

To make a valid instance of this `Monad`, we need to supply the implementations
of `pure` and `bind`, as well as proofs that the monad laws hold.  Here's how
we might do this for a datatype that looks an awfully lot like `Maybe a`:

{% lean "LtlFrp/Structures.lean", "monad_ex" %}

Monads are all about encoding a piece of computation, just like our signal
transformers that we defined in terms of `<$$>`, so when it comes to what
_indices_ we might expect an indexed Monad to have, well, a natural choice
might be to have two: one for the `pre`condition that must hold before the
computation takes place, and the `post`condition for what must hold afterwards.

## Events are _monadic_, actually

Back when we defined `Event`s we made them part of Lean's `Functor` typeclass.
We hinted at a bit more generality than what's there, 

## Events can be _indexed_ monads, actually

A logical proposition with a quantifier is shaped like "for all x, ..." or
"there exists an x, such that ...".  Recall that, if we unfolded the FRP
definitions of `Signal` and `Event`, we'd eventually end up with the `always`
and `eventually` LTL primitives, a:

{% lean "LtlFrp/LTL.lean", "always" %}
{% lean "LtlFrp/LTL.lean", "eventually" %}


---
layout: post.njk
title: "Reactive Programming in Lean 4"
date: 2026-03-05
tags: [post, lean, reactive-programming]
excerpt: "Extending Lean's dependent type system to reason about reactive programs"
draft: true
---

Over the holidays I spent a bunch of time seeing how far we could push Lean's
type system and built-in theorem prover to reason about everybody's
[least-favourite interview problem](/posts/proving-the-coding-interview-lean).
We actually had a lot to say about that, but Fizzbuzz is not exactly
representative of most programs out there in the world: apart from the argument
to the function, it doesn't react to user input or other external stimuli, is
stateless, and certainly has no notion of concurrent parts coordinating and
operating in tandem.

For this next series, I'd like to build up to verifying programs that _do_ have
these properties.  As before, we'll start simple and see what mechanism we need
to build up.

## Transformational and Reactive Programs

Certainly nobody reading this blog needs to have algorithms defined for them.
Instead, I'll use terminology from [Harel and
Pnueli](https://www.state-machine.com/doc/Harel85.pdf) and assert that Fizzbuzz
was a _transformational_ program: it consumes some input, chugs away for
awhile, and ultimately produces some final output.  We usually just call
transformational programs "programs", and if you're a functional programmer or
PL person, you might even call a function "a program", since, hey, it certainly
fits the description!

When we verified our Fizzbuzz function-slash-program last time, we stated
correctness in terms of the relationship between its input to its output;
recall that we proved the length of `fizzbuzz n` was `n`, and a lot of facts
about how our helper `fb_one i` function's output varied as `i` changes.

A _reactive_ program is different.  Reactive programs are non-terminating and
respond to external _events_ or _signals_ acting upon it.  Most programs we
actually care about these days, be it a GUI program, a web server, an AI agent
responding to calls from a model, are reactive.  Harel and Pnueli have a
delightful figure contrasting the two: transformational programs are the usual
black box with input arrows going in one side and output arrows going out the
other, whereas reactive programs are "black cacti", with input and output
arrows spiking all around the box.

::: margin-note
Technically we can define Lean functions as `partial`, but that limits their
use in types and proofs, so we'll see a different approach soon enough.
:::
That non-terminating aspect is a problem for us, because _total_ functions must
terminate on all inputs, so it isn't obvious how to write something like an
event loop function in Lean.  This is a common requirement for dependent types:
terms that appear in types must be total in order for the type system's logic
to be consistent.  (To see why, remember that contradictions derive from trying
to prove `False`, which is a type with no values of that type.  But,
what could the return type of the function `def loop x = loop x`?  Well, it
never produces a value at all, so any return type is just as good as any other;
so, it's not incorrect to say that `loop` returns type `False`! And, since
we've seen, `False` proves anything, non-terminating computation punches a hole
in our logic.)

So, clearly, writing and proving properties about reactive programs is going to
be a lot different tnan what we've done before.

## Our first reactive program

::: tip
* _Anna_: Are you sure you pressed the right button?
* _Gunther_: I do not make mistakes of that kind!
* _Anna_: Your hand might have slipped.
* _Gunther_: No, I wanted orange. It gave me lemon-lime.
* _Anna_: The machine would not make a mistake.

-- evesdropped breakroom conversation from [Deus Ex
(2000)](https://www.youtube.com/watch?v=hxVPPy5w9NA)
:::

::: margin-note
[Geographically-speaking](https://archive.nytimes.com/ideas.blogs.nytimes.com/2008/09/11/the-soda-vs-pop-map/),
I refuse to say "soda machine".
:::
To get our bearings, let's implement one of the
[textbook](https://mitpress.mit.edu/9780262026499/principles-of-model-checking/)
examples of a reactive system in Lean, a vending machine (VM) that sells cans of
pop.  A VM has a bunch of state: it's got some number of cans of pop (let's say
two, to keep things straightforward), some number of coins that have been
inserted, and zero or one cans of some pop flavour in the dispenser.

### A Vending Machine's State

In Dafny we might write this as a class, but a plain old structure will do for
us in Lean:

::: margin-note
We saw `deriving Repr` in earlier posts - this is equivalent in Rust to `impl
ToString`. 
:::
```lean4
inductive Flavour where
  | Orange
  | LemonLime
deriving Repr

structure VMState where
  coins: Nat
  dispensed: Option Flavour
  numOrange : Nat
  numLL : Nat
deriving Repr
```

Suppose any given vending machine starts fully stocked, with no coins in the
hopper nor can in the dispenser:

```lean4
def init : VMState := { 
  coins := 0, dispensed := none, numOrange := 5, numLL := 5 
}
```

### A Vending Machine's Actions

We've defined the nouns for a vending machine.  What about the verbs?

There are probably lots of things a vending machine does that are strictly
internal: the chiller pump needs to turn on and off to keep the drinks cold,
for instance.  We're going to abstract away purely-internal actions and focus
exclusively on events that come in from the outside world.  This way, the
"black cactus" remains opaque.

I can think of a few external events:  A customer can drop a coin in the slot,
press one of the "select flavour" button, and can take a can out of the
dispenser.  I suppose the machine can be restocked by the owner, too.

```lean4
inductive VMAction where
  | DropCoin
  | Choose : Flavour → VMAction
  | Restock
  | TakeItem
deriving Repr
```

This sum type's constructors take no argument, except for `Choose`, which can
either be a `Choose Orange` or `Choose LemonLime`.

We now need to connect these two data definitions in order to write a program
over them.

### Acting on a State with the vending machine's operational semantics

We probably all have a rough intuition of what an action should do to a state
here: `Choose`ing `Orange` should decrement `numOranges` and place an `Orange`
in the dispenser.  Let's write the function that does this.

For this function, we clearly need a `VMState` and a `VMAction`, resulting
in a new `VMState` depending on the given action:

::: margin-note
If you learned programming from the [How To Design Programs](https://htdp.org/)
curriculum, you'll recognise this as the template for functions that consume a
`VMAction`.  We'll see a lot of functions shaped like this, unsurprisingly.
:::
```lean4
def vmStep (s : VMState) (a : VMAction) : VMState :=
  match a with
  | .DropCoin  => --TODO
  | .TakeItem  => --TODO
  | .Choose f  => --TODO
  | .Restock   => --TODO
```

I've called this function `vmStep` because its purpose is to encode one step in
the vending machine's operation.  The ten dollar computer science term for this is
the system's _small-step operational semantics_. 

Small step semantics are ubiquitous in the study of programming languages:
Language designers use them to formally describe how programs evaluate: here,
the state would probably include all the in-scope variables, and an action
might involve taking one step of evaluating an expression (say, simplifying 
`1 + 2 + 3` to `3 + 3` and then to `6`).  Small-step semantics can also be used to
define safe program transformations: the
[CompCert](https://xavierleroy.org/publi/compcert-CACM.pdf) C compiler used
operational semantics of its intermediary representation to prove that
optimization passes didn't change the semantics of the program being compiled.

OK, anyway, let's fill in `vmStep`.

:::margin-note
50 cents for a can of pop?  _In this economy??_
:::
```lean4
def vmStep (s : VMState) (a : VMAction) : VMState :=
  match a with
  | .DropCoin        => { s with coins := s.coins + 1 }
  | .TakeItem        => { s with dispensed := none }
  | .Choose .Orange  => { s with
    coins     := s.coins - 2,
    numOrange := s.numOrange - 1
    dispensed := some .Orange,
  }
  | .Choose .LemonLime => { s with
    coins     := s.coins - 2,
    numLL     := s.numLL - 1
    dispensed := some .LemonLime,
  }
  | .Restock         => init
```

Last time, we spent a lot time thinking about what program values were
well-typed but in practice invalid (recall all the ways a `Vector String n`
could _not_ encode the first `n` values of the Fizzbuzz problem).  Before
proceeding, something to think about: the `VMState` type permits us to construct
a vending machine with any (nonnegative) number of cans of each flavour, but,
could there ever be a sequence of actions that leads us to having 6 `Orange`s
in stock.  The idea of which states are _reachable_ from a given starting state
will be, as we'll see, super-important down the road.

::: margin-note
Technically, we'll need one more piece, but who's counting?  You might enjoy
pausing and pondering what that final piece might be before we proceed - one
big hint: it relates to that notion of reachability and validity...
:::
These three pieces - our state, action, and step definitions - define the
_abstract machine_ for the vending machine.  All we need now is a way to write
down and execute programs on this abstract machine and we'll have completed our
first reactive Lean program!

## The State Monad, revisited

In the previous series we used monadic programming to mimic mutation in an
otherwise pure functional program; let's do the same thing here!  Since vending
machine programs -- sequences of actions -- are inherently stateful, operating
on the machine itself, having the ergonomics of the state monad to compose
operations together sounds like a useful way to program. 

Remember our old friend, the State monad?  If not, that's okay, [From Zero to
QED](https://sdiehl.github.io/zero-to-qed/10_effects.html) has got your back.

The relevant bits for us: `StateM σ α` mimics mutation of a value of type `σ`
(sigma, for "s"tate) that ultimately produces a value of type `α` (alpha, for,
"a"h, I don't have a good mnemonic for this one).  Clearly, sigma is going to
be `VMState`, our value under mutation, and alpha can vary depending on what
output we want a given abstract machine program.

### Stepping within `StateM` with monadic actions

Let's build a tiny bit of mechanism to take a step within a `StateM VMState`,
given some action.  We call this _lifting_ `vmStep` into the State monad:

::: margin-note
I could have one-lined this as `modify (vmStep · a)`, if I was feeling
ambitious, too.
:::
```lean4
def perform (a : VMAction) : StateM VMState Unit := do
  let s ← get
  let s' := vmStep s a
  set s'

#eval (perform .DropCoin).run init -- ((), { coins := 1, dispensed := none, numOrange := 5, numLL := 5 })
```

Here, stepping has become a _monadic action_ which involves two effectful
operations: `get`ing the current state and calling `vmStep` with that state,
and subsequently `set`ting that new `VMState` as the monad's state value.  The
standard naming convention is for `s` to be the current state and `s'` to be
the new state and I've reflected that here.  Since this is an effectful
operation, it doesn't make sense for the final result to be anything other than
`Unit` (akin to a setter in Java returning `void`).

We can run our monadic operation with our `init` state, and see that we are
handed back a tuple, containing `()` (our returned value of type `Unit`) and
the final state of the vending machine: as expected, it has a single coin in it.

Let's drop in two coins and make a pop choice: as expected, zero coins are left
in the hopper, and a can has been dispensed to us:

```lean4
def getOrange : StateM VMState Unit := do
  perform (.DropCoin)
  perform (.DropCoin)
  perform (.Choose .LemonLime)

#eval getOrange.run init -- ((), { coins := 0, dispensed := some (Flavour.LemonLime), numOrange := 5, numLL := 4 })
```

### A new monadic action to return the `Flavour`

You probably notited that `getOrange`'s monad's return type is `Unit` - really,
this should be a `Flavour`.  The problem is that we `perform (.TakeItem)`, it
gets removed from the `VMState` but we lose track of it.  We should create another
monadic action that pulls out the contents of `dispensed` before taking that step.

::: margin-note
A bit more monadology: `pure x` just wraps the literal value `x` in the
relevant monad. So, here, we're going from a `Option Flavour` to a `StateM
VMState (Option Flavour)`.
:::
```lean4
def take : StateM VMState (Option Flavour) := do
  let s ← get
  perform .TakeItem
  pure s.dispensed
```

That `take` returns an `Option Flavour` suggests the starting state `s` might
not have had a flavour dispensed at some point in the past.  In order to type
this as `StateM VMState Flavour` , we'd have to have some sort of precondition
on bindings with `take` of the form "at some point in the past, we needed to
have dispensed a can, and at no point between then and now did we take the can
out".  

It's not clear how we could even express a proposition like that, saying
nothing of validating it here, but stay tuned...

We can now complete the implementation of `getOrange`, which encodes the
effectful operations of dropping in two coins, choosing a flavour, and taking
it out of the machine.  The final state is the same as before but now our
output value is the expected flavour.  Excellent!

```lean4
def getOrange : StateM VMState (Option Flavour) := do
  perform (.DropCoin)
  perform (.DropCoin)
  perform (.Choose .LemonLime)
  take

#eval getOrange.run init -- (some (Flavour.LemonLime), { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```

## Prohibiting invalid steps requires proving validity of valid steps!

There's nothing prohibiting us from taking steps that don't make sense: for
instance, do we actually need to drop in coins to take a `LemonLime`?

```lean4
def getOrange : StateM VMState (Option Flavour) := do
  perform (.Choose .LemonLime)
  take

#eval getOrange.run init -- (some (Flavour.LemonLime), { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```

It's clear that we have to revisit our step function to only allow actions to
be taken on a state if the state satisfies some _logical precondition_.  So,
let's start writing such a function:

```lean4
def validAction (s : VMState) (a : VMAction) : Prop := 
  match a with
  | .DropCoin  => --TODO
  | .Restock   => --TODO
  | .TakeItem  => --TODO
  | .Choose f  => --TODO
```

Something worth being explicit about here: this function is dependently-typed!
In other languages, at runtime, we'd compare the `VMAction` against the current
`VMState` and return a Boolean.  But, returning a Prop means the typechecker
can do some verification _at compile time_.

Let's fill out `validAction`: for a given `a`, what precondition to be true
about `s`?  Your vending machine might differ from mine, but as a first pass,
here's what I think needs to hold:


* You can always feed a coin into the machine.  (This means our hopper is
  infinitely large, but maybe that's okay for an abstract machine.)
* Similarly, you can always restock a machine back to its `init`ial state.
* You can take an item from the dispenser only if it holds an item.
* You can choose a flavour only if you've fed enough coins into the machine to
  pay for it (both flavours cost two coins).

::: warning
One of the fundamental problems with software verification is even writing down
the specification that the implementation needs to adhere to.  For `Fizzbuzz`
we could just read the problem statement off and translate it into `Prop`s, but
already we can see that "what is the correct behaviour of a vending machine"
becomes murkier; you and I could write two different but probably reasonable
specifications.

You should definitely pick apart this spec and see if there are any holes you
can spot.  Next time we'll fix those up.
:::

OK, so let's write this spec.  Each arm of the `match` will return the
appropriate logical proposition (which are all different types of type `Prop`)
(remember, this is not the same as evaluating a boolean expression at runtime):

::: margin-note
As before, I annotated this function with `@[simp]` so that when we're in
tactics mode and want to simplify our goal, we'll automatically have the
definition unfolded for us.
:::
```lean4
@[simp]
def validActionV1 (s : VMState) (a : VMAction) : Prop :=
  match a with
  | .DropCoin      => True
  | .Restock       => True
  | .Choose Orange => s.coins >= 2 ∧ s.num_orange > 0
  | .Choose LL     => s.coins >= 2 ∧ s.num_ll > 0
  | .TakeItem      => Option.isSome s.dispensed
```

Let's remember how dependent types work here: if we have some `s` and some `a`,
the dependent type `validActionV1 s a` encodes what needs to be true in order
for the step to be valid.  So, our step function better consume a _hypothesis_
of such a type as evidence that we're allowed to take this step:

::: margin-note
This `H` argument might be a good candidate for an _implicit argument_ since in
some cases Lean can synthesize the right argument.  I'm going to leave it
explicit, though, since I think it'll make things more confusing down the road
when we start writing complicated proofs.
:::
```lean4
def vmStep (s : VMState) 
           (a : VMAction) 
           (H : validActionV1 s a) -- NEW: evidence that we have confirmed that a can step s
           : VMState :=
  match a with ...
```

In the editor, if you're following around, it's worth taking a moment and
seeing how the context window changes as you navigate around the body of
`vmStep`.  If your cursor is in the `DropCoin` arm of the `match`, you will
have `H : validActionV1 s VMAction.DropCoin` in your context, and it'll change 
as you move between `match` arms.

## Statically proving steps are valid

The power of dependent typing is this: If we can't write a proof of
`validActionV1 s a`, Lean won't let us even write down a call to `vmStep` with
those arguments!  Let's see this in action with the "drop two coins, choose, take"
example from before.

(I'm deliberately _not_ using our monadic API here, because as we'll see, it
adds some complications; and, it's always useful to see the "unfolded" states
explicitly anyway and not get lost in the weeds of abstraction.)

Here's the scaffolding for this "abstract machine program".  Lean needs a proper
proof for each of the steps, which we'll fill in as we go.

```lean4
#eval
  let s0 := init
  let s1 := vmStep s0 .DropCoin (by sorry /- TODO -/)
  let s2 := vmStep s1 .DropCoin (by sorry /- TODO -/)
  let s3 := vmStep s2 (.Choose .LemonLime) (by sorry /- TODO -/)
  let s4 := vmStep s3 .TakeItem (by sorry /- TODO -/)
  s4
```

### Proving `DropCoin` steps is simple

When we drop into tactics mode in the `vmStep s0 ...` call, what's in our
context?

```lean4
#eval
  let s0 := init
  let s1 := vmStep s0 .DropCoin (by ...

1 goal
s0 : VMState := init
⊢ validActionV1 s0 VMAction.DropCoin
```

A classic proof context that we've seen many times before.  `unfold`ing
seems like a reasonable thing to do:

```lean4
#eval
  let s0 := init
  let s1 := vmStep s0 .DropCoin (by unfold validActionV1; -- NEW
  ...

1 goal
s0 : VMState := init
⊢ match VMAction.DropCoin with
| VMAction.DropCoin => True
...
```

Simplifying the `match` statement leaves us with having to "prove" `True`,
which is the simplest possible thing to prove.  Following up the `unfold` with
`simp` gets the job done for both `DropCoin`s.

Since we annotated `validActionV1` as `@[simp]`, we can elide the explicit
unfolding, and we're done for those steps.

```lean4
#eval
  let s0 := init
  let s1 := vmStep s0 .DropCoin (by simp) -- NEW
  let s2 := vmStep s1 .DropCoin (by simp) -- NEW
  ...
```

### Proofs of valid `Choose`s necessitate arithmetic reasoning

Unfortunately, proving that we can `Choose` after two coin drops requires a
bit more work.  After we simplify, we see we have a numeric inequality to prove:

```lean4
#eval
  let s0 := init
  let s1 := vmStep s0 .DropCoin (by simp)
  let s2 := vmStep s1 .DropCoin (by simp)
  let s3 := vmStep s2 (.Choose .LemonLime) (by simp; -- NEW
  ...

1 goal
s0 : VMState := init
s1 : VMState := vmStep s0 VMAction.DropCoin True.intro
s2 : VMState := vmStep s1 VMAction.DropCoin True.intro
⊢ 2 ≤ s2.coins
```

::: margin-note
This is why I didn't write this example using the monadic API: states are not
threaded though explicit `let` bindings but are instead _implicit_; when a
state does appear its originating context is lost.

There's a dependently-typed variant of monads called [indexed
monads](https://kseo.github.io/posts/2017-01-12-indexed-monads.html) which
might help here, but I'm not sure, and that's a topic for another time anyway.
:::
We know, of course, that `s2.coins = 2`, because we can read it off from the
first two steps.  It turns out that in this specific case, Lean can too! In
previous examples, `s2` might have been an argument to a function - when it's
passed into that function, the original source of how `s2` was defined was
lost, so Lean wouldn't be able to unfold the definition of s2 back to its
original definitions.  Here, though, it _can_, because it's defined in terms
of `s1`, which is defined in terms of `s0`, which is just `init`.  So, Lean
has all the states it needs in scope to see that by the time we get to `s2`,
`coins` has been incremented twice.

So, in this case, both we _and_ Lean know that `s2.coins = 2`.  So, ultimately,
our goal is `2 <= 2`, and of course there's a theorem for that:

::: margin-note
Since applying theorems in tactics mode is the same as calling the theorem like
a function outside tactics mode, `by apply thm arg` can be simplified to just
`thm arg`.
:::
```lean4
#eval
  let s0 := init
  let s1 := vmStep s0 .DropCoin (by simp)
  let s2 := vmStep s1 .DropCoin (by simp)
  let s3 := vmStep s2 (.Choose .LemonLime) (by simp; apply Nat.le_refl 2) -- NEW
  ...
```

### Proofs of `TakeItem` are trivial, too

For a similar reason to above, Lean can see through the previous definitions
and can see that `Option.isSome s3.dispenser` is True.  Proving `True = True`
is as simple as using the first tactic we ever learned, which completes all
our proofs, and Lean is happy to step through our actions and produce the 
final state we expect:

::: tip
```lean4
#eval
  let s0 := init
  let s1 := vmStep s0 .DropCoin (by simp)
  let s2 := vmStep s1 .DropCoin (by simp)
  let s3 := vmStep s2 (.Choose .LemonLime) (Nat.le_refl 2)
  let s4 := vmStep s3 .TakeItem (by rfl)
  s4
```
```
{ coins := 0, dispensed := none, numOrange := 5, numLL := 4 }
```
:::

## Refining our monadic API

If you've been typing along, you've probably noticed that our monadic API
doesn't typecheck anymore - we have to thread our proof of valid step through
`perform`.

## Towards writing _temporal_ specifications

## Next time...

---
layout: post.njk
title: "LTL-in-Lean part 2: reasoning about executions"
date: 2026-03-05
tags: [post, lean, reactive-programming]
excerpt: "Get in losers, we're doing temporal logic"
draft: true
---

## Traces, concretely

Let's get our bearins by accumulating finite traces from our monadic API. 

Remember that `Trace`s are conceputally infinite in length, so when we actually
execute a series of actions, we're actually producing a _trace fragment_. (This
is sometimes called a _trace prefix_ or just a finite trace.)  Fragments will
be produced by executing our TSM monad - the only thing we have to do to make
this happen is to accumulate the states we transition to.

The thing is, `TSM` now has _two_ interpretations: the "execute a sequence of
actions, producing a final state or an error" one, and also the "just give me
all the sequence of states".  These interpretations aren't fundamentally different
from each other, so we could try and maintain a stateful list of transitioned
states, or maybe use the
[Writer](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Control/Monad/Writer.html)
monad, which allows us to mix in "emitting log entries"-like behaviour.  

```lean4
import Mathlib.Control.Monad.Writer

...
abbrev Fragment := List VMState
abbrev TSM α := WriterT Fragment (StateT VMState (Except String)) α
```

`TSM` is three monads stacked together, which is kind of convoluted, but
we only need ot know that this monad now imbues computation in `TSM`
with a new `tell` function, which records `VMStates` as we come across them:

:::margin-note
A sufficiently-complicated monad transformer stack actually makes it _easier_
to see why monads are an interesting way to program: every monad can be seen as
introducing a new "language feature": `State` introduces, well, mutable state,
`Except` introduces exception raising, and now `Writer` introduces output
logging, none of which are obviously present in a pure functional language!
:::
```lean4
def perform (a : VMAction) : TSM Unit := do
  let s ← get
  if h : validAction s a then
    tell [s] -- NEW: remember that we saw [s]
    let s' := vmStep s a h
    set s'
  else Except.error s!"Invalid action {repr a} in state {repr s}"

...

#eval getOrange.run init 

Except.ok (
  (LemonLime,
  [{ coins := 0, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 1, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 2, dispensed := none,           numOrange := 5, numLL := 5 },
   { coins := 0, dispensed := some LemonLime, numOrange := 5, numLL := 4 }]),
 { coins := 0, dispensed := none, numOrange := 5, numLL := 4 })
```

With a little helper, we can pull out only the fragment from a computation.
In fact, while we're doing so, why don't we turn that fragment into a proper
trace:

::: margin-note
Here, we make the trace well-defined by saying it's just hanging for all points
in time after the final transition.  You might think another way to do this
would be to just loop back to the first action and repeat the seqeuence over
and over again, but this wouldn't work for this trace; we'd eventually run out
of pop cans to dispense so we'd get stuck.

You may disagree with my choice of return value of `.error`: since we will only
use this for a few examples, feel free to change it to a `panic!`, after you
solve the type error that it creates for you >:)
:::
```lean4
def getFragment (init : VMState) (tsm : TSM σ) : Trace VMState :=
  match (tsm.run init) with
  | .ok ((_, frag), final) =>
    (fun n => if h : n < frag.length then frag.get ⟨n, h⟩ else final)
  | .error e => (fun _ => init)

def orangeTrace := getFragment init getOrange
```

### Our first proposition

Here's a useful thing to prove: in this specific execution trace, is a can
ever dispensed?

## Traces, abstractly


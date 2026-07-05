---
layout: post.njk
title: "FRP in Lean: Hoare Logic and loop invariants redux"
date: 2026-06-30
tags: [post, lean, reactive-programming, frp, hoare-logic]
excerpt: "New program logic just dropped!"
series: lean-ltl
series_title: "Hoare Logic"
draft: true
---

Last time we implemented a series of combinators that transformed not just data
values that might flow through a functional reactive program, but invariants
about that data.  Recall our `RSignal.map` function:

```lean4
def map
  {pre: α → Prop}
  {post: β → Prop}
  (f: {a: α // pre a} → {b : β // post b})
  (s: □ α // pre)
  : □ β // post := ...
```

Given a precondition over the input type `a` and a postcondition over the
output type `β`, and a mapping function that turns an `a` that satisfies `pre`
into a `β` that satisfies `post`, we can turn a signal of `a`s where `pre` is a
safety property into a signal of `β`s with -- yes, you guessed it -- `post` as
a safety property.  (The other combinators we wrote had a similar sort of
shape: consume a refined signal and somehow transform its value and safety
property).

Someone pointed out that this looks a lot like [_Hoare
logic_](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare.html),
which is a classic way of reasoning about sequential, imperative, mutable
programs.  (This is in contrast to what we've been doing so far: reasoning
about concurrent, functional programs!) I thought it might be fun to see how
far we can connect Hoare logic to our FRP library. I have a suspicion that
we'll get most, but not _all_ of the way there, and it'll help reveal if
there's any gaps in our library.

## Warmup: Faking `RSignal` as a Functor

We discussed last time that we can't make `RSignal` an instance of the
typeclass `Functor`, because `RSignal` has a dependent type `(α : Type) → (α →
Prop) → Type`, which won't fit `Functor`'s `Type → Type` shape.  We can at
least, though, add a custom operator to replace the `<$>` we don't get to use:

::: margin-note
You should attempt to do the same thing with `Applicative`, by implementing a
`infixr:60 " <**> " => RSignal.map2` and some definition of `pure`, and see
where you get stuck.
:::
```diff-lean4
 -- Unrefined Signals are truly Functors and Applicatives...

 instance : Functor Signal where
   map := Signal.map -- e.g. <$>

 instance : Applicative Signal where
   pure := Signal.const
   seq sf sx := Signal.map2 (· ·) sf (sx ()) -- e.g. <*>

+ -- ... RSignals can have identically-implemented operators, but
+ -- they can't be expressed through the same typeclass interface.
+ infixr:100 " <$$> " => RSignal.map
```

Going forward, I'll use `<$$>` in place of `RSignal.map` whenever possible.

## The essence of Hoare logic, in one formula

We'll see exactly what sorts of program behaviour we can express in Hoare logic
soon enough, but the most important part of the logic is the _Hoare triple_.
It's, as you might expect, a logical expression with three parts:

::: tip
The Hoare triple `{P} c {Q}` is made up of a precondition `P`, a postcondition
`Q`, and a "command" (a statement in some imperative programming language) `c`.
A Hoare triple is valid if, under the assumption that `P` holds before `c`
executes, `Q` will hold after it executes.
:::

A classic Hoare triple (which I'm borrowing from the _Software Foundations vol
2_ chapter linked above might be `{i == 0} i++ {i == 1}`: if `i` was `0`
before incrementing it, it'll be `1` after.  Another valid triple with the same
precondition might be `{i == 0} i++ {i > 0}` - incrementing a zero-value
variable will leave it as a positive-valued variable.  One more: `{10 < 20} i++
{j == 99}`: here, neither the precondition nor the postcondition state anything
about `i`, and the latter refers to a totally different (presumably in-scope)
variable!

::: margin-note
Is the proposition we just wrote down valid or not?  Probably depends on some
factors about `i` that we haven't explicitly stated in this example.  It's
worth pausing and ponding a situation where that proposition is valid and one
where there's a counterexample.
:::
Just like how we embedded temporal logic in Lean's type theory, we could do the
same here, too: `∀ x, {i == x} i++ {i == x+1}` is a proposition that
quantifies in the host logic to make a statement in the embedded logic.

This is a very different kind of logic from LTL!  A command can be more
structured than just a single statement like `i++`; we'll see that there are
Hoare logic rules for loops, conditionals, variable declarations; anything you
need, really, in a straightforward imperative programming language.  The hope
is that if our FRP library "spans" the space of Hoare logic primitives, then we
ought to imagine our set of FRP combinators is expressive enough to implement
"realistic imperative programs" in.

Remember the pop machine example from way back in the first post, where we
implemented a monadic API to give the illusion of imperative programming?
`getOrange.run`, starting with a fully-stocked machine, would ultimately
dispense an orange pop, after some internal mutations: We could write the Hoare
triple for this operation, perhaps, like:

```lean4
-- imaginary Hoare triple syntax
{ numOrange > 0 } getOrange.run init { result := some Orange }
```

We could do the same for each individual operation in `getOrange`, too:

::: margin-note
Notice that the postcondition from the previous statement feeds into the
precondition of the next statement.  We haven't talked about how we might come
up with "the right" pre- and post-conditions, but hopefully you agree that the
ones I've chosen are at least decent!
:::
```lean4
{ numOrange > 0 }              DropCoin      { numOrange > 0 ∧ coins = 1 }
{ numOrange > 0 ∧ coins = 1 }  DropCoin      { numOrange > 0 ∧ coins = 2 }
{ numOrange > 0 ∧ coins = 2 }  Choose Orange { dispensed := some Orange }
{ dispensed := some Orange}    take          { result := some Orange }
```

::: margin-note 
Hey, I know a decent [Dafny tutorial](/posts/proving-the-coding-interview/) or
[two](/posts/proving-the-coding-interview-lean/), if you're looking for one!
:::
Hoare logic is also at the essence of how Dafny weaves logical statements about
different parts of a program.  Here's a Dafny method that ought to feel
familiar, even if the syntax strictly speaking might not:

```dafny
method increment(x: int) returns (y: int)
  requires x == 0      // precondition: P
  ensures y > 0        // postcondition: Q
{
  y := x + 1;
}

... 
z := 0
x := increment(z)      // Pre: z = 0; Post: x > 0
```

For Dafny to "typecheck" a program that calls `increment`, the precondition
regarding the input argument (or any other piece of program state) has to be
provably satisfied at all call sites; symmetrically, Dafny will in turn expose
the postcondition for the parts of the program following the function call.

In FRP-land, of course, we don't have variable assignments in the imperative
programming sense, but a Signal _does_ have the property that it's "a box that
holds a value that can change over time".  Hoare
[called](https://www.cs.cmu.edu/~crary/819-f09/Hoare69.pdf) the idea that "in
an assignment `x := y`, whatever proposition `P` is true about the right-hand
side of the assignment will also be true about the left hand side" the _axiom
of assignment_.  The Hoare triple encapsulating this slightly convoluted
English sentence might read `{ P(y) } x := y { P(x) }` for some well-chosen
`P`s.  This means that we're invoking the axiom of assignment whenever we
declare a new Signal value.

```lean4
def incr (i : {i : Int // i = 0}) : {i : Int // i > 0} := ...
def sqrt (i : {i : Int // i > 0}) : {i : Int // i >= 0} := ...

def z : □ Int // (· = 0)  := RSignal.const ⟨0, by lia⟩
def x : □ Int // (· > 0)  := incr <$$> z
```

Next: Here's a call of `increment` in some larger Dafny program:  (I haven't
written a square root method, and I'm not sure if the Dafny standard library
has one, but you can probably imagine a caller's Hoare triple might be
something like `{x >= 0} sqrt(x) {sqrt(x) >= 0}`.)

::: margin-warning
For now, let's gloss over the fact that we have an implicit weakening step that
turns `z > 0` into `z >= 0`.  This is trivial for Dafny's solver but we'd have
to use `RSignal.weaken` manually.
:::
```dafny
// sequencing...
let z := 0;          // z := 0
z := increment(z);   // z > 0
z := sqrt(z);        // z >= 0

// ... is composition.
z := sqrt(increment(0)) // z >= 0
```

Here we are _sequencing_ operations on some program state, which is the same
here as composing the two functions together.  Lean lets us write the same
program in FRP style: 

```lean4
-- sequencing of signals...
def z :  □ Int // (· = 0)  := RSignal.const ⟨0, by lia⟩
def z2 : □ Int // (· > 0)  := incr <$$> z
def z3 : □ Int // (· >= 0) := sqrt <$$> z2

-- ... is composition of signals.
def z4 : □ Int // (· >= 0) := sqrt <$$> incr <$$> z
```

This bring us to our first correspondence: composition of Signals is
Hoare logic's _sequencing rule_.

## Sequencing and composition

Here's the sequencing rule for Hoare logic: 

::: margin-note
This might be the first time we've seen [Genzen
notation](https://planetmath.org/gentzensystem), or sequent calculus, in this
series.  This is an _inference rule_; you read this by saying "if the
statements above the line hold, then the statement below the line holds".

Under Curry-Howard, an inference rule corresponds to a _function type_ whose
arguments have types of the statements above the line, and whose return type is
that which is below the line.
:::
::: tip
```
     {P} S1 {Q}    {Q} S2 {R}
    -------------------------- (hoare_seq)
          {P} S1; S2 {R}
```
The _sequencing rule_: Starting with two Hoare triples, each with their own
statement, and where the postcondition of the first is the precondition of the
second, it's valid to "toss out the middle proposition" if our Hoare command
becomes "execute the first statement, and then execute the second statement".
:::

In our example here, `z4`, our composition-of-signals, has an intermediary
proposition that gets hidden inside the composition.

As it happens, because `RSignal.map` maintains the _functor law_ `map (f ∘ g) =
map f ∘ map g` (even though it doesn't implement `Functor`, for reasons we
discussed last time), composing two refined functions and then lifting them
into a Signal gives the same result as lifting each function separately and
then compositing the two signals.  We can even prove they're the same function!

::: margin-note
I spent awhile trying to complete the `z4 = z5` proof before discovering a
reflexivity proof is enough.  I genuinely am not sure how Lean figures that out
with such a simple tactic, because I would have thought we'd have to manually
prove that `Signal.spilt` and `Signal.collect` are inverses, which we've never
actually done!
:::

```lean4
def z4 : □ Int // (· >= 0) := sqrt <$$> incr <$$> z
def z5 : □ Int // (· >= 0) := (sqrt ∘ incr) <$$> z
example : z4 = z5 := by rfl`
```

We can go deeper and state `hoare_seq` under Curry-Howard, the proof of which
is `∘`!

```lean4
def hoare_seq
  {P : StateProp α} {Q : StateProp β} {R : StateProp γ} :
  ((□ α // P) → (□ β // Q)) → ((□ β // Q) → (□ γ // R)) →
  ((□ α // P) → (□ γ // R)) := flip Function.comp
```

### Skip is a no-op

Before we move on from `map`, it's worth pointing out that Hoare logic
implements a so-called _skip rule_ for being able to state "a predicate is
preserved by a no-op": this is captured by the "command" being the identity
function:

```lean4
def hoare_skip : (□ α // P) → (□ α // P) := id
```

:::tip
```
      ------------------- (hoare_skip)
          {P} skip {P}
```

The _skip_ rule: Skip is akin to an empty statement (like `;` in C).  It's
always safe to skip, and doing so carries all preconditions ahead.
:::


## Conjunctions and conditionals

`RSignal.map`, ahem, mapped pretty cleanly onto the sequencing rule.  We might
expect `map2` to, as well, but we'll see the correspondence isn't quite so
exact; there are actually a few different Hoare logic rules that correspond to
a use of `map2`.  Which is cool!  `map2` is a general combinator and so we might
expect to be able to use it in a few different contexts.

The most straightforward interpretation of `map2` is that it's just the
multi-arity version of what we saw in `map`:  a Hoare command that requires
two inputs 

```lean4
def s1 : □ Int // (· = 5)  := RSignal.const ⟨5, by lia⟩
def s2 : □ Int // (· = 7)  := RSignal.const ⟨7, by lia⟩
def s3 : □ Int // (· > 10) :=
  RSignal.map2 (fun ⟨a, ah⟩ ⟨b, bh⟩ => ⟨a + b, by lia⟩) s1 s2
```

If we look at what's in our context in the body of the `fun`, we have,
unsurprisingly, both input signals' preconditions in scope:

```lean4
a : Int
ah : a = 5
b : Int
bh : b = 7
⊢ { c // c > 10 }
```

when we discharge the proof of `a + b > 10` via `lia`, the tactic's inequality
solver will somehow combine `ah` and `bh`.  This should suggest that `map2`
_conjoins_ signals.

There are a few ways we can make use of a joining step: implementing
conditionals is a pretty important one.  Here's the Hoare logic inference rule
for conditionals:

::: tip
```
       {C ∧ P} S1 {Q}    {¬C ∧ P} S2 {Q}
      ----------------------------------- (hoare_ite)
          {P} if C then S1 else S2 {Q}
```
The _conditional_ rule: given two statements that share a precondition `P` and
postcondition `Q`, but differ in that one's precondition satisfies `C` and the
other satisfies `¬C`, an if-then-else construct dispatches on the validity of
`C` to the appropriate statement, ensuring that `Q` holds either way.
:::

Here, our preconditions have an shared underlying `P` proposition and a `Q`
postcondition.  What's different between them is in that one branch, some other
`C` is true, and in the other it's false.  This rule lets us factor the `C` out
from `P`.

### A `Prop`-dependent `if-then-else` combinator

Let's start building an FRP combinator for signal switching: We'll clearly need
three propositions, `C`, `P`, and `Q`, and at a signal where at least we know `P`
holds.

```lean4
def RSignal.ite
  {P : StateProp α} {Q : StateProp β}
  (C : StateProp α)
  (sig : □ α // P)
  /- ... TODO: what else? -/
  : □ β // Q := sorry /- TODO -/
```

Of course, taking a `□ α // P` to a `□ α // Q` sounds like a job for `map`, but
the new wrinkle is how to involve `C`.

Suppose the interpretation of this combinator is "at each timestep", choose
between applying two functions depending on whether `C` holds at a given
moment.  Let's add those two functions to the signature:

::: margin-note
`thn` and `els` could be typed differently.  In particular, imagine if they
were `□ β // Q`s - this combinator would then let us dynamically switch between
two signals, depending on where `C` points us.  The downside there is that we
lose `C` being mentioned in those two signals' types, and so we lose the
preconditions on each that we get out of the Hoare rule.

You could also imagine `thn` and `els` being _signals of functions_, where at
each timestep we get a specific `α // (P a ∧ C a) → β // Q b` function to call.
This sort of time-varying transformation sounds super-general (and should make
you think of `map3` or applicative functors from last time) and maybe we'll
find use for this level of dynamism down the road.
:::
```diff-lean4
 def RSignal.ite
   {P : StateProp α} {Q : StateProp β}
   (C : StateProp α)
   (sig : □ α // P)
+  (thn : {a : α // P a ∧ C a}   → {b : β // Q b})
+  (els : {a : α // P a ∧ ¬ C a} → {b : β // Q b})
-  /- ... TODO: what else? -/
   : □ β // Q := 
+    let f a := sorry
+    f <$$> input
```

Let's see what the implementation for `f` looks like.  If we use a dependent-if
binding (which we've seen at some point in the distant past), then we're 90% of
the way there: `if h : C a.val` will bring `h: C a` and `h: ¬ C a` into the
context in the true and false branches, and then we can conjoin `a.property : P
a` and `h`, so long as we insist that `C` is a decidable proposition and not just
some arbitrary (possibly impossible-to-prove) proposition:

```diff-lean4
 def RSignal.ite
   {P : StateProp α} {Q : StateProp β}
-  (C : StateProp α)
+  (C : StateProp α) [inst : DecidablePred C]
   (sig : □ α // P)
   (thn : {a : α // P a ∧ C a}   → {b : β // Q b})
   (els : {a : α // P a ∧ ¬ C a} → {b : β // Q b})
-  /- ... TODO: what else? -/
   : □ β // Q := 
-    let f a := sorry
+    let f a := if h : C a.val then
+      thn ⟨a.val, And.intro a.property h⟩ else
+      els ⟨a.val, And.intro a.property h⟩
     f <$$> input
```

Here's `RSignal.ite` in action: maybe you recognise the _Syracuse function_ in
terms of a certain conjecture that it's connected to:

```lean4
-- On even positive input, divide by two
def syra_even : {n : Int // n > 0 ∧ n % 2 = 0} → {m : Int // m > 0} :=
  fun ⟨n, ⟨hPos, hEven⟩⟩ => ⟨n / 2, by lia⟩

-- On odd positive input, multiply by three, inc, divide
def syra_odd : {n : Int // n > 0 ∧ ¬ (n % 2 = 0)} → {m : Int // m > 0} :=
  fun ⟨n, ⟨hPos, hOdd⟩⟩ => ⟨(3*n + 1) / 2, by lia⟩

-- Make the signal well-defined for all positive inputs,
-- banishing the parity check from the signal's precondition
def syra : (□ Int // (· > 0)) → (□ Int // (· > 0)) :=
  hoare_if (· % 2 = 0) syra_even syra_odd

def positives : □ Int // (· > 0) :=
  Signal.collect (fun t => ⟨ Int.ofNat t + 1, by lia⟩)

-- We can take one step for all values from [1..11)
-- [2, 1, 5, 2, 8, 3, 11, 4, 14, 5]
#eval (List.range 10) |>.map (syra positives).val
```

That certain conjecture states that `syra`, from any starting value, will
eventually converge onto the value `1`.   The problem is this: The final
`#eval` expression takes a bunch of `Nat`s and steps one iteration of the
Syracuse function for each of them.  What we actually want, though, is to feed
the output of the `syra` signal back into itself for repeated iteration until
we reach `1`.  This means we need to enrich our FRP library's notion of 
control flow - good news, though, because Hoare logic has a looping primitive
that will help us design just that.

## Control flow and loop invariants

Hoare logic isn't limited to just simple statements like assignments and
mutations.  In fact, arguably the most important problem in modeling imperative
programs involves what invariants hold during control flow such as loops.  (If
you read the Dafny posts, you'll remember how much time we spent choosing the
right loop invariants!).

The Hoare logic inference rule for a `while` loop can be built up like this:
suppose we start with a loop like this, in the
[Blub](https://paulgraham.com/avg.html) language:

::: margin-note
Example from [Software Foundations Vol 2 Ch
3](https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html).  Did I
ever tell you that I fell in love with dependent-typed programming when
a friend nerd-sniped me to take Software Foundations Vol 1 on a very long
[VIA rail](https://www.viarail.ca/en) ride through Atlantic Canada?  I doubt
any author would ever read this post, but in case one ever does, thanks a lot.
:::
```bash
var I, Z : Nat
Z := 1
I := 0
while I < N do
    I += 1
    Z *= I
done
```

The backwards-branch that returns us to the `I < N` check is exactly what
we have to figure out how to express in FRP.

## The Hoare rule for while loops

What's always true when we enter the loop body?  Well, it better be the case
that if we entered the loop body, the conditional `I < N` evaluated to true, so
`I < N` would make a great precondition here.  By contrast, what's true when we
exit the loop body?  It might be the case that we've finished the final
execution of the loop and so the conditional no longer holds, or we're destined
to re-enter the loop body, in which case it's still true.  So, those great
preconditions would make very poor postconditions.

So, in principle, the triple `{ b } loop_body { b ∨ ¬b }` encapsulates the
logical obligations of the while loop; in the above example, we'd have `{ I < N
} I += 1; Z *= I { true }`.  However, we probably also want to be able to state
something about `Z`; that variable is modified in the loop body but isn't
present in the loop's conditional expression.

What's a general statement about `Z` that holds zero, one, two, any number of
times through the loop?  Well, in this case, `Z = fact(I)` holds before and
after the loop body.  That's our _loop invariant_, so our triple would be `{ Z
= fact(I) ∧ I < N } I += 1; Z *= I { Z = fact(I) }`.  If this feels like
consecution from our discussion about safety properties, well, it is! (We can
say more: if we have consecution we probably also need initiation. That's
saying that the loop invariant holds before the loop ever starts.) 

A triple that generalises this, for some statement `S`, some conditional
expression `b`, and loop invariant `P`, is `{P ∧ b} S {P}`.

Zooming out: when we reach the `while` keyword, our loop invariant `P` has to
hold (because, remember, it holds no matter how many times we enter the loop,
even if that number of times is zero).  Similarly, when we reach the `done`
keyword, `P` still has to hold (because it held on our final pass through the
loop body).  We also know that we hit `done` because we exited the loop, and we
know we exited the loop because our loop's conditional evaluated to false; so,
we'd expect `¬b` to hold at that point.  A triple that encapsulates this is
`{P} while b do S done {P ∧ ¬b}`.

So, when we put all these facts together, for some loop invariant `P` and
conditional expression `b`, our Hoare logic inference rule for while loops
is:

::: tip
```
                  {P ∧ b} S {P}
      ----------------------------------- (hoare_while)
          {P} while b do S done {P ∧ ¬b}
```
The _while_ rule: Given a statement where `b` is known to hold before but may
or may not weaken `b` out in the postcondition, `hoare_while` repeatedly
invokes that statement until `b` ceases to hold.
:::

## Mapping `hoare_while` back to FRP

Okay, how do we take this inference rule and map it to something we can use to
transform an FRP program with?  Our other translations of Hoare inference rules
are shaped like "`(□ α // P) → (□ α // P)`", so we might expect a function that
consumes some sort of signal and produces some other sort of signal.

Reading off the conclusion of the inference rule, we might want to build a
combinator that looks something like: "we need to produce a `Signal // P ∧ ¬b`
given an input signal, a P and a b":

```lean4
def hoare_while_ish
  (P b : StateProp a) -- P, our loop invariant; b, our loop check
  (s : □ α // P)      -- our source of input values to poll
  : □ α // P ∧ ¬b := sorry
```

A Signal's the wrong thing to return, though, since we don't _always_ end up
with a value such that `P a ∧ ¬b a` hold.  Our goal is to build an FRP
primitive that shows from any number of loop iterations, say, `i`, will
eventually converge onto `n`.  "Eventually" should make us think of LTL's `◇`,
and LTL's `◇` should make us think of FRP's `◇` - that is, `FRP.Event`!

So, our prototype should produce an Event that raises a value upon loop
termination!

```diff-lean4
  def hoare_while_ish
    (P b : StateProp a) -- P, our loop invariant; b, our loop check
    (s : □ α // P)      -- our source of input values to poll
-   : □ α // P ∧ ¬b := sorry
+   : ◇ {a : α // P ∧ ¬b} := sorry
```

Having an Event mechanism to notify the larger FRP graph when a loop terminates
would be broadly useful, and composes nicely into a larger FRP program.

This is a great v0: the input signal can come from `FRP.scan`,
`FRP.accumulate`, or any other Signal primitive, or a network of composed
signals.  This combinator simply says, "watch this refined signal until the
guard ceases to hold, and then emit the first exit state".

### loop termination and an `Event` to raise on loop exits

::: margin-note
Not thinking about it might be problematic in the event of a loop variable
overflow!
:::
Any programmer's written a "`i = 0; while i < n: ... ; i++`"-shaped loop so
many times that we probably don't even think about the possibility of infinite
loops.  For more complicated control flow, though, we might have to.  And,
no matter whether simple or complicated, in order to construct a proper Event,
that truly encapsulates the inevitability of an eventual LTL proposition, we
have to have a proof of loop termination.

In order to construct that Event we need a proof that the Event will actually
fire; that's exactly our loop termination condition!

```diff-lean4
  def hoare_while_ish
    (P b : StateProp a) -- P, our loop invariant; b, our loop check
    (s : □ α // P)      -- our source of input values to poll
+   (hTerm : ∃ t, ¬ b (s.val t))  -- Proof that we eventually exit the loop
    : □ α // P ∧ ¬b := sorry
    : ◇ {a : α // P ∧ ¬b} := sorry
```

Let's now see how we can implement the body of this combinator.

## A first pass of the `factorial` loop in FRP

Before trying to design a general FRP combinator, let's see how we'd write this
back when we introduced signals in part 3.  I imagine we'd have a signal for
each state variable, and an "environment" variable that bundles them all up:

::: margin-note
In general, we might want `fact_env` to be expressed as a map-like structure
over "all the state variables currently in scope", which, if you've ever
implemented a compiler or interpreter, you know is called the _environment_.
For now, though, just keeping a tuple of values straight is enough for us.
:::
```lean4
def i : □ Nat := FRP.scan (· + 1) 0
def z : □ Nat := (·.factorial) <$> i
def fact_env : □ (Nat × Nat) := Prod.mk <$> i <*> z

#eval fact_env 10 -- (10, 3628800)

example : (fact_env 5).2 = 120 := by decide
```

Clearly, `fact_env` being a signal means it will just keep counting up
indefinitely, so there's no way to maintain a `i < n` invariant.  It kind
of feels like what we want is a notification mechanism to raise an `Event`
when the final environment state is consumed.

It might not be immediately obvious what form this combinator should take,
but if we revisit the conclusion of the `hoare_while` inference rule, we can
essentially read the function signature right off:

::: margin-note
I thought flipping the polarity of `hold` versus `b` in the inference rule
made the type signature here a bit cleaner.  YMMV!
:::
```lean4
def Event.firstWhen
  {P : StateProp α}
  (continue : StateProp α) [DecidablePred b]
  (sig : □ α // P)
  : ◇ {a : α // P a ∧ cont a} := sorry
```

`Event.firstWhen` is a bridge between modalities: it consumes a `□` and
produces aso I `◇`. This isn't the first time we've seen such a function:
`accumulate` went the other way, consuming a `◇` and producing a `□`!

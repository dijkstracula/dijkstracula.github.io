---
layout: post.njk
title: "Leaning into the Coding Interview 4: Alternate implementations and proof-carrying code"
date: 2026-01-30T00:00:00-05:00
tags: [post, lean, verification, provingthecodinginterview]
excerpt: "Time to actually our end-to-end specification!"
draft: true
---

::: tip
_This is part of an ongoing introduction to Lean 4 series_: 
  * [Part one - theorem-proving basics](/posts/proving-the-coding-interview-lean)
  * [Part two - static bounds checks and dependent types](/posts/proving-the-coding-interview-lean-2)
  * [Part three - completing the spec with tactic combinators](/posts/proving-the-coding-interview-lean-3)
  * [Intermezzo - equality proofs between different Fizzbuzzes](/posts/proving-the-coding-interview-lean-intermezzo)
  * [Part four - proof-carrying code](/posts/proving-the-coding-interview-lean-4)

All previous Proving The Coding Interview posts can be found
[here](/tags/provingthecodinginterview/).
:::

## A proof-carrying FB

Last time we looked at the data definition of `Vector a n`, and saw that it was
a structure type containing its runtime data (the backing `Array a` of
elements) and a compile time-only proof relating the size of the array to `n`.
One way to think about this data type is that every `Vector` instance carries
that proof along with it (in practice, remember that owing to _proof
irrelevance_, these sorts of logical propositions get erased after
typechecking, so these statements aren't actually stored in memory and carried
around as the program runs.)

We can do the same thing with the `FB` type.  Currently it's not
dependently-typed (it isn't even polymorphic), but imagine if we made it thus:

```lean4
-- in other words, defining a "polymorphic" type like `FB<i>`
inductive FB (i : Nat) : Type where
  -- TODO: our constructors Fizz, Buzz, Fizzbuzz, and Num
```

This makes FB a _type family_ (or _type constructor_): it defines an infinite
number of types, for all possible `Nat` values.  it's a function at the type
level with type `Nat → Type`. For each natural number i, `FB i` is a distinct
type. So `FB 3`, `FB 5`, and `FB 15` are three different types.  So, `(i : Nat)
→ FB i` is a dependent function type: the type of functions that produce `FB i`
for any i.  Hey, as it happens, `fb_one` is a function of that type!

Unsurprisingly, Lean's type system lets us express a type family in terms of a
`forall` universal quantifier, so `∀ (i: Nat), FB i` refers to the same
concept.  (Another way to express this that bit more like function notation is
`Π (i: Nat) . FB i` - this is just like the lambda calculus, but with `Π` (Pi)
instead of lambda - it's a "map" from Nat to some type in the `FB` family).

OK, for a given `i`, what can we say about each of our constructors?  Well, to
construct a `Fizzbuzz` of type `FB i`, it better be the case that `i % 15 = 0`.
For a `Num` to be a valid `FB i`, `i` must not divide 3 nor 5.  If each
constructor took a _proof_ as argument for the relevant `i`, then, a `FizzBuzz`
could never be used in place where an `FB 12` was expected, for instance.
Let's write that dependent type:

```lean4
inductive FB (i : Nat) : Type where
  | Fizz     (ev : i % 3 = 0 ∧ i % 5 ≠ 0)
  | Buzz     (ev : i % 3 ≠ 0 ∧ i % 5 = 0)
  | FizzBuzz (ev : i % 15 = 0           )
  | Num      (ev : i % 3 ≠ 0 ∧ i % 5 ≠ 0)

instance (i : Nat) : ToString (FB i) where
  toString fb := match fb with
    | .Fizz _     => "Fizz"
    | .Buzz _     => "Buzz"
    | .FizzBuzz _ => "Fizzbuzz"
    | .Num _      => toString i
```

The proof associated with each `FB` constructor is the evidence for that
contructor: it's not enough to simply construct some particular `FB i` like
`Fizzbuzz : FB 15`; we have to provide proof (in the sense of providing _a
proof_!) to the type system that our choice of `i` is a correct one.

### Exploring the `FB` type family with `#check`

So if `FB 42` is a type, and, of course, `42` is a `Nat`, what can we say about
`FB`?  Seems like it's acting like a function that consumes a `Nat` and returns
a type.  And Lean would agree!

:::margin-note
The `#check` command in our IDE lets us inspect the results of typechecking the
supplied expression.  
:::
```lean4
#check FB 42
FB 42 : Type

#check 42
42 : Nat

#check FB
FB (i : Nat) : Type
```

So just as we expeted, `FB` is a function at the type level. Let's play around
with this a bit more: What's the type of `FB.Fizz`?

```lean4
#check FB.Fizz 

FB.Fizz {i : Nat} (ev : i % 3 = 0 ∧ i % 5 ≠ 0) : FB i
```

(The `{i : Nat}` in curly braces is an [implicit
argument](https://lean-lang.org/doc/reference/latest/Terms/Functions/#implicit-functions);
for our purposes, just pretend it isn't there for now.)  What _is_ there,
though, is the `ev` argument: for `FB.Fizz` to typecheck to some `FB i`, we
have to provide the right divisibility proof for the right typelevel `i`!

### Constructing an `FB i` now requires passing in a proof 

Wte can see this in action when we try to define a value whose type is in the
`FB` type family: if we define a variable representing what should be our 41st
entry in our produced Vector, what type should it have?  Hopefully it's clear
that it should be of type `FB 42`.  (Did you say `FB 41`?  Argh, that
off-by-one strikes again!)

```lean4
def my_favourite_fb : FB 42 := -- TODO
```

::: margin-note
If you're convinced that there's truly only one value of a given `FB i` (a type
with one _inhabitant_ is what we call a _singleton type_), that might be worth
writing a theorem about.  Maybe we'll do that another time.
:::
Now, what's a _value_ of type `FB 42`?  Well, 42 is divisible by 3 but not 5,
so that means it's got to be constructed by `FB.Fizz`, right?  Almost but not
quite:

::: warning
```lean4
def my_favourite_fb : FB 42 := FB.Fizz

Type mismatch
  FB.Fizz
has type
  ?m.3 % 3 = 0 ∧ ?m.3 % 5 ≠ 0 → FB ?m.3
but is expected to have type
  FB 42
```
:::

It's not the most readable error (unless you're accustomed to C++ template
metaprogramming), but hopefully if you blur your eyes you can see something to
the effect of "FB.Fizz needs us to prove `42 % 3 = 0 /\ 42 % 5 = 0` to properly
construct a `FB 42`.  Right!  `FB.Fizz` is a constructor that takes a proof as
an argument, and that argument's a proposition.  Well, how do we provide a
proof of `42 % 3 = 0 /\ 42 % 5 = 0`? Good old `lia` will do the trick; turns
out `simp` is smart enough to simplify this down too!

```lean4
def my_favourite_fb : FB 42 := FB.Fizz (by simp)
```

This maybe gives us a sense of what the `by` keyword is all about: we've seen
it start the proofs of all our theorems: `by` drops us into _tactics mode_ for
the remainder of the current expression.  (This means we can prove a theorem
_without_ `by`; maybe we'll see an example of that someday.)

If I forgot my multiples of three and tried to define a `FB 42` with the
`FB.Fizzbuzz` constructor instead, what do I get, by contrast?  Lean gives us
a type error that I can only describe as "you screwed up, and no I will NOT
tell you how!":

::: warning
```lean4
def my_favourite_fb : FB 42 := FB.FizzBuzz (by simp) 

1 goal
⊢ False
unsolved goals
⊢ False
```
:::

Not at all a useful type error, it simply tells us, by way of `False` in our
goal, that there's a contradiction somewhere between us and the proposition
we're trying to prove.

### Type ascription, implicit arguments, and bidirectional typechecking

This also should give you a sense of why dependently-typed languages aren't
able to fully infer types, like more conventional languages can.  Suppose I'd
left off the _type ascription_  of our definition like this:

:::warning
```lean4
def my_favourite_fb := FB.Fizz (by simp)

unsolved goals
⊢ ?m.3 % 3 = 0 ∧ ¬?m.3 % 5 = 0
```
:::

The `?m` indicates that Lean is trying to "fill in the blank" with an appropriate
`i` value to discharge the proof, but it doesn't have one on hand to do so.
This makes sense - after all, well, what _is_ my favourite fizzbuzz?  Is it `FB
15`?  Is it `FB 30`?  `FB 470055`??? I don't know and neither do you.  So, we
have to nail down the `i` _somehow_, and by specifying the full `FB` type of 
the definition we can do so.  

Alternatively, remember that when we looked at the type constructor
for `FB.Fizz`, there was an _implicit argument_.  We can opt into specifying
implicit arguments explicitly with the `@` prefix:

```lean4
def my_favourite_fb := @FB.Fizz 42 (by simp)
```

Now, `i` isn't filled in from the context of us telling Lean what the type of
the definition is, but rather we're passing it in directly.  This means we
don't need type ascription, because we've provided a value for `i` just in a
different way.

The fact that the relevant information for `i` can flow in either direction
is an aspect of _bidirectional typechecking_: `(FB.Fizz (by simp) : FB 42)` is
checked in a top-down way: Lean starts with "<some expression `e`> has type `FB
42`" and remembers that fact when it inspects the expression.  "term e checks
against type τ" is encoded mathematically as `e ⇐ τ`.

By contrast, `@FB.Fizz 42 (by simp)` requires Lean to start with "<some
expression `e`> has <some type `τ`>", writte - it has to use the expression to
figure out the type, so all the information it needs for the latter better be
specified in the former. "term e synthesizes type τ" is encoded as `e ⇒ τ`.

In the first case, checking flows from types to terms, whereas in the second,
it flows from terms to types.

## `fb_one` must provide the _evidence_ for each FB

Okay, enough theory for now.  Hopefully you have a bit of intuition about 
how to define dependently-typed `FB` values no.

Remember that in the last post, when we were stating and proving all these
properties about the `FB` constructors, we did these compile-time checks as
part of a theorem that was separate from our data definitions. The hope is that
this might simplify the proof of our specification without making it harder to
write the implementation.  Let's see if that's actually true.

Okay, with our above changes, `fb_one` no longer typechecks, so let's start
rewriting it.  Already, we can see we hit a snag pretty quickly: in the "then"
arm of the first `if`, we need to pass a proof term to the FB.FizzBuzz
constructor, but, where are we going to find one?

```lean4
def fb_one (i : Nat) : FB i :=
    if i % 15 = 0 then FB.FizzBuzz ??? -- TODO: what proof do we pass to the constructor?
```

Whatever pass to the constructor needs to be a proof that `i % 15 = 0`.
Of course, this is _exactly_ the proposition we know to be true, because
it's right there in the `if` conditional.  We might think it's the case
that we can just pass an automated tactic like `(by lia)` as the argument
to each `FB i` data constructor, but we can see that doesn't work:

::: warning
```lean4
def fb_one (i : Nat) : FB i :=
    if i % 15 = 0 then FB.FizzBuzz (by 

1 goal
i : Nat
⊢ i % 15 = 0
```
:::

We need to specify a proof that i % 15 = 0, but we don't have one in our
context.  But, we know that because we took the `then` arm of the `if`, then
it's obviously true from the program's control flow!

So, here's fun thing we can do in Lean that I've never seen in any other
language: we can use a _dependent if_: at runtime, this behaves identically
to a good old-fashioned `if` special form, but at _typechecking time_, whatever
the conditional is, it acts as an assumption in our proof context.  Take a
look!

```lean4
def fb_one (i : Nat) : FB i :=
    if h15 : i % 15 = 0 then FB.FizzBuzz (by -- NEW

i : Nat
h15 : i % 15 = 0
⊢ i % 15 = 0
```

We can see that, as expected, the `if` is now in our context! That's exactly
the right argument to `FB.FizzBuzz`!  So, we can pass `h15` in directly, or
stay in tactics mode and use `(by assumption)`, which looks through our context
for an exact match to our goal.  Let's pass in the hypothesis directly.

```lean4
def fb_one (i : Nat) : FB i :=
    if h15 : i % 15 = 0 then FB.FizzBuzz h15 else
    -- TODO: the remaining three cases
```

OK, let's keep going:

```lean4
def fb_one (i : Nat) : FB i :=
    if h15 : i % 15 = 0 then FB.FizzBuzz h15 else
    if h5 : i % 5 = 0 then FB.Buzz --TODO: ok now which proof here??

i : ℕ
h15 : ¬i % 15 = 0
h5 : i % 5 = 0
⊢ FB i
```

Notice that because we're in the "else" branch of the `i % 15 = 0` `if`,
our `h15` hypothesis is changed!  This makes sense because we know here
that the first hypothesis must be false, but the `i % 5 = 0` one must
be true.

Remember that `lia`, the linear arithmetic solver-backed tactic, is powerful
enough to derive  `i % 3 ≠ 0 ∧ i % 5 = 0` from what we have in our context.
So, the proof argument for `FB.Buzz` is simply `by lia`!

In fact, `lia` will be our workhorse for the remaining three cases:

```lean4
def fb_one (i : Nat) : FB i :=
    if h15 : i % 15 = 0 then FB.FizzBuzz h15 else
    if h5 : i % 5 = 0 then FB.Buzz (by lia) else
    if h3 : i % 3 = 0 then FB.Fizz (by lia) else
    FB.Num (by lia)
```

## Constructing our vector of certified `FB`s

Unsurprisingly, that we've added some things to `FB` means we've pushed
some complexity into `fb_vec` as well as `fb_one`.

`fb_one`'s type signature wasn't any harder to write than it was before,
because it was clear where we'd get the term argument for `FB`: the
function gets passed `i` as an argument, and `i` is used in the dependent
return type.

But in the return type for `fb_vec`, what should the argument be?

```lean4
def fb_vec (n : Nat) : Vector (FB ???) n :=
```

## We're producing a `Vector` of ... what, exactly?

So far, when we've defined a dependent type, the term "argument" for the type
constructor was already obvious.  For instance, where did we get the `i` in the
return type of `fb_one`?  Well, it was passed into the function, so it was
already in scope.  

The only `Nat` in scope for us here is `n`, and that's clearly not correct. A
`Vector (FB n) n` would have `n` identical elements of type `FB n`, so we'd
have as possible values of such a type: `[1] : Vector (FB 1) 1`, `[2, 2] :
Vector (FB 2) 2`, `[Fizz, Fizz, Fizz] : Vector (FB 3) 3`, and so on. An
_interesting_ family of types, but not the one we're after.

In fact, no particular `Nat` will do here - The type we want to describe
needs to describe a `Vector` whose elements have types that _vary_: 

```lean4
[ Num 1    : FB 1, 
  Num 2    : FB 2, 
  Fizz     : FB 3, 
  Num 4    : FB 4,
  ... 
  FizzBuzz : FB 15] : Vector (??? FB (...????...) ) 15
```

### Sigma types relate a value with a dependently-typed value

We can write a type like this down by defining `i` _inside_ the parameter
to the vector - it's a bit like moving a global variable inside a function
definition, sorta.  We can't actually write it this way, but we could perhaps
imagine something like:

```lean4
[ Num 1    : FB 1, 
  Num 2    : FB 2, 
  Fizz     : FB 3, 
  Num 4    : FB 4,
  ... 
  FizzBuzz : FB 15] : Vector (let (i:Nat) be some number in FB i) 15
```

I'll show you the _actual_ syntax first and then explain what it's saying, and
then after that, move on to what it _means_:

```lean4
[ <1, Num 1>     : (1, FB 1)
  <2, Num 2>     : (2, FB 2)
  <3, Fizz>      : (3, FB 3)
  <4, Num 4>     : (4, FB 4)
  ... 
  <15, FizzBuzz> : (15, FB 15)] : Vector (Σ i, FB i) 15
```

::: margin-note
We construct datatypes like records and tuples with the angle brackets `⟨` and
`⟩`: the first element of the pair is the `i` value that will fix the type `FB
i`, and the second element is the expression that typeschecks to `FB i`. 
:::
The elements of this Vector are no longer just `FB _`s, but a _dependent
pair_: We can read this _sigma type_ as saying "the elements of this Vector
are `FB i` _for some varying i_".  In this construction, each element is now
two values: some number `i`, and the `i`th element of the Fizzbuzz sequence!
The first element is sometimes called the _witness_ of the type: it's another
form of evidence to the type system, namely a proof that a value of type `FB i`
is constructable!

Note that our runtime representation of what `fb_vec` returns has now changed:
Even though propositions and types are erased at runtime, the witness is _not_
erased at runtime!  So, this representation _does_ take up more memory. (This
makes sense when you consider that `i` is used both in the type-level but also
in computation, when we print out `FB.num i`.)

## `fb_vec` must now produce a dependent pair

The change for `vb_vec` is pretty mechanical: rather than just mapping over
the `Vector` of `[1, 2, ... n]` with `fb_one`, we said just now that instead
we need to produce a _dependent pair_.  

We know for sure that an `FB i` is constructable because that's the return
type of `fb_one i`.  So, our `fb_vec` function is now:

```lean4
def fb_vec (n : Nat) : Vector (Σ i, FB i) n :=
  Vector.range' 1 n |> Vector.map (fun i => ⟨i, fb_one i⟩)

```

::: note
It's worth pausing and pondering about what Vectors this type rejects but also
incorrectly accepts.  For instance, does this type say anything about ordering
of the `i`s, or uniqueness?  Does every element of `Vector (FB n) n` (that is,
`[1]`, `[2, 2]`, `[Fizz, Fizz, Fizz]`, and so on) have a one-to-one
correspondence with elements in `Vector (Σ i, FB i) 15`?
:::

Note that because Lean doesn't implement `ToString` for sigma types, even
if each element in the pair does, if we want to print Vectors returned 
by `fb_vec` directly, we have to do so ourselves.

Our goal could be to write an `instance ToString` for sigma types of witness
type `α` and dependent type `β α`, which we would write as `(Σ (x : α), β x)`.
(In our particular sigma type, `(Σ i, FB i)`, `α` is `Nat` and `β` is `FB`.)  

```lean4
instance : ToString (Σ (x : α), β x) where
  toString := -- TODO
```

Just to simplify things for this post, rather than writing a `ToString` for
_all_ dependent pairs (which means we have to show that `α` and `β` are
`ToString`able, let's just specialise this for our exact pair:

```lean4
instance : ToString (Σ i, FB i) where
  toString := fun ⟨_, fb⟩ => s!"{toString fb}"
```

:::margin-warning
Strangely, `Vector` doesn't seem to implement `ToString`, so I'm printing it
out by pulling out its backing `Array`.  I wonder if this is just an omission
or if there's a good reason for this.
:::
```lean4
#eval (fb_vec 5).toArray

#[1, 2, Fizz, 4, Buzz]
```

## Caching out by simplifying our spec

All right!  We've pushed a lot of formal complexity into the implementation.

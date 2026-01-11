---
layout: post.njk
title: "Leaning into the Coding Interview 4: Proof-carrying code"
date: 2026-01-30T00:00:00-05:00
tags: [post, lean, verification, provingthecodinginterview]
excerpt: "Time to actually our end-to-end specification!"
draft: true
---

::: tip
_This is part of an ongoing introduction to Lean 4 series_: 
  * [Part one - theorem-proving basics](/posts/proving-the-coding-interview-lean)
  * [Part two - static bounds checks and dependent types](/posts/proving-the-coding-interview-lean-2)
  * [Part three - completing the spec with tactics combinators](/posts/proving-the-coding-interview-lean-3).
  * [Part four - proof-carrying code](/posts/proving-the-coding-interview-lean-4).

All previous Proving The Coding Interview posts can be found
[here](http://localhost:8080/tags/provingthecodinginterview/).
:::

## A proof-carrying FB

Last time we looked at the data definition of `Vector a n`, and saw that it was
a structure containing its runtime data (the backing `Array a` of elements) and
a compile time-only proof relating the size of the array to `n`.  One way to
think about this data type is that every instance carries that proof along with
it (in practice, remember that owing to _proof irrelevance_, these sorts of
logica propositions get erased after typechecking, so these statements aren't
actually stored in memory and carried around as the program runs.)

We can do the same thing with the `FB` type.  Currently it's not
dependently-typed (it isn't even polymorphic), but imagine if we made it thus:

```lean4
-- in other words, defining a "polymorphic" type like `FB<i>`
inductive FB (i : Nat) : Type where
  -- TODO: our constructors Fizz, Buzz, Fizzbuzz, and Num
```

This makes FB a _type family_: it defines an infinite number of types, for each
possible `Nat` value.  OK, for a given `i`, what can we say about each of our
constructors?  Well, to construct a `Fizzbuzz` of type `FB i`, it better be the
case that `i % 15 = 0`.  For a `Num` to be a valid `FB i`, `i` must not divide
3 nor 5.  If each constructor took a _proof_ as argument for the relevant `i`,
then, a `FizzBuzz` could never be used in place where an `FB 12` was expected,
for instance.  Let's write that dependent type:

```lean4
inductive FB (i : Nat) : Type where
  | Fizz     (w : i % 3 = 0 ∧ i % 5 ≠ 0)
  | Buzz     (w : i % 3 ≠ 0 ∧ i % 5 = 0)
  | FizzBuzz (w : i % 15 = 0           )
  | Num      (w : i % 3 ≠ 0 ∧ i % 5 ≠ 0)

instance (i : Nat) : ToString (FB i) where
  toString fb := match fb with
    | .Fizz _     => "Fizz"
    | .Buzz _     => "Buzz"
    | .FizzBuzz _ => "Fizzbuzz"
    | .Num _      => toString i
```

### `fb_one` must _witness_ the valid construction of each FB

Okay, `fb_one` no longer typechecks.  Let's start rewriting it.  Already, we
can see we hit a snag pretty quickly: in the "then" arm of the first `if`, we
need to pass a proof term to the FB.FizzBuzz constructor, but, where are we
going to find one?

```lean4
def fb_one (i : Nat) : FB i :=
    if i % 15 = 0 then FB.FizzBuzz ??? -- TODO: what proof do we pass to the constructor?
```

Whatever pass to the constructor needs to be a proof that `i % 15 = 0`.
Of course, this is _exactly_ the proposition we know to be true, because
it's right there in the `if` conditional.  

So, here's fun thing we can do in Lean that I've never seen in any other
language: we can use a _dependent if_: at runtime, this behaves identically
to a good old-fashioned `if` statement, but at _typechecking time_, it
acts as an assumption in our proof context.  Take a look!

```lean4
def fb_one (i : Nat) : FB i:=
    if h15 : i % 15 = 0 then FB.FizzBuzz -- NEW

i : ℕ
h15 : i % 15 = 0
⊢ FB i
```

Note that our context doesn't say anything about goals, because we're not
writing tactics to prove a theorem right now.  But we can see that inside
the "then" branch, we have the proposition `h : i % 15 = 0`.  That's exactly
the right argument to `FB.FizzBuzz`! 

```lean4
def fb_one (i : Nat) : FB i:=
    if h15 : i % 15 = 0 then FB.FizzBuzz h15 else
    -- TOOD: the remaining three cases
```

OK, let's keep going:

```lean4
def fb_one (i : Nat) : FB i:=
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

In fact, `lia` will be our workhorse for the remaining two cases:

```lean4
def fb_one (i : Nat) : FB i:=
    if h15 : i % 15 = 0 then FB.FizzBuzz h15 else
    if h5 : i % 5 = 0 then FB.Buzz (by lia) else
    if h3 : i % 3 = 0 then FB.Fizz (by lia) else
    FB.Num (by lia)
```

---
layout: post.njk
title: "Proving the Coding Interview: Lean vs Dafny round two"
date: 2026-01-30T00:00:00-05:00
tags: [post, lean, verification, provingthecodinginterview]
excerpt: "Pls types?  No terms!  Only types!"
draft: true
---

In an [earlier](/posts/proving-the-coding-interview-lean/) post, we learned a
bunch of Lean's syntax and saw how to write some simple theorems about the
venerable(?) Fizzbuzz problem.  In particular, we learned some simple _tactics_
that can break down a theorem's goal into simpler statements, until we are
left with an axiomatically-true statement:

- The `rw` tactic lets us, if we have a proof of equality, substitute one
side of the equality for another;
- The `unfold` tactic lets us substitute the name of something, like a function,
with its definition;
- The 'apply' tactic lets us break down our goal if we have an
  appropriately-typed existing theorem on hand.

This time, we'll refine our `fizzbuzz` implementation and write some more
interesting proofs about it, and learn some more tactics along the way.

## Previously, on...

Here's where we left off last time!  We wrote the function in a straightforward
functional way, and a few theorems.  (Realizing that I never actually showed
you how to _run_ any of the code we wrote, I just now added a `main` function
to the program.)

::: margin-note
Lean can transpile first to C - by running `lean --c=FB.c FB.lean` you can try
to convince yourself that the theorems we wrote have no runtime representation
and exist only for the typechecker to verify!  Now that's what I call a
zero-cost abstraction...
:::
```lean4
def fizzbuzz (n : Nat) : List String :=
  List.range' 1 n |> List.map (fun i =>
    if i % 15 = 0 then "Fizzbuzz" else
    if i % 5 = 0 then "Buzz" else
    if i % 3 = 0 then "Fizz" else
    Nat.repr i)

theorem fizzbuzz_of_3_example : fizzbuzz 3 = ["1", "2", "Fizz"] := rfl

theorem fizzbuzz_of_3_is_nonempty : 0 < (fizzbuzz 3).length := by
  rw [fizzbuzz_of_3_example]
  simp

theorem fizzbuzz_of_n_is_length_n (n : Nat) : (fizzbuzz n).length = n := by
  unfold fizzbuzz
  simp

def main (args : List String) : IO Unit :=
  match args[0]? >>= String.toNat? with
  | none =>   IO.println "No argument or invalid ℕ"
  | some n => IO.println s!"fizzbuzz({n}) = {fizzbuzz n}"
```
```
$ lean --run FB.lean
No argument or invalid ℕ
$ lean --run FB.lean 42
fizzbuzz(42) = [1, 2, Fizz, 4, Buzz, Fizz, 7, 8, Fizz, Buzz, 11, Fizz, 13, 14, Fizzbuzz, 16, 17, Fizz, 19, Buzz, 
                Fizz, 22, 23, Fizz, Buzz, 26, Fizz, 28, 29, Fizzbuzz, 31, 32, Fizz, 34, Buzz, Fizz, 37, 38, 
                Fizz, Buzz, 41, Fizz]
$
```

At the end of the last post, we noticed that while we're using Lean's fancy
("dependent") type system in the theorem-proving part of the program, we aren't
leveraging it as well as we could in the actually-do-the-computation part.
We saw there were lots of different ways for the function `Nat -> List String`
to return something _other_ than the fizzbuzz problem.  

::: margin-note
Functional programmers like to refer to the type system "making invalid states
unrepresentable" - we are already doing this by, say, making it impossible to
return a `List Int`; let's see how much farther we can push it!
:::
If we can reformulate the `fizzbuzz` function's type signature more precisely,
maybe we can statically prevent the function from doing egregiously wrong things,
and then write theorems for more fine-grained specifications.

Okay, this is what was left on our todo list:

::: tip
1) Encode the elements returned not as strings but as an enum-like type that
forces a "fizz", "buzz", "fizzbuzz", or number value.
2) Produce not just an ordinary `List` of values, but a special collection type
that knows its own length, so just like with `add_one_pos`, the return type
can _depend_ on the value of the function argument;
:::

## Destringifying our computation

We said before that having `fizzbuzz`'s return type be `List String` isn't all
that precise - most valid `String`s are invalid for our problem.  (Another way
to say this is that there are many invalid _inhabitants of `String`_).  A
safer representation is to define a new type whose only inhabitants represent
the strings "buzz", "fizz", "fizzbuzz", or a natural number:

```lean4
inductive FB : Type where
  | Fizz
  | Buzz
  | FizzBuzz
  | Num (i : Nat)
```

You might recognise this as a _sum type_ or an _enum_, depending on your
background; we may see later on that Lean's _inductive types_ are more
general, but that's a topic for another time.

From a programming perspective, we can do all the things with this type
that you'd expect.  We can _construct_ elements using its four defined data
constructors, we can turn an element into something else by pattern match over
it (we'll see that this is _eliminating_ an element), we can attach methods or
implement typeclasses or traits based on them... in fact, why don't we do that
last one right now:

```lean4
instance : Repr FB where
  reprPrec fb _ := match fb with
    | .Fizz => "Fizz"
    | .Buzz => "Buzz"
    | .FizzBuzz => "Fizzbuzz"
    | .Num i => toString i |> Std.Format.text
```

This definition makes `FB` an instance of the Repr typeclass (which is a
concept similar to associating a type with a trait in other languages), which
gives us a way of turning a value of this type into a string.

## A proof that connects the helper function to `fizzbuzz`

Okay, now it's time for a meatier proof that I'm going to guess will come in
handy as a lemma for proofs down the road.  The bulk of our problem
specification invoves statements relating how element `i` of the returned list
relates to, well, what gets passed into the `fb_one` helper.  Having a proof
that states that relationship more formally will help us connect later proofs
about `fizzbuzz` to ones about `fb_one`.  Sometimes this is called a _bridge
proof_.  Let's write it!

```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1)) := by

1 goal
⊢ ∀ (i n : ℕ), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1))
```

A bit more syntax: the `[]?` operator indexes into a `List α` and produces
an `Option α`, depending on whether the index was in range or not.  So,
this is saying "not only will the `i`th element of the list be well-defined,
but it will have the same value as calling `fb_one (i+1)`.

### `intro` introduces propositions into our context

Notice that I've written this theorem with a "forall" quantifier instead
of having it consume an argument, and when we start out our context has no
hypotheses in scope.  The `intro` tactic lets us add things into our context
in two cases:

::: margin-note
We can combine multiple `intro`s on one line by using the `intros` tactic.
:::
1) If our goal looks like `∀ (x: t), expr` (read: "for all `x`s of type `t`,
`expr`"), `intro x` will add the proposition `x : t` (read: "suppose `x` is of
type `t`") into our context, and changes the goal to `expr`:

```
theorem fb_one_to_fizzbuzz_x :
    ∀ (i n : Nat), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1)) := by
  intro i n

1 goal
i n : ℕ
⊢ ∀ (n : ℕ), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1))
```

Of course, the context doesn't tell us anything about what values `i` and `n`
have, since the whole point of a forall-quantifier is that _the values don't
matter_- whatever we're trying to prove better be true no matter what values
they take!

2) If our goal looks like an implication of the form `x -> y`, then `intro x`
adds `x` as a _hypothesis_ into our context and reduces the goal to just `y`.
The interpretation of a logical implication here is that knowing `x` is
_sufficent_ to prove `y`, so with `x` as an assumption, we need only prove `y`
to complete our proof.

Here, the antecedent in our implication is the bounds-check `i < n`, so with
another `intro` we have that appear in our goal:

```
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n

i n : ℕ
H_i_lt_n : i < n
⊢ (fizzbuzz n)[i]? = some (fb_one (i + 1))
```

Notice that `intros` always adds things in they appear in the goal: if we'd
given different names to `i` and `n` we would have renamed them. I did just
that here: `H_i_lt_n` is the _hypothesis_ that states that `i` is less than
`n`, after all.

### `have` and `exists` let us introduce new things ... if we can prove them

I often feel like starting out a nontrivial proof feels like I just got [kicked
off the boat at Seyda Neen](https://en.uesp.net/wiki/Morrowind:Seyda_Neen): 
a whole world of possibilities have opened up to me, but it's hard to know
where to start.

Well.  Since we have an _equality proof_ here, and I know `fb_one` is in
`fizzbuzz`'s function body, it seems reasonable to start by unfolding
`fizzbuzz` so we at least have `fb_one` on both sides of the equality.  You can
certainly prove it this way, but if we go down that road we'll find that
wranging that `some` value through to the end of the proof ends up being a bit
annoying.

::: margin-note
I wish I could give you advice about how to _intuit_ which path is going
to be less fraught.
:::

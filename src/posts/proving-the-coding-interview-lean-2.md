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
venerable(?) Fizzbuzz problem.

## Previously, on...

Here's where we left off last time!  We wrote the function in a straightforward
functional way, and a few theorems.  (Realizing that I never actually showed
you how to _run_ any of the code we wrote, I just now added a `main` function
to the program.)

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
fizzbuzz(42) = [1, 2, Fizz, 4, Buzz, Fizz, 7, 8, Fizz, Buzz, 11, Fizz, 13, 14, Fizzbuzz, 16, 17, Fizz, 19, Buzz, Fizz, 22, 23, Fizz, Buzz, 26, Fizz, 28, 29, Fizzbuzz, 31, 32, Fizz, 34, Buzz, Fizz, 37, 38, Fizz, Buzz, 41, Fizz]
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
1) Produce not just an ordinary `List` of values, but a special collection type
that knows its own length, so just like with `add_one_pos`, the return type
can _depend_ on the value of the function argument;
2) Encode the elements returned not as strings but as an enum-like type that
forces a "fizz", "buzz", "fizzbuzz", or number value.
:::

## A List that knows its own length

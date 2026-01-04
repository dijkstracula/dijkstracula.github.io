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
- The `apply` tactic lets us break down our goal if we have an
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
::: margin-note
In case you need a refresher on `Option`: Akin to "nullable" values in other
languages, it indicates either the absence of a value of type `a` (via the
`some a` constructor) or its absence (via `none`).  This way, indexing into
our `args` `List` is always well-defined; we don't have to worry about an
exception or a `panic!` (or a segfault!).
:::
```lean4

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
that knows its own length at the type level, so just like with `add_one_pos`,
the return type can _depend_ on the value of the function argument;
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
instance : ToString FB where
  toString fb := match fb with
    | .Fizz => "Fizz"
    | .Buzz => "Buzz"
    | .FizzBuzz => "Fizzbuzz"
    | .Num i => toString i
```

::: margin-note
In fact, our `main` function can be left unchanged, since implemeting `ToString
FB` means anything we can do with a `String` (and subsequently a `List String`)
we can also do with an `FB` (and also `List FB`).
:::
This definition makes `FB` an instance of the `ToString` typeclass (which is
similar to associating a type with a trait in other languages), which gives us
a way of implicitly stringifying to print out the `List FB`, just like we did
with the earlier version's `List String`.  

## A proof that connects `fb_one`'s behaviour to `fizzbuzz`'s

There were _two_ TODOs on our list, but I'm going to defer the second one for a
moment.

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

::: margin-note
More generally we say that `[]?` is a _total_
function: every input has a well-defined output, even though not every input
value has a well-defined element to index into.
:::
A bit more syntax: the `[]?` operator indexes into a `List α` and produces an
`Option α`, depending on whether the index was in range or not.  We actually
saw this in use in our `main` function at the top of this post.  So, our
proposition here is saying "not only will the `i`th element of the list be
well-defined, but it will have the same value as calling `fb_one (i+1)`.
(There's also a `[]!` operator, which will either return an unwrapped `α` or
_panic_ if we attempt to index out of bounds, and also a mysterious third `[]`
operator, which we'll talk about very soon.)

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

```lean4
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

```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n --NEW

i n : ℕ
H_i_lt_n : i < n
⊢ (fizzbuzz n)[i]? = some (fb_one (i + 1))
```

Notice that `intros` always adds things in they appear in the goal: if we'd
given different names to `i` and `n` we would have renamed them. I did just
that here: `H_i_lt_n` is the _hypothesis_ that states that `i` is less than
`n`, after all.

### `have` lets us state new hypotheses (so long as we can prove them too)

I often feel like starting out a nontrivial proof feels like I just got [kicked
off the boat at Seyda Neen](https://en.uesp.net/wiki/Morrowind:Seyda_Neen): 
a whole world of possibilities have opened up to me, but it's hard to know
where to start.  Well.  

Since we have an _equality proof_ here, and I know `fb_one` is in `fizzbuzz`'s
function body, it seems reasonable to start by unfolding `fizzbuzz` so we at
least have `fb_one` on both sides of the equality.  Our proof would succeed if
we `unfold`ed right now, but, it'll make the goal term gnarlier than it needs
to be, so I'll actually hold off on doing it just yet.

Well, so then what _else_ could we do to simplify our goal?

If we think about simplifying our goal from the outside inwards, maybe seeing
if we can handle the `Option` value as it relates to using the safe element
lookup operator `[]?` makes sense. After a bit of splunking around the `List`
datatype's lemmas file, I came across an interesting-sounding one:

::: tip
```lean4
theorem getElem?_eq_some_iff {l : List α} : 
  l[i]? = some a ↔ ∃ h : i < l.length, l[i] = a := ...
```
:::

::: margin-note
Next time you're bored in the shower it might be useful to spend a moment
meditating on the way that equality (`<prop> = <prop>`) is similar and not
similar to biconditional equvialence (`<prop> <-> <prop>`).
:::
This theorem is a _biconditional_ ("if and only if"), stating that the equality
on the left-hand side of `<->` is equivalent to the one on the right. It might
be worth taking a second and letting the fact that up to this point we've only
been writing theorems that state propositions about program values: `(fizzbuzz
n).length = n`, `0 < ["1", "2"].length + 1`, and so on.  But this is a
proposition stating something about _other propositions_.

OK, since the left-hand side of this `<->` is shaped exactly like our goal,
let's use `rw` to transform it into the right-hand side.

```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n
  rw [@List.getElem?_eq_some_iff] --NEW

1 goal
i n : ℕ
H_i_lt_n : i < n
⊢ ∃ h, (fizzbuzz n)[i] = fb_one (i + 1)
```

Three things have changed here: First, on the right-hand side of our goal
equality, the `some` constructor is gone.  Second, on the left-hand side, we're
indexing into the returned `List` not with `[]?` nor with `[]!`, but with that
mysterious third `[]` operator.  This is [lookup with proof
obligation](https://leanprover-community.github.io/mathlib4_docs/Init/GetElem.html)
notation!  What this means is that the type system will only let us index into
our `List` with some index `i` if we have a hypothesis somewhere in our context
stating that `i` is less than the length of the list.

The cool thing here is that this means `[]` is well-defined for all valid inputs
without needing a wrapper type like `Option` or sacrificing purity by panicing,
so long as we can prove that the index is in bounds statically!

This explains the third thing that changed: The goal now wants that proof from
us: it wants some hypothesis `h` such that `h` explains why it's safe for us 
to index into our returned list.

### `have` defines a new hypothesis

::: margin-note
The `exists` tactic does the same thing as producing a value of type `Exists`
with the
[intro](https://github.com/leanprover/lean4/blob/b40dabdecdf666cb50d20ed8f2037a41aaa999e2/src/Init/Core.lean#L331-L334)
constructor - in fact, under the hood many tactics are actually constructing
so-called "proof terms" for us - but `Exist`'s type signature is a bit gnarly
for us just yet so I'll stick to using tactics whenever possible. 
::: 
We _almost_ have that hypothesis in our context: `H_i_lt_n` states `i < n`.
Let's see what happens when we try to suggest that Lean fill in the existential
with it:

::: warning
```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n
  rw [@List.getElem?_eq_some_iff]
  exists H_i_lt_n --NEW
```
```
Application type mismatch: The argument
  H_i_lt_n
has type
  i < n
but is expected to have type
  i < (fb_list n).length
in the application
  Exists.intro H_i_lt_n
```
:::

::: margin-note
Even though Lean's not really capable of giving us _counterexamples_ to our
theorems in the way that Dafny could, this is a pretty readable error message
as far as type errors go!
:::
This makes sense - the theorem is stating something about the length of the
`List`, and we know intuitively that `n` represents the length of the `List`.
What we have to do is show that `(fizzbuzz n).length` equals `n`.

We'll do this with the `have` tactic: `have` defines a new hypothesis in our
context, that we'll have to prove before we can proceed with the rest of our
`fb_one_to_fizzbuzz` proof:

```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fb_list n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n
  rw [@List.getElem?_eq_some_iff]  
  have H_n_is_len : (List.length (fb_list n) = n) := by -- NEW

1 goal
i n : ℕ
H_i_lt_n : i < n
⊢ (fb_list n).length = n

unsolved goals
i n : ℕ
H_i_lt_n : i < n
H_n_is_len : (fb_list n).length = n
⊢ ∃ h, (fb_list n)[i] = fb_one (i + 1)
```

Notice that our new goal is to prove the local proposition we just defined,
and that Lean reminds us of our still-unsolved goal underneath.

...hey, as it happens, we proved this last time with the `fb_length` theorem!
So, we can simply apply our previous theorem and then we're immediately done.

::: margin-warning
Here we're using `have` to define a new entry in our context.  In Coq, I could
simply have applied `fb_length` to the _existing_ entry with `apply fb_length
at H_i_lt_n`, saving us a few steps.  Lean, though, doesn't seme to let us
apply a theorem to a hypothesis, though.  I'm not sure why!
:::
```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fb_list n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n
  rw [@List.getElem?_eq_some_iff]  
  have H_n_is_len : (List.length (fb_list n) = n) := by apply fb_length --NEW

1 goal
i n : ℕ
H_i_lt_n : i < n
H_n_is_len : (fb_list n).length = n --NEW
⊢ ∃ h, (fb_list n)[i] = fb_one (i + 1)
```

Now we're back to the original goal to prove, but now we have our new equality
ready to use.  If we rewrite the `n` in `H_i_lt_n`, then we've got precisely
the bounds-check proof we need!

```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fb_list n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n
  rw [@List.getElem?_eq_some_iff]  
  have H_n_is_len : (List.length (fb_list n) = n) := by apply fb_length
  rw [<- H_n_is_len] at H_i_lt_n -- NEW

1 goal
i n : ℕ
H_i_lt_n : i < (fb_list n).length --NEW
H_n_is_len : (fb_list n).length = n
⊢ ∃ h, (fb_list n)[i] = fb_one (i + 1)
```

Now that we have precisely the hypothesis that the type checker complained
that we didn't have before, we can use `exists` as before, and we'll see the 
"there exists an `h`, such that..." part of the goal disappear!

```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fb_list n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n
  rw [@List.getElem?_eq_some_iff]  
  have H_n_is_len : (List.length (fb_list n) = n) := by apply fb_length
  rw [<- H_n_is_len] at H_i_lt_n
  exists H_i_lt_n

1 goal
i n : ℕ
H_i_lt_n : i < (fb_list n).length
H_n_is_len : (fb_list n).length = n
⊢ (fb_list n)[i] = fb_one (i + 1)
```

::: margin-note
Did I unfold first, and after completing the proof, decide that for
expository purposes it was better to do it later, or am I actually
_just that insightful_?  You be the judge...
:::
OK, we're kind of out of other things to do, so _now_ let's unfold the
definition of `fizzbuzz` and simplify the goal with `simp`.  (Again, the proof
would look essentially identical if we'd unfolded from the start, but the
expanded definition would have been a lot harder to read.

```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fb_list n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n
  rw [@List.getElem?_eq_some_iff]  
  have H_n_is_len : (List.length (fb_list n) = n) := by apply fb_length
  rw [<- H_n_is_len] at H_i_lt_n
  exists H_i_lt_n
  unfold fb_list; simp

1 goal
i n : ℕ
H_i_lt_n : i < (fb_list n).length
H_n_is_len : (fb_list n).length = n
⊢ fb_one (1 + i) = fb_one (i + 1)
```

The equality is _almost_ the same on both sides: the only difference
is the order of arguments to `+`.  We know addition is commutative,
and via the `Nat.add_comm` theorem, so does Lean, so with one final
rewrite we can complete the proof.

::: margin-note
One of the downsides of using automated tactics like `simp` is that
it's not immediately clear to us as programmers what simplifications
it will be able to do.  I might have thought that it'd attempt to 
flip the arguments to the addition, but clearly not.  By contrast,
as opaque as Dafny's internals seem to be, its underlying SMT solver
seems grounded enough in the axioms of linear arithmetic that we would
reasonably guess what it's capable of doing "out of the box".
:::
```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fb_list n)[i]? = some (fb_one (i + 1)) := by
  intros i n H_i_lt_n
  -- unfold fb_list
  rw [@List.getElem?_eq_some_iff]
  have H_n_is_len : (List.length (fb_list n) = n) := by apply fb_length
  rw [<- H_n_is_len] at H_i_lt_n
  exists H_i_lt_n
  unfold fb_list; simp
  rw [Nat.add_comm]

Goals accomplished!
```

Phew, that was a bit of a journey.

## Lifting the length of a list into its own type

We did it!  We actually proved a pretty cool and nontrivial proof about
`fizzbuzz`, putting us well on our way to being able to write the rest
of our specification.

I want to divert things for a moment, though, to finally cover the other TODO
that we left the previous post with:  Remember that we had to write an external
theorem relating the length of `fizzbuzz n` to `n` itself.  On our TODO
list was:

::: tip
`fizzbuzz` should produce not just an ordinary `List` of values, but a special
collection type that knows its own length at the type level.
:::

::: margin-note
`Vector` is an example of a generalsed algebraic datatype (GADT), which even
non dependently-typed languages like Haskell and OCaml let you implement. See
[these
notes](https://www.seas.upenn.edu/~cis1940/spring15/lectures/10-gadts.html) for
more details if you're curious.
:::
Such a collection type is one of the canonical dependent types, which is by
convention named `Vector a n`, where `a` is the type of the elements in the
collection (just like `a` in `List a`) and `n` is a _type-level term_
representing how many elements are in the collection.  (So, of course, this is
distinct from `std::vector` or a linear algebra one-dimensional matrix.)

Remember that types in Lean have no runtime semantics, so this is _not_ the
same as `Vector` being, say, a structure type holding a `List a` and a number.
To drive this home, let's look at the data definition for `Vector a n`:

::: margin-note
As you might imagine, `Array a` is another basic collection type, just like
`List a`, in Lean.  There's also an `List.Vector` type that backs the elements
with `List` instead, but I'll stick with the "standard" one here.
:::
```lean4
/-!
# Vectors

`Vector α n` is a thin wrapper around `Array α` for arrays of fixed size `n`.
-/

structure Vector (α : Type u) (n : Nat) where
  /-- The underlying array. -/
  toArray : Array α

  /-- Array size. -/
  size_toArray : toArray.size = n
```

What this _actually_ is is a structure type that also holds a _proof of
equality_ about the underlying collection.

## A dependently-typed `Fizzbuzz`

Let's rewrite `fizzbuzz` to have a `Vector` return type.  The collection we
return will hold `n` elements of type `FB`, and so our type signature is going
to be `Nat -> Vector FB n`.  Straightforward enough, but is implementing this
function going to be harder than before?

Turns out: with a bit of perusing of the `Vector` documentation, we in fact
have replacements for
[List.range](https://github.com/leanprover/lean4/blob/master/src/Init/Data/Vector/Basic.lean#L363-L364)
and
[List.map](https://github.com/leanprover/lean4/blob/master/src/Init/Data/Vector/Basic.lean#L237-L238),
making our dependently-typed Fizzbuzz look almost identical to the one that
returns a List!  (If you look at those two functions, they're not complicated
in their own right, so if the standard library didn't expose them for us it
wouldn't have been super onerous to do it ourselves.)

Okay, here's our dependently-typed function:

```lean4
def fb_vec (n : Nat) : Vector FB n := 
  Vector.range' 1 n |> Vector.map fb_one
```

Just from reading off the type signature, we can see that there's really no
need to write a theorem stating that the length of `fb_vec n` equals `n` - it's
encoded right there in the type signature!

I mean, we _can_ write it anyway, but it's going to be a pretty simple one - 
`rfl` is enough to prove it!

```lean4
theorem fb_vec_length (n : Nat) : (fb_vec n).size = n := by rfl
```

Anything that can be proven by `rfl` is "obvious" to Lean, so this means our
equvialent theorem that relates `fb_vec` to `fb_one` is way easier to write: we
don't have to bother proving that the length of the returned collection is `n`,
because in this case Lean can simply "read it off" from the `Vector`'s type.

Here's the full proof.

::: margin-note
The `[i]'h` syntax here indicates that `h : i < n` is the proof that this is a
safe access to the `Vector`.  By giving it a name, like we did with `i` and
`n`, we can refer to it elsewhere in the proposition.
:::
```lean4
theorem fb_one_to_fb_vec :
    ∀ (i n : Nat), (h : i < n) → (fb_vec n)[i]'h = fb_one (i + 1) := by
  intros i n h
  unfold fb_vec; simp
  rw [Nat.add_comm]
```

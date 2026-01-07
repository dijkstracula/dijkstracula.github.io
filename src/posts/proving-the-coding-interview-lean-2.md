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
-- our implementation 

def fb_one (i : Nat) : String :=
  if i % 15 = 0 then "Fizzbuzz" else
  if i % 5 = 0 then "Buzz" else
  if i % 3 = 0 then "Fizz" else
  Nat.repr i

def fizzbuzz (n : Nat) : List String :=
  List.range' 1 n |> List.map fb_one

-- our specification

theorem fizzbuzz_of_n_is_length_n (n : Nat) : (fizzbuzz n).length = n := by
  unfold fizzbuzz
  simp

theorem fb_of_n_len_is_n (n : Nat) : (fizzbuzz n).length = n := by
  unfold fizzbuzz
  rw [List.length_map, List.length_range']

def main (args : List String) : IO Unit :=
  match args[0]? >>= String.toNat? with
  | none =>   IO.println "No argument or invalid ℕ"
  | some n => IO.println s!"fizzbuzz({n}) = {fizzbuzz n}"
```
```
$ lean --run FB.lean 15
fizzbuzz(15) = [1, 2, Fizz, 4, Buzz, Fizz, 7, 8, Fizz, Buzz, 11, Fizz, 13, 14, Fizzbuzz]
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
that knows its own length at the type level, so just like with `add_one_pos`,
the return type can _depend_ on the value of the function argument;
2) Encode the elements returned not as strings but as a finite type that
forces a "fizz", "buzz", "fizzbuzz", or number value.
:::

## A proof that connects `fb_one`'s behaviour to `fizzbuzz`'s

Before we tackle our TODO list, though, let's write another theorem to get 
our head back in the game; I'm going to guess this one will come in handy as a
lemma for proofs down the road.  The bulk of our problem specification invoves
statements relating how element `i` of the returned list relates to, well, what
gets passed into the `fb_one` helper.  Having a proof that states that
relationship more formally will help us connect later proofs about `fizzbuzz`
to ones about `fb_one`.  Sometimes this is called a _bridge proof_.  Let's
write it!

```lean4
theorem fb_one_to_fizzbuzz :
    ∀ (i n : Nat), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1)) := by

1 goal
⊢ ∀ (i n : ℕ), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1))
```

Note the annoying off-by-one here, since the `0`th element of the returned list
should be `fb_one 1`, and so on.

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
in two cases: one where the goal begins with a _quantified variable_ and
another where it begins with an _implication_:

::: note
1) If our goal looks like `∀ (x: t), expr` (read: "for all `x`s of type `t`,
`expr`"), `intro x` will add the proposition `x : t` (read: "suppose `x` is of
type `t`") into our context, and changes the goal to `expr`:
:::

```lean4
theorem fb_one_to_fizzbuzz_x :
    ∀ (i n : Nat), i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1)) := by
  intros i n

1 goal
i n : ℕ
⊢ i < n → (fizzbuzz n)[i]? = some (fb_one (i + 1))
```

Of course, the context doesn't tell us anything about what values `i` and `n`
have, since the whole point of a forall-quantifier is that _the values don't
matter_- whatever we're trying to prove better be true no matter what values
they take!

::: note
2) If our goal looks like an implication of the form `x -> y`, then `intro x`
adds `x` as a _hypothesis_ into our context and reduces the goal to just `y`.
The interpretation of a logical implication here is that knowing `x` is
_sufficent_ to prove `y`, so with `x` as an assumption, we need only prove `y`
to complete our proof.
:::

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

### Statically verifying no out-of-bounds errors

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

::: margin-note
Fun fact: statically avoiding bounds-checks was one of the main motivations
for [early work](https://dl.acm.org/doi/10.1145/277650.277732) on dependent types.
Interestingly, the argument was not for safety but for performance!  Xi and
Pfenning's paper has some pretty convincing speedups from being able to elide
bounds checks on programs with lots of array accesses.
:::
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
`Vector` is an example of an _indexed_ generalized algebraic datatype, which
even non dependently-typed languages like Haskell and OCaml let you implement.
See [these
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
return will hold `n` elements of type `String`, and so our type signature is going
to be `Nat -> Vector String n`.  Straightforward enough, but is implementing this
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
def fb_vec (n : Nat) : Vector String n := 
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

Here's the full proof.  Clearly `Vector`s give us a lot of built-in mechanism
to simplify our proofs!

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
constructors, we can turn an element into something else by pattern matching
over it (we'll see that this is _eliminating_ an element), we can attach
methods or implement typeclasses or traits based on them... in fact, why don't
we do that last one right now:

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

## At last, a real specification for Fizzbuzz

Let's try writing one a proof of one of our actual Fizzbuzz specifications -
following the design of our "program", we'll first prove that `fb_one i`, when
`i` is appropriately-chosen, is `Fizzbuzz`, and then extrapolate that to
`vb_vec[i]` under the same constraint for `i`.

::: margin-note
Note that I've deliberately written this theorem slightly differently than how
it appears in the implementation: here this theorem states a hypothesis about
`i % 3 = 0` and `i % 5 = 0`, whereas `fb_one` does a single check that `i % 15
= 0`.  Dafny had no trouble distinguishing without us explaining why that these
are saying the same thing.
:::
```lean4
theorem fb_one_i_mod_15_is_fizzbuzz:
  ∀ (i : Nat) (H3: i % 3 = 0) (H5 : i % 5 = 0), fb_one i = FB.FizzBuzz := by ...

1 goal
⊢ ∀ (i : ℕ), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz
```

### Intro and unfold, like usual

As usual, our first tactic involves introducing statements into our context
and unfolding some basic definitions.

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 -- NEW 
  unfold fb_one -- NEW

1 goal
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
⊢ (if i % 15 = 0 then FB.FizzBuzz else 
   if i % 5 = 0 then FB.Buzz else 
   if i % 3 = 0 then FB.Fizz else 
   FB.Num i) = FB.FizzBuzz
```

Notice that there's clearly one situation that makes sense here: the left-hand
side only matches the right-hand side when `i % 15 = 0`.  More subtly, though,
it also needs to be the case that if `i % 15 != 0`, it better not be the case
that our two hypothesis `i % 3 = 0` and `i % 5 = 0` also hold.

::: margin-note
Yes, you can extend Lean with custom tactics if you're so inclined!  They're
typically written as a macro that expands into operations over the Tactics
Monad.  (Since Lean's a pure functional language, maybe you surmised that we
would need something like the State Monad in order to remember and modify
the goal and its context.)
:::
Mathlib introduces a new tactic called `split_ifs` which can help us prove
both those situations:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5
  unfold fb_one
  split_ifs with H15 -- NEW

2 goals
case pos
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : i % 15 = 0
⊢ FB.FizzBuzz = FB.FizzBuzz

case neg
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : ¬i % 15 = 0
⊢ False
```

You might expect to see _four_ goals here because we have four branches in
`fb_one`'s nested-if.  It turns out that this tactic will automatically
simplify down and eliminate branches that it knows are logically impossible.
(You can play with the simpler `split` tactic to see the difference: the two
goals missing from our proof have obvious contradictions that `split_ifs` is
able to eliminate right off the bat.

### Focus in on subgoals with the `·` dot operator

This is, I think, our first example of a _structured_ proof, where a tactic
has broken our goal down into multiple subgoals for us to prove individually.

We can focus on the first goal with the `·` "bullet" operator - this will take
our context, which currently has two goals to prove, and "zooms in" on the
first one in the list.  (This should remind you of proving a lemma that you've
defined inline with `have`.)

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs with H15
  · --NEW

1 goal
case pos
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : i % 15 = 0
⊢ FB.FizzBuzz = FB.FizzBuzz
```

This is the "then" side of the `if` expression: when the conditional `i % 15 =
0` is true, then `fb_one` produces `FB.FizzBuzz`, which is exactly the
expression our theorem states it should.  A `rfl` is enough here.

### Proving `false` means hunting for a contradiction

The second subgoal is more complicated to solve, and introduces a really
interesting concept about what falsity means:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs with H15
  · rfl 
  · --NEW

1 goal
case neg
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : ¬i % 15 = 0
⊢ False
```

Our goal is to prove that the proposition `False` is true.  That seems...
actually impossible to do.  This whole time we've been crunching the goal down
until it's something that Lean can reduce to `True`, after all!

::: margin-note
It's not a coincidence that we encountered the principle of explosion right
about when we first encountered the _negation_ of a statement.  In Lean (as
well as Rocq and other similar languages), `Not x` is
[defined](https://github.com/leanprover/lean4/blob/2234c9116310b4c954ae42178e1f5d8e9795c682/src/Init/Prelude.lean#L223)
as the implication `x -> False`.  In other words, "not x" means "it is a
contradiction to be able to prove x"!
:::
There's an escape hatch of sorts here: by the logical principle known,
spectacularly, as both the [principle of
explosion](https://en.wikipedia.org/wiki/Principle_of_explosion) and _ex falso
quodlibet_.  It states that any goal, no matter how absurd it seems, can be
proven if you assume a contradiction.

Less philosophically-speaking: the purpose of this goal _actually_ is to show
that there's a contradition somewhere in our _context_.  It's hard not to see
where the contradiction is: we have both `i % 3 = 0` and `i % 5 = 0`, but also
`¬i % 15 = 0`.  If we can massage H3 and H5 into `i % 15 = 0`, then we've got
our two contradictory statements.

Well, let's do that, then: let's state that, actually, `i % 15 = 0`:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs with H15
  · rfl 
  · have H_15': i % 15 = 0 := by

1 goal
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : ¬i % 15 = 0
⊢ i % 15 = 0
```

Notice that the goal has changed, because we've stated something with `have`
that we are now going to prove.

I'll admit that it's been long enough since my undergrad math classes that I
wasn't entirely sure how to actually prove this!  I knew it had something to do
with 3 and 5 being coprime, and so probably falls out of the Fundamental Theorem
of Arithmetic or something.  I struggled for quite a while until I wondered
whether, like Rocq, if Lean happens to have the `lia` tactic.  Turns out it
does!

`lia` is another automated tactic that specifically solves goals involving
linear arithmetic, which is exactly what we've got on our hands here.  The docs
say it's ["inspired by modern SMT
solvers"](https://github.com/leanprover/lean4/blob/2fcce7258eeb6e324366bc25f9058293b04b7547/src/Init/Grind/Tactics.lean#L16)
and uses cool research like
[e-matching](https://leodemoura.github.io/files/ematching.pdf).  Automated
tactics like `lia` bridge the gap between writing Lean proofs entirely by hand
as we've been doing here, and handing off the entire proof burden to an
automated solver, like we did with Dafny.

All right, with our lemma proven, the trap's set:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs with H15
  · rfl 
  · have H_15' : i % 15 = 0 := by lia -- NEW

1 goal
case neg
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
H15 : ¬i % 15 = 0
H_15' : i % 15 = 0
⊢ False
``` 

Our contradiction is clear: certainly hypotheses `H_15` and `H_15'` can't
_both_ be true, so the only thing left to us is to close out the subgoal
by marking it as a proof by contradiction:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs with H15
  · rfl 
  · have H_15' : i % 15 = 0 := by lia
    contradiction --NEW 

Goals accomplished!
```

## Connecting it back to `fb_vec`

OK, let's see if we can quickly connect the proof we just wrote to one about
`fb_vec`.   Actually, you know what -- by now you've seen enough proofs that I
think _you_ should give it a try! Here's the scaffholding to get you started:

```lean4
theorem mod_15_is_fizzbuzz' : 
  ∀ (i n : Nat) (H : i < n), 
    (i + 1) % 3 = 0 → 
    (i + 1) % 5 = 0 → 
    (fb_vec n)[i]'H = FB.FizzBuzz := by
```

(You might benefit from knowing about the `exact` tactic: `exact e` closes the
goal if `e` is a proof of the goal.)

## What if we'd gotten the implementation wrong?

It's all fine and well if we prove something about an implementation we
already knew was correct.  Let's introduce a bug into `fb_one` and see
how our proof goes awry:

```lean4
def fb_one (i : Nat) :=
    if i % 5 = 0 then FB.Buzz else       -- NEW: This line and the line below
    if i % 15 = 0 then FB.FizzBuzz else  -- it were flipped!
    if i % 3 = 0 then FB.Fizz else
    FB.Num i
...
```

Hopefully you can see what goes wrong here: we'll never print out `FizzBuzz`
because the earlier `i % 5 = 0` check will satisfy cases where `i` is also
divisible by 15.

So what goes wrong when we try and prove our earlier theorem with a broken
implementation?  We'll hit a snag when it comes time to split on all the nested
`if`s:

```lean4
theorem mod_15_is_fizzbuzz : 
  ∀ (i : Nat), i % 3 = 0 → i % 5 = 0 → fb_one i = FB.FizzBuzz := by
  intros i H3 H5 
  unfold fb_one
  split_ifs

1 goal
i : ℕ
H3 : i % 3 = 0
H5 : i % 5 = 0
⊢ False
```

If this single remaining goal looks unsolvable, that's because ... it _is_
unsolvable!  This makes sense when you consider that the statement we're
trying to prove is fundamentally unsolvable.

You might remember that when we broke our Dafny implementation in a similar way
we got a lovely counterexample back from the solver.  Here we're not so lucky;
we don't get an _error_, per se, so much as just a partial proof that's
impossible to prove.

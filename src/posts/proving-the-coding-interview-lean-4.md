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
  * [Part three - completing the spec with tactic combinators](/posts/proving-the-coding-interview-lean-3)
  * [Part four - proof-carrying code](/posts/proving-the-coding-interview-lean-4)

All previous Proving The Coding Interview posts can be found
[here](/tags/provingthecodinginterview/).
:::

Last time we finished our Fizzbuzz specification, so we're arguably done with
this series!  Even with a problem as silly as Fizzbuzz, though, there's still
plenty of interesting avenues to go down.

In this lagniappe of a final post, I wanted to experiment with an alternate way
of implementing the problem that more aggressively leverages the features of
dependent types.  By the end of the post, we'll hopefully have an opinion on
whether we've improved our design or not!

## Proving two implementations are equal

You and I might well have arrived at different implementations of our `fb_one`
functions.  Stephen Diehl's superb [From Zero To
One](https://sdiehl.github.io/zero-to-qed/07_control_flow.html#fizzbuzz) page
has a different but probably-equivalent implementation to ours:

```lean4
def fb_one_sdiehl (n : Nat) : String :=
  match n % 3 == 0, n % 5 == 0 with
  | true,  true  => "FizzBuzz"
  | true,  false => "Fizz"
  | false, true  => "Buzz"
  | false, false => toString n

def fb_one_ntaylor (i : Nat) : String :=
  if i % 3 = 0 ∧ i % 5 = 0 then "Fizzbuzz" else
  if i % 5 = 0 then "Buzz" else
  if i % 3 = 0 then "Fizz" else
  Nat.repr i
```

::: margin-note
I'm going back to our original version that returned a String rather than a
`FB`, to simplify the proof and to make the (spoiler alert!) counterexample we
get back more obvious, though you can certainly write your own version that
proves that `toString (fb_one i) = fb_one_sdiehl i`.
:::
It doesn't look all that different to ours - at a quick glance, it uses a
`match` statement instead of our `if`-ladder, and calls `Nat.repr` instead of
using the `ToString` typeclass, but we should be somewhat convinced that no
matter what `Nat` we give it, we'll get the same String returned to us.

In most languages, it doesn't even make sense to ask what two functions being
"equal" means - in C, we could certainly compare a _function pointer_ for
referential equality, but that's as good as we can do statically.  Conceptually
we'd have to "run the functions on all inputs" and manually validate that the
returned values are the same.  (The "two functions are the same if you get the
same output for the same input" is called _function extensionality_, or
sometimes _pointwise equality_.) But, in the presence of mutable state, we'd
have to also make sure that their _side effects_ are also "equal" (whatever
that means??)

Lean, of course, doesn't have side effects.  And, we've seen the power that
one gains by having a theorem prover write statements about programs.  It
turns out that function extensionality _is_ a notion Lean is familiar with,
and we can write proofs to that effect!

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i

1 goal
i : ℕ
⊢ fb_one_ntaylor i = fb_one_sdiehl i
```

::: margin-note
Technically I did think of applying
[funext](https://lean-lang.org/doc/reference/latest/The-Type-System/Functions/#funext),
but let's pretend I don't know about that one.
:::
We've heard this song before.  I can't think of anything else to do but
`unfold` our two implementations.

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor --NEW
  unfold fb_one_sdiehl  --NEW

1 goal
i : ℕ
⊢ (if i % 3 = 0 ∧ i % 5 = 0 then "Fizzbuzz" else 
   if i % 5 = 0 then "Buzz" else 
   if i % 3 = 0 then "Fizz" else 
   i.repr) =
  match i % 3 == 0, i % 5 == 0 with
  | true, true => "FizzBuzz"
  | true, false => "Fizz"
  | false, true => "Buzz"
  | false, false => toString i
```

Now's a good time to handle one of our differences: `fb_one_sdiehl` converts
`i` to a string by `Nat.repr` whereas we used `Nat.toString`.  Luckily,
even though those functions are not nominally the same, it's a simple matter
to `have` a theorem that states they are, and `rfl` is enough to prove it.
Then we can rewrite `toString` away using that theorem.

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor
  unfold fb_one_sdiehl
  have repr_eq : toString i = Nat.repr i := by rfl -- NEW
  rw [repr_eq] --NEW

1 goal
i : ℕ
repr_eq : toString i = i.repr
⊢ (if i % 3 = 0 ∧ i % 5 = 0 then "Fizzbuzz" else 
   if i % 5 = 0 then "Buzz" else 
   if i % 3 = 0 then "Fizz" else 
   i.repr) =
  match i % 3 == 0, i % 5 == 0 with
  | true, true => "FizzBuzz"
  | true, false => "Fizz"
  | false, true => "Buzz"
  | false, false => i.repr
```

### `repeat` reapplies a tactic until the goal stops changing

Remember from last time that `split` decomposed the goal into different paths
that the progrma could go down; we used this while proving `mod_15_is_fizzbuzz`.
Our goal here is to keep `split`ting the `if` ladder until we've decomposed all
the code paths into subgoals.  `repeat` is a tactical that will do this for us:
it takes as argument a tactic, and keeps applying it until it reaches a _fixpoint_
(in other words, the goal stops changing.)

This expands out to, after trivial auto-simplification, six subgoals:

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor
  unfold fb_one_sdiehl
  have repr_eq : toString i = Nat.repr i := by rfl
  rw [repr_eq]
  repeat split -- NEW

6 goals
case isTrue
i : ℕ
repr_eq : toString i = i.repr
h✝ : i % 3 = 0 ∧ i % 5 = 0
⊢ "Fizzbuzz" =
  match i % 3 == 0, i % 5 == 0 with
  | true, true => "FizzBuzz"
  | true, false => "Fizz"
  | false, true => "Buzz"
  | false, false => i.repr

...

case isFalse.isFalse.isFalse
i : ℕ
repr_eq : toString i = i.repr
h✝² : ¬(i % 3 = 0 ∧ i % 5 = 0)
h✝¹ : ¬i % 5 = 0
h✝ : ¬i % 3 = 0
⊢ i.repr =
  match i % 3 == 0, i % 5 == 0 with
  | true, true => "FizzBuzz"
  | true, false => "Fizz"
  | false, true => "Buzz"
  | false, false => i.repr
```

So far that looks good: we have banished the `if` ladder from our goal, at the
expense of having a bunch of subgoals to prove individually.  Now we need to,
for every subgoal, `repeat split` the _match_ expression away. Recall the `<;>`
"xargs" tactical that will do this for us:

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor
  unfold fb_one_sdiehl
  have repr_eq : toString i = Nat.repr i := by rfl
  rw [repr_eq]
  repeat split <;> repeat split --NEW

5 goals
case h_1
i : ℕ
repr_eq : toString i = i.repr
h✝ : i % 3 = 0 ∧ i % 5 = 0
x✝¹ x✝ : Bool
heq✝¹ : (i % 3 == 0) = true
heq✝ : (i % 5 == 0) = true
⊢ "Fizzbuzz" = "FizzBuzz"

case h_2
i : ℕ
repr_eq : toString i = i.repr
h✝ : i % 3 = 0 ∧ i % 5 = 0
x✝¹ x✝ : Bool
heq✝¹ : (i % 3 == 0) = true
heq✝ : (i % 5 == 0) = false
⊢ "Fizzbuzz" = "Fizz"
...
```

Great!  Looks like we have either trivial goals (like in `h_1`) or obvious
contradictions involving modular arithmetic in our proof context.  We know
`lia` can handle both of those situations, so that tactic should let us prove
all our subgoals!  Let's try that and declare victory:

```lean4
theorem fb_one_eq : ∀ (i : Nat), fb_one_ntaylor i = fb_one_sdiehl i := by
  intros i
  unfold fb_one_ntaylor
  unfold fb_one_sdiehl
  have repr_eq : toString i = Nat.repr i := by rfl
  rw [repr_eq]
  repeat split <;> repeat split <;> lia --NEW 

unsolved goals
case h_1
i : ℕ
repr_eq : toString i = i.repr
h✝ : i % 3 = 0 ∧ i % 5 = 0
x✝¹ x✝ : Bool
heq✝¹ : (i % 3 == 0) = true
heq✝ : (i % 5 == 0) = true
⊢ "Fizzbuzz" = "FizzBuzz"
```

Wait, why didn't all our goals discharge...?

D'oh!!!  Stephen spelled his string "FizzBuzz", whereas I used a lowercase 'b'.
Not a bad reason to model your domain more abstractly (as we did with the `FB`
datatype), to avoid silly irrelevant string differences like this!  Yet another
reason why as an interview problem this is a clasically-bad one.  Does our
choice of capitalisation _really_ matter that much?

(By making this correction in either function, we get to see the final goal
solved and enjoy the "No goals" message in our editor.)

::: note
Interestingly, it seems like Dafny does _not_ support the notion of function
extensionality, so making the equivalent statement in Dafny wouldn't be
possible.  Given that we're free to mutate state in Dafny programs, maybe this
shouldn't come as a surprise to us.  There could well be other factors that
limit extensionality -- maybe there's some aspect of how Dafny's solver models
functions? -- but I'm not sure.  Again, interesting tradeoff between the two
languages, the style of programming they allow, and the second-order effects
of those design choices.
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

This makes FB a _type family_: it defines an infinite number of types, for each
possible `Nat` value.  OK, for a given `i`, what can we say about each of our
constructors?  Well, to construct a `Fizzbuzz` of type `FB i`, it better be the
case that `i % 15 = 0`.  For a `Num` to be a valid `FB i`, `i` must not divide
3 nor 5.  If each constructor took a _proof_ as argument for the relevant `i`,
then, a `FizzBuzz` could never be used in place where an `FB 12` was expected,
for instance.  Let's write that dependent type:

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

We can see this in action in our IDE: if we define a variable representing
what should be our 42nd entry in our produced Vector, what type should it
have?  Hopefully it's clear that it should be of type `FB 42`.

```lean4
def my_favourite_fb : FB 42 := -- TODO
```

::: margin-note
If you're convinced that there's truly only one value of a given `FB i` (a type
with one _inhabitant_ is what we call a _singleton type_), that might be worth
writing a theorem about.
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

## `fb_one` must provide the _evidence_ for each FB

Remember that last time, when we were stating and proving all these properties
about the `FB` constructors, we did these compile-time checks as part of a
theorem after the fact. The hope is that this might simplify the proof of our
specification without making it harder to write the implementation.  Let's see
if that's actually true.

Okay, with our above changes, `fb_one` no longer typechecks because we've added
an argument to `FB`. Let's start rewriting it.  Already, we can see we hit a
snag pretty quickly: in the "then" arm of the first `if`, we need to pass a
proof term to the FB.FizzBuzz constructor, but, where are we going to find one?

```lean4
def fb_one (i : Nat) : FB i :=
    if i % 15 = 0 then FB.FizzBuzz ??? -- TODO: what proof do we pass to the constructor?
```

Whatever pass to the constructor needs to be a proof that `i % 15 = 0`.
Of course, this is _exactly_ the proposition we know to be true, because
it's right there in the `if` conditional.  

So, here's fun thing we can do in Lean that I've never seen in any other
language: we can use a _dependent if_: at runtime, this behaves identically
to a good old-fashioned `if` special form, but at _typechecking time_, whatever
the conditional is, it acts as an assumption in our proof context.  Take a
look!

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

In fact, `lia` will be our workhorse for the remaining three cases:

```lean4
def fb_one (i : Nat) : FB i:=
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

### We're producing a `Vector` of ... what, exactly?

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

We can write a type like this down by defining `i` _inside_ the parameter
to the vector - it's a bit like moving a global variable inside a function
definition, sorta.  I'll show you the syntax first and then explain 
what it's saying, and then move on to what it _means_:

```lean4
[ <1, Num 1>     : (1, FB 1)
  <2, Num 2>     : (2, FB 2)
  <3, Fizz>      : (3, FB 3)
  <4, Num 4>     : (4, FB 4)
  ... 
  <15, FizzBuzz> : (15, FB 15)] : Vector (Σ i, FB i) 15
```

The elements of this Vector are no longer just `FB _`s, but a _dependent
pair_: We can read this _sigma type_ as saying "the elements of this Vector
are `FB i` _for some varying i_".

::: note
It's worth pausing and pondering about what Vectors this type rejects but also
incorrectly accepts.  For instance, does this type say anything about ordering
of the `i`s, or uniqueness?  Does every element of `Vector (FB n) n` (that is,
`[1]`, `[2, 2]`, `[Fizz, Fizz, Fizz]`, and so on) have a one-to-one
correspondence with elements in `Vector (Σ i, FB i) 15`?
:::

## `fb_vec` must now produce a dependent pair

The change for `vb_vec` is pretty mechanical: rather than just mapping over
the `Vector` of `[1, 2, ... n]` with `fb_one`, we said just now that instead
we need to produce a _dependent pair_.  Such a pair is constructed with
the angle brackets `⟨` and `⟩`: the first element of the pair is the `i` 
value that will fix the type `FB i`, and the second element is the expression
that produces the `FB i` itself.  This second element is sometimes called
the _witness_ of the type: it's another form of evidence to the type system,
namely a proof that a value of type `FB i` is constructable!

We know for sure that an `FB i` is constructable because that's the return
type of `fb_one i`.  So, our `fb_vec` function is now:

```lean4
def fb_vec (n : Nat) : Vector (Σ i, FB i) n :=
  Vector.range' 1 n |> Vector.map (fun i => ⟨i, fb_one i⟩)
```

---
layout: post.njk
title: "Proving the Coding Interview: Lean vs Dafny cage-match"
date: 2026-01-02T00:00:00-05:00
tags: [post, lean, verification, provingthecodinginterview]
excerpt: "Is Fizzbuzz easier to write in Lean, or just differently hard?"
---

Back in grad school, I ran a [directed reading
group](https://sites.google.com/view/utdirp) for undergrads interested in the
intersection of systems and PL research.  Most weeks we just discussed papers,
but the final session of the semester was special: I'd tell them, "Okay, all
term you've seen what others have built; today, let's write and verify some
programs of our own!" So, we'd sit in a conference room with a text editor and
a box of donuts, and bang out a few verified insertion sorts in the various
languages used in the semester's papers.  (Looking back, it's a bummer that
this was as close as I ever got to actually teaching in the program, and that
this was one of the few genuinely-enjoyable parts of the PhD.)

Repeatedly writing the same program in different languages was always
illuminating, because we'd get tripped up on wildly-different parts of the
implementation, depending on what the given language's strengths and sharp
corners were.  In an [earlier](/posts/proving-the-coding-interview/)
installment, we implemented everyone's least-favourite interview question,
Fizzbuzz, in the Dafny language.  We saw how natural it was to program in
Dafny: we programed with loops, common datatypes and objects, and mutable
variables, just like in a Real Language(tm), and annotated our code with
logical propositions (our _program specification_). Dafny's _automated prover_
would do the rest: it would attempt to verify our program and either give us
the Big Okay, or error out with a counterexample indicating how our
implementation diverged from the spec.  It felt like magic, but things are
never as simple as they seem.  We had to be careful to:

* Explicitly state _loop invariants_ so that the compiler would understand
  what changed (and what stayed the same!) between iterations;
* Manually write common routines (like toString functions, notably) that the
  standard library didn't provide for us;
* Avoid writing specs that might cause the underlying automated solver to time
  out

What would it mean if it didn't necessarily have to be this way?

## The Lean programming language

[Lean](https://lean-lang.org/) is a fundamentally different kind of programming
language to Dafny: It's both a programming language and interactive proof
assistant.  (If you've heard of languages like Rocq (formerly Coq), Idris, or
Agda, it's definitely cut from the same cloth).  Like Dafny, it's actively used
in industrial settings like the AWS Automated Reasoning group, and has also
found its way into highly-theoretical settings like mathematics research.

In theory, Lean's design avoids all of Dafny's sharp corners:

::: margin-warning
Don't fall into the trap of thinking that purity is a moral judgement.  All
"pure" means is that functions don't have side-effects like mutating global
variables, raising exceptions, or I/O. Don't be like my ex-coworker who
compared non-pure programming to the antivaxxer movement.
:::
* It is a _pure functional language_, with only recursion and no mutable
  state, we don't have to worry about writing tricky loop invariants (since
  we can't even syntactically write a loop!);
* There's enough of a third-party ecosystem in Lean that we shouldn't have to
  reinvent the wheel for simple helpers, like we had to do with our
  Dafny `toString()` function;
* As a proof-assistant, Lean doesn't attempt to automatically prove your
  programs correct as Dafny does, but relies on the programmer to write and
  prove _theorems_ about them.  This means there's no SMT solver with unstable
  performance characteristics to worry about, as you may have noticed if you
  played with our Dafny fizzbuzz program yourself.  Once your theorems and
  proofs are written, verifying your program boils down to just typechecking
  it.

Of course, it also stands to reason that what was easy to do in Dafny might
be problematic in Lean.  Shall we see if that's in fact true...?

## Our problem statement, revisited

Fizzbuzz as a problem has not become any less familiar nor any less irritating
since my Dafny post got published all those years ago.  But, just to remind us
what we're trying to do here:

::: tip
First, construct a list of strings of length `n`, such that the following hold
for all values `i` from 1 through to n:

1) If `i` is a multiple of 3 (but not of 5) then the `i-1`th element is the string "Fizz";
2) If `i` is a multiple of 5 (but not of 3) then the `i-1`th element is the string "Buzz";
3) If `i` is a multiple of 15 then the `i-1`th element is the string "Fizzbuzz";
4) Otherwise, the `i-1`th element equals the string representation of `i`.

Then, print out, separated by a newline, every element in the list.
:::

::: note
Enough of you got on my case that the Dafny specification was zero-indexed that
I've adjusted this here - now I have to think hard about avoiding off-by-one
errors between the value `i` residing at index `i-1`.  The good news, though is
that verifying our implementation against this specification can help me get
this right!
:::

## A starting non-solution solution

::: margin-note
A note to the Lean experts: I'm new to the language and most of my proof
assistant experience has been in Coq, and I'll be avoiding opaque `crunch`-like
automated tactics and tacticals in favour of clear and explicit steps, so
please don't get too upset if my solution here is not super idomatic or
character-count optimised!
:::
If you're comfortable with more, ahem, "popular" functional languages like
Scala or OCaml, you might write Fizzbuzz in such a way:

```lean4
def fb_one (i : Nat) : String :=
  if i % 15 = 0 then "Fizzbuzz" else
  if i % 5 = 0 then "Buzz" else
  if i % 3 = 0 then "Fizz" else
  Nat.repr i

def fizzbuzz (n : Nat) : List String :=
  List.range' 1 n |> List.map fb_one
```

As with the Dafny example, I don't expect you to pick up every piece of
syntax, but: this defines the function `fizzbuzz` with one argument `n`
of type `Nat`, and produces a List of Strings (this polymorphic type is written
`List String`; imagine that `String` was in angle-brackets like it'd be in a
more conventional syntax).  Following the `:=` is the body of the function,
which calls a helper function `fb_one`.

::: margin-note
In case it wasn't clear by now, when you call a function you don't wrap the
arguments in parens, so if in C you'd write `f(x, y, g(z))`, you'd simply in
Lean write `f x y (g z)`.
:::

This function first creates the `List Nat` expression `[1, 2, 3, 4, ... n+1]`
and then "pipes" each number into the string-creation heper function.  So,
`fizzbuzz 5` would produce `["1", "2", "Fizz", "4", "Buzz"]`, as we would hope
it would.  (You can type `#eval fizzbuzz 5` in your Lean file and the IDE will
show the result of that computation.)

As a child of the [How To Design Programs](https://htdp.org/) curriculum, I
like explicitly separating out and giving a name to the helper that we pass to
`List.map`, as opposed to just writing it as an anonymous function in the body.
In HtDP, this was so we could more easily write unit tests, but here, of
course, the hope is that a more decomposed implementation will also allow a
more decomposed specification.

::: note
If you're interested in typing along with this post, great!  You'll want to be
sure to include
[mathlib4](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
as a dependency for your Lean project, since it includes theorems about modular
arithmetic that we'll want to make use of.
:::

## Our first theorem

In fact, why don't we codify a fact like "we expect `fizzbuzz 5` to be some
particular list of elements" by stating the above `#eval` more formally!  In a
lot of languages we might write an `assert()` or a unit test or something;
here, we'll do it in Lean's proof system by by stating it as a _theorem_:

```lean4
theorem fizzbuzz_thm : fizzbuzz 3 = ["1", "2", "Fizz"] := rfl
```

In VS Code, I see a little blue check next to the theorem, indicating that
Lean has validated it.  (If I changed the final element of the list, or broke
something in `fizzbuzz`, I'd, as you'd expect, see an immediate and
reasonable-sounding error in my IDE:

:::warning
```
the left-hand side
  fizzbuzz 3
is not definitionally equal to the right-hand side
  ["1", "2", "Buzz"]
```
:::

Before going any further, you should take a moment and think about how you
would convince yourselves that this equality always holds.  (It probably
involves mentally evaluating the left hand side and confirming the final result
happens to be the right-hand side.)  

While it's pretty easy to see that it's the case here, and would still be easy
to see even if `fizzbuzz` was written in Python or Java or something, in more
complicated functions you never know if some non-obvious piece of global
mutable state will ultimately change the returned value between different
function calls.  

::: margin-note
I once worked at a company whose large C codebase had a
2000-line long function `void poke(void)` - clearly the _only_ thing that
function could ever do is read and modify global variables!
:::

Lean's functional purity means such mutable state fundamentally can't exist
anywhere in the program, so the function's output can only vary based on its
inputs.  For formal proofs about our programs, this is an incredibly nice
property to have.

### So what is a theorem, really?

Calling it a "theorem" certainly _sounds_ fancier that a test, but how is it
actually different than one?

Here's the kicker: no part of this definition has any runtime semantics; you
can think of it as invisible "ghost code" (which should sound familiar to you
from Dafny).  the _proposition_ that this theorem states, `fizzbuzz 3 = ["1",
"2", "Fizz"]` might at first glance look like a boolean expression, but just
like with Dafny's invariants, it's not! Look where it resides in the theorem
definition, between `:` and `:=`.  In the function definition earlier, this was
where the return type went.  And with good reason: the proposition `fizzbuzz 3
= ["1", "2", "Fizz"]` is, in lean, the _type_ of the theorem!!

That a type can look like this might feel ridiculous if you've never seen a
type system like Lean's before. In most languages that, well, we can make money
programming in, a type doesn't tell you much more than the set of possible
values that a variable can have. If you're used to low-level programming, maybe
you think of a type more in terms of its bitwise-representation in memory.

Here, though, we're thinking about a type as being the _same_ as a logical
proposition.

Edwin Brady (and probably others, but I learned it from his book) draw a nice
comparision between types and tests: a test can demonstrate the _presence_ of a
bug, but a type can demonstrate the _absence_ of a bug.  (Of course, this is
contingent on having a type system expressive enough to state interesting facts
about your program. `int` and `String` might technically be "logical
propositions" in Java, but they're not logically proposing anything
to us).

::: margin-note
You might be wondering why, if we prove theorems through its type system,
Lean doesn't seem to have much in the way of type inference.  It turns out that
its type system is too expressive to support it - it's in fact proven to be
formally undecidable!  This is why we, the programmer, need to help Lean along
by writing proofs ourselves.

Because Dafny's type system (and underlying prover) is not as expressive as a
fully-dependent type system like Lean's, we give up the ability to articulate
certain propositions but we gain the ability for Dafny to automatically deduce
more aspects of their correctness.  I find this tradeoff really fascinating and
there is lots of interesting research, like [liquid type
systems](https://www.youtube.com/watch?v=C5PuBeiWaSA), that plays in this
space.
:::
Back to figuring out the syntax of our theorem: in the function definition,
what followed after `:=` was the function body. What this is is our explanation
-- our _proof_ -- of _why_ this theorem is correct.  If you want to think of
this theorem as "a function of zero arguments, that evaluates to `rfl`", that's
not a terrible way to do it for now.  It's certainly not far off from how
Lean's typechecker thinks about it, at least.

The good news is that this is an easier process than writing, say, first-year
discrete math proofs, because even though you have to write the proof yourself,
Lean will tell you if you made a mistake in the proof, like assuming something
that isn't true or missing an edge case in a case analysis or something.

### So what is a proof, really?

We can look at the definition of `rfl` in Lean's frankly excellent
documentation to understand what the body of the theorem -- the theorem's
_proof_ -- is doing:

::: tip
`rfl : a = a` is the unique constructor of the equality type.

This is a more powerful theorem than it may appear at first, because although
the statement of the theorem is a = a, Lean will allow anything that is
definitionally equal to that type. So, for instance, 2 + 2 = 4 is proven in
Lean by rfl, because both sides are the same up to definitional equality. 
:::

Huh, so `rfl` is a _constructor_ for a value of type `a = a`!  Again, `a = a`
doesn't look like the sort of type we're used to, so if you want to mentally
substitute the traditional polymorphic `IsTheSame<T, T>` type until you're more
familiar, that's fine.  So, in Java, the body of an equivalent "theorem" might
be `return new IsTheSame<>()` or something like that. 

This is a theme -- as well as a fundamental result in theoretical computer
science -- that we'll keep coming back to: a _type_ states a logical
proposition, and the _proof_ of that logical proposition takes the form of some
computation, like the body of a function that returns a value of that type.

::: note
I always like getting my bearings by seeing what we could express in a
not-fancy type system.  It's pretty easy to imagine in, say, Java, getting a
`IsTheSame<Employee, Employee>` to typecheck - `Employee` it makes sense that
any class (irrespective of the the equality of any _objects_ of that class) is
identical to itself. If we implemented `IsTheSame` with variance, it'd also be
reasonable to expect `IsTheSame<Employee, Person>` or `IsTheSame<Employee,
Student>`, since they presumably share a common superclass.

What we certainly _can't_ do in Java is to write what we just wrote in Lean:
Whatever goes between the angle brackets in Java needs to be a type, not an
arbitrary program expression (which PL people typically call "terms"), so
`IsTheSame<2 + 2, 4>` would for sure be totally nonsensical, because in most
languages types and terms occupy different _syntactic domains_ - this wouldn't
even parse, much less typecheck.  Clearly what Lean's type system is doing is
blurring the lines between types and terms somehow.  We'll have a lot more to
say about this down the road.
:::

So, if we're writing a theorem whose goal it is to prove that two things are
equal to each other, that will probably mean we'll be using `rfl` at some point
in its proof. (In general: two things might be equal but not _definitionally_
so, so we might need to first transform the left and right-hand sides ourselves
to get them into a state that `rfl` can handle.)

## When `rfl` isn't enough

Here's another theorem that we might want to write: let's suppose we want to
validate that the the list that `fizzbuzz 3` produces isn't empty.  We might
start the theorem like this:

```lean4
theorem fb_of_3_len_nonzero : 0 < (fizzbuzz 3).length := -- TODO: finish me
```

`rfl` is all about proving equalities, but we have an _inequality_ here, so
it's not going to help us here.

In order to complete this proof, we're going to not directly return a
type constructor like `rfl` but instead use Lean's _tactic system_.  Tactics
are like "commands" in Lean that allow us to transform types into (hopefully)
simpler ones.  So, a tactics-oriented proof looks like a sequence of rewrites.

To enter tactics mode, we use the `by` keyword in the theorem body:

```lean4
theorem fb_of_3_len_nonzero : 0 < (fizzbuzz 3).length := by
```

And the IDE now shows us, in its "tactics state" panel:

```lean4
1 goal
⊢ 0 < (fizzbuzz 3).length 
```

This is sometimes called the _proof context_. 

Right now we just have one goal (the expression that follows the sideways-T
thing) but in more complicated cases we might have several goals to handle
individually, or might list hypotheses that have been introduced to us.

::: margin-note
This is the first example of a common theme, here: Dafny figured out
automatically what we have to explicitly state in Lean.  For this cage-match to
not be utterly one-sided, we better make sure that we get something in return
for this tradeoff.
:::

To prove a goal means to simplify it down, step by step, to something that Lean
axiomatically knows to be true.  (We did this earlier with `rfl`; having an
equality where both sides are "the same" is enough to satisfy the proof
assistant.)

## Tackling the proof with some basic tactics

So now we're kind of on our own!  It's now up to our intuition to transform
this goal into something that's "obviously" true.  This is a problem if you
are new to proof assistants and haven't yet developed your intuition!

Here's how I proved this theorem: I started with the following proof and
proof context:

```lean4
theorem fb_of_3_len_nonzero : 0 < (fizzbuzz 3).length := by

1 goal
⊢ 0 < (fizzbuzz 3).length
```

That is, the goal starts out by looking just exactly like the theorem we're
trying to prove.  Where can we go from here?

### `rw` rewrites the goal based on a known equality

What can we say about what `fizzbuzz 3` evaluates to?  Well, by the theorem
we wrote earlier, we have a _proof of equality_ about its value.  So, we can
use the `rw` tactic with `fizzbuzz_thm` to transform the goal into:

```lean4
theorem fb_of_3_len_nonzero : 0 < (fizzbuzz 3).length := by
  rw [fizzbuzz_thm] -- NEW

1 goal
⊢ 0 < ["1", "2", "Fizz"].length
```

::: margin-note
As a rough heuristic, usually, but not always, if your goal is getting smaller
or simpler, you're on the right track. 
:::
A theorem that helps us prove another one is sometimes called a _lemma_.
Rewriting with `fizzbuzz_thm` has banished the function call away, leaving
us with the raw list expression (that we then take the length of).  This feels
like pretty good progress so far!

### `unfold` replaces something with its definition

::: margin-note
We could have, in the first proof above, unfolded `fizzbuzz` instead of using
our existing theorem and tried to simplify from there.  Maybe you could give
that a try yourself!
:::
It's clear to you and me that a list of three elements has length 3, but
we have to think about how that can be made clear to the proof assistant.
The `unfold` tactic takes as argument the name of something in scope and
replaces it with its definition.  Let's see what happens when we apply this
tactic on the `length` function:

```lean4
theorem fb_of_3_len_nonzero : 0 < (fizzbuzz 3).length := by
  rw [fizzbuzz_thm]
  unfold List.length -- NEW

1 goal
⊢ 0 < ["2", "Fizz"].length + 1
```

This makes sense if you're familiar with how a length function would be
[recursively
written](https://github.com/leanprover/lean4/blob/2234c9116310b4c954ae42178e1f5d8e9795c682/src/Init/Prelude.lean#L2987-L2993)
in a functional language - the length of a list of three elements is one
greater than the length of the list of two elements.

This might not feel like a big change but it's kind of the lynchpin of the
proof: Lean might not know exactly what the length of `["2", "Fizz"]` is.  But,
something that's foundational to the natural numbers is that _any_ natural
number plus 1 has to be greater than zero.  If we can remind Lean of that,
by finding a built-in theorem that states that, we've won!

::: margin-note
As much as I'm an LLM cynic, I have to concede that describing something I want
to prove in natural language, having it search for a potentially-useful
theorem, and seeing if it works to complete the proof would be _really_ handy.
These so-called _neurosymbolic_ approaches, which combine "AI" with formal
methods, are super hot in the research community right now.
:::

### `apply` "calls" an existing theorem

In a lot of ways, the hardest part of writing these sorts of proofs is finding
built-in theorems to help you out.  With the help of Lean's [proof search
website](https://loogle.lean-lang.org/?q=0+%3C+_+%2B+1), I searched for
all theorems in the Lean standard library shaped like "`<something>` is less
than `<something else> plus one`" and found a great candidate:
[Nat.add_one_pos](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html#Nat.add_one_pos)!

Let's take a look at this theorem definition:

```lean4
theorem add_one_pos (n : Nat) : 0 < n + 1 := ...
```

::: margin-note
Another way, perhaps more natural to mathematicians than programmers, to write
this theorem is to use the `forall` keyword in the proposition:
`∀ n : Nat, 0 < n + 1`.  To the best of my knowledge, Lean treats these two
propositions as identical under the hood.
:::
Unlike our theorems so far, `add_one_pos` takes an `n`, just like a function of
one argument would. And interestingly, `n` also appears in the return type
(that is, the theorem's proposition)!  You could read this theorem aloud as
"for all natural numbers `n`, zero is less than the successor of `n`."


::: note
We say that the type _depends_ on the term `n`; even though would also be
reasonable to say that `ArrayList<T>` depends on the type variable `T`, that
piece of terminology is reserved specifically for terms.  In the followup post
to this one, we'll see (and maybe write?) a few more types like this.

Type systems that allow you to express such types are, perhaps unsurprisingly,
called _dependent type systems_, and they're about as powerful and expressive
as type systems get.
:::

::: margin-note
Applying a theorem doesn't always automatically complete the proof - for
instance, if our goal was to prove `n-1 < n`, and we applied the theorem
[Nat.sub_one_lt](https://leanprover-community.github.io/mathlib4_docs/Init/Data/Nat/Basic.html#Nat.pred_lt),
our goal would next be to prove that the antecedent proposition `n ≠ 0` holds
(Think about how n being nonzero is a requirement for `n-1 < n` to be true for
the Nats!). But since `Nat.add_one_pos` isn't an "if-then" implication, we're
all done!
:::
If we _applied_ this theorem to our goal with the tactic `apply Nat.add_one_pos
<some argument>`, our goal would be transformed into the theorem's proposition,
namely `0 < <some argument> + 1`.  Here's how this is different from _rewriting_
the goal with `rw`: Here, we're reducing our goal, which we haven't proven,
into the goal of another theorem, _which has been proven_!  In this case, this
is enough complete our proof!

What's `add_one_pos`'s `n` in our theorem's goal?  It's `["2", "Fizz"].length`,
so we would pass that term in as an argument.  When we do so, Lean tells us our
proof is complete!

::: note
Technically, Lean can infer what argument we want so we don't have to
explicitly pass it in. Lots of proof assistants have these sorts of syntactic
shortcuts to abbreviate the proof, but it makes what's happening a bit opaque.
I'm being as explicit as possible here just to keep the mechanism clearer.
:::

```lean4
theorem fb_of_3_len_nonzero : 0 < (fizzbuzz 3).length := by
  rw [fizzbuzz_thm]
  unfold List.length
  apply Nat.add_one_pos (["2", "Fizz"].length) -- NEW

0 goals
Goals accomplished!
```

::: margin-note
By far the _worst_ feature of Lean is that, unlike Coq, you do _not_ close out
a finished proof with the [QED](https://en.wikipedia.org/wiki/Q.E.D.) keyword.
Boo!
:::
As virtuous as we might feel for having completed the proof, this might not feel
as push-button as it would have in Dafny.  But, when we got stuck in Dafny with
a missing invariant, the error messages often didn't guide us to what needed to
be added.  By contrast, Lean will always show us the state of the incomplete
proof, leaving us a trail of breadcrumbs to follow at every step.

## Our first Fizzbuzz specification

When we saw `Nat.add_one_pos`, we learned that theorems can take arguments.
Given that `(fizzbuzz 3).length = 3`, maybe we're now inspired to make a
general statement about _all possible_ calls to the function:

```lean4
theorem fb_of_n_len_is_n (n : Nat) : (fizzbuzz n).length = n := by 
  -- TODO: what tactics can we apply to prove this statement?

1 goal
n : ℕ
⊢ (fizzbuzz n).length = n
```

You might read this theorem aloud as "for all natural numbers `n`, `(fizzbuzz
n).length = n`", and note that this covers the first sentence in the
specification: "First, construct a list of strings of length `n`, ...". 

::: margin-warning
Sometimes hypotheses are called _assumptions_ in formal logic.  Don't mistake
this for the colloquial "ass-out-of-you-and-me" meaning of "assume": Lean's
type system is _sound_, which means if Lean introduces a hypothesis into your
context like it did with `n`, you can trust that this was a correct thing for
it to do.
:::
Notice we have something new in our context: `n : ℕ` is a _hypothesis_
indicating that there's a value `n` of type `Nat` that we can make use of in
our goal.  You can think of it like defining a local variable in a function,
or, in a hand-written proof, a statement to the effect of "Let n be a natural
number."

### Tackling the body of `fizzbuzz`

Well, we don't have a lemma to tell us anything specifically about
`fizzbuzz n`.  Guess we could do worse than just unfolding `fizzbuzz` itself
to see if there's anything in its definition that can help us out.

```lean4
theorem fb_of_n_len_is_n (n : Nat) : (fizzbuzz n).length = n := by 
  unfold fizzbuzz -- NEW

1 goal
n : ℕ
⊢ (List.map
      fb_one
      (List.range' 1 n)).length = n
```

### Exploiting theorems about `List`s

It better always be the case that if you map over some list, you get back a
list with the same number of elements.  With a little bit of a [proof
search](https://loogle.lean-lang.org/?q=%28List.map+_+_%29.length), we can see
that some kind library maintainer has written down the
[List.length_map](https://github.com/leanprover/lean4/blob/2fcce7258eeb6e324366bc25f9058293b04b7547/src/Init/Data/List/Lemmas.lean#L1062-L1065)
theorem for us!  It produces the equality proof `(as.map f).length = as.length`
for all lists `as` (in our case, `List.range' 1 n`) and all functions that can
map over them (in our case, `fb_one`).

Before proceeding, see if you can remember what tactic we can apply to this
theorem to help us make progress on our goal.

```lean4
theorem fb_of_n_len_is_n (n : Nat) : (fizzbuzz n).length = n := by
  unfold fizzbuzz
  rw [List.length_map] -- NEW

1 goal
n : ℕ
⊢ (List.range' 1 n).length = n
```

If you guessed `rw`, you're right!  `List.length_map` is a statement about
equality, and our goal to prove is the left-hand side of that equality.  Notice
that owing to the right-hand side of `List.length_map`, any mention of `fb_one`
is banished from our goal!  This simplification feels promising to me.

What we're left with is another plausible goal, and good news, with a bit more
[proof
search](https://loogle.lean-lang.org/?q=List.length+%28List.range%27+_+_+_%29)
we've found a nice property about `List.range'`: in essence, it states `(range'
s n).length = n`!
[match](https://github.com/leanprover/lean4/blob/2fcce7258eeb6e324366bc25f9058293b04b7547/src/Init/Data/List/Range.lean#L32-L34)!

Once you fill in the arguments for `s` and `n`, this is exactly what's left in
our goal, so this completes the proof.

::: margin-note
We can group multiple adjacent rewrites onto one line like this: `rw
[List.length_map, List.length_range']`. 
:::
```lean4
theorem fb_of_n_len_is_n (n : Nat) : (fizzbuzz n).length = n := by
  unfold fizzbuzz
  rw [List.length_map]
  rw [List.length_range'] -- NEW

0 goals
Goals accomplished!
```

## Simplifying proof-writing with automation tactics

We had a slightly annoying proof-writing loop just now: our path to the goal
was clear but we had to hit a search engine to figure out the exact name of
the theorem we wanted to use.  Lean is able to take over this process for us
in simple cases with the `simp` tactic: it tries to simplify the goal down
by exploring some possible theorems to apply or rewrite with.  Trying it out
is a good first strategy when you're not sure how to proceed.

::: margin-note
Interestingly, there's a tactic called `aesop` which tries to prove theorems
with an SMT solver, just like Dafny.  I've never used it but maybe it's useful
in some cases!
:::
Using automation tactics can make your proof a bit more opaque if you're not
sure exactly _how_ your goal changed.  The variation `simp?` will show in the
context which helpful theorems it found.  (There's no guarantee that `simp`
will find an _efficient_ or _intuitive_ path, though!)

## Thinking in Lean means thinking in types, which we should all do anyway

We _could_ proceed with trying to write some theorems about, say, every third,
fifth, and fifteenth element of `fizzbuzz n`, but we're leaving some complexity
on the table by doing so.  Think about what each of those theorems would have
to state and how wd'd have to try to prove them: "Every 5th index in the
produced list contains a string that ends, case insenstively, in 'buzz'" would
involve some annoying list operations and substring slicing.  This sounds
brittle to get right.

Let's put aside all this fancy theorem proving stuff and just look a bit at the
type signature of our `fizzbuzz` function: it consumes a `Nat` and produces a
`List String` (we write this function type with an arrow between each argument
and the return type, so: `Nat -> List String`).  Here's a thought experiment:
in what ways could a broken Fizzbuzz implementation still satisfy this
signature? I can think of at least a few different ways:

::: tip
1) It could return a list of length unequal to the input value.  (In other
words, it would violate the theorem we just wrote.)  In the worst case, it could
just unconditionally return the empty list!  The type checker might be satisified
but we certainly wouldn't be.
2) The strings in the list might not relate to the the Fizzbuzz problem.  I could
produce the first `n` words of Jabberwocky and in the absence of any theorems
stating otherwise, Lean would be perfectly happy with it.  
:::

By contrast: a way this function could _not_ be broken is if we passed a
negative number to the function.  That's because the input argument's type is
not an `Int` but rather a `Nat`.  And, the good news is that we were at least
able to write a theorem guaranteeing that the first situation couldn't happen.
So, we are _somewhat_ taking advantage of Lean's cool feautres.

Nonetheless, though, it kind of feels like we're being a bit sloppy with
our type signatures and are hoping that our theorems will pick up the slack
for us.  This might not be the best way to program in Lean, and, it might not
even be the best way to program in Scala or OCaml (or Java (or Python!)!)

Perhaps the more "type-friendly" way to write this function would be to:

::: tip
1) Produce not just an ordinary `List` of values, but a special collection type
that knows its own length at the type level, so just like with `add_one_pos`,
the return type can _depend_ on the value of the function argument;
2) Encode the elements returned not as strings but as a finite type that
forces a "fizz", "buzz", "fizzbuzz", or number value.
:::

So, we'll make a modification to our English-language specification:

::: tip
First, construct a list of values, of length `n`, such that the following hold
for all values `i` from 1 through to n:

1) If i is a multiple of 3 (but not of 5) then the `i-1`th element is an internal representation of "fizz";
2) If i is a multiple of 5 (but not of 3) then the `i-1`th element is an internal representation of "buzz";
3) If i is a multiple of 15 then the `i-1`th element is an internal representation of "fizzbuzz";
4) Otherwise, the `i-1`th element equals an internal representation of `i`.

Then, print out, separated by a newline, every element in the list, after
converting them from their private representation to their expected string
form.
:::

Next time, we'll do this simple refactoring and then see where that leads us.

## Conclusion: how's the cage match going?

Frankly, so far, it doesn't seem like things are looking good for Lean.  By the
end of the first Dafny post, we had an almost verified Fizzbuzz implementation,
whereas here it feels like we've been just building type-theoretic mechanisms
to get off the ground.  There's a saying about programming in types: it goes
fast but _feels slow_.  In the next section, we'll design a more
"type-oriented" function, get it verifed, and confirm whether that saying's
actually true!

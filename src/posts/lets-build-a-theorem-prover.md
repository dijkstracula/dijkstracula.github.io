---
layout: post.njk
title: "Let's Build a Theorem Prover: Decision procedure lifestyle trends"
date: 2022-12-07T01:22:23.770Z
tags: [post, sat, logic, verification]
excerpt: "The president has ordered all programmers to maximise their automated reasoning with these weird tricks! Logical agents hate this!"
---

*This post originally appeared on [Cohost](https://web.archive.org/web/20241104063350/https://cohost.org/nathan/post/372692-let-s-build-a-sat-so).*

---

*The president has ordered all programmers to maximise their automated reasoning with these weird tricks!  Logical agents hate this!*

Last night I was talking to a friend about how I should write more, and then only a few hours later I found myself wide awake at 2:30 AM, so what better time to get comfy and write a bit about something I find cool?

If you're a computer-toucher, I could give you a boolean expression like `(true or false) and (not true)` and you could you could probably tell me, either by staring at it or typing it into Python, that it would evaluate to `false`.  I could also make the expression slightly irritating by giving each *boolean literal* its own variable, like this,

```python
$ python -q
>>> (b1, b2, b3) = (True, False, True) # Assign values to each variable...
>>> (b1 or b2) and not b3              # ...and evaluate the formula.
False
```

...but that wouldn't fundamentally change anything; as expected, it still evaluates to False when we substitute values for its variables.  With a bit of thinking, I can modify those assignments such that our formula now evaluates to True:

```python
>>> (b1, b2, b3) = (True, False, False) # Now, b3 is true...
>>> (b1 or b2) and not b3               # ...evaluate the same formula with new variable bindings...
True
```

The *boolean satisfiability problem* (SAT for short) automates this job for us: I give it as input a boolean formula, and it tells me assignments to that expression's variables such that if we *were* to evaluate that formula with those variable assignments, it would evaluate to true:

```python
>>> (b1, b2, b3) = [None for i in range(3)]
>>> find_me_satisfying_assignments_please((b1 or b2) and not b3)
>>> (b1, b2, b3)
(True, False, False)
```

(Of course, I can come up with a contradictory formula like `b1 and (not b1)`: no amount of thinking will get us a  assignment to `b1` that makes the formula true, and that's ok - it should tell us that that's the case, or throw an exception, or something.  The thing that matters is that it should never lead us astray by giving us the wrong answer, and should eventually stop computing and give us back a correct answer.)

For a long time I had never really thought of SAT as an interesting problem: I learned a bit of complexity theory in school and understood that you can formulate all lots of interesting, seemingly-unrelated problems like graph traversal and circuit design as SAT problems, but I also knew how to throw around words like NP-completeness, which any middling student like me knew meant "we don't really have a better way to solve this problem than by brute-forcing all possibilities":

```python
>>> import itertools
>>> for (b1, b2, b3) in itertools.product([True, False], repeat=3):
...     if ((b1 or b2) and not b3):
...             break
...
>>> (b1, b2, b3)
(True, True, False)
>>>
```

The loop above *enumerates* all the possible assignments to our variables, and tries each in turn until our expression happens to be true.  Notice that we got a different assignment than the one I gave you above: any satisfying assignment is a valid one as far as we're concerned.

The body of this loop is simple - just evaluate the expression! - but the problem is that we'll have two possible assignments for each variable, so we'll have an exponential number of possibilities to try.  If we want to find satisfying assignments to boolean formulae with hundreds of thousands of variables, this won't work.

Amazingly, though, solving real-world satisfiability problems has had incredible breakthroughs in the last few decades.  My day job involves trying to use systems of logic to reason about the correctness of programs, and SAT solver libraries like Z3 are an important workhorse for the things I do.  If you saw some of my earlier posts about the Dafny programming language, at the bottom of Dafny's prover is in fact a SAT solver!  Other cool new languages like [F*](https://www.fstar-lang.org/) use SAT solving for similar things, too.

OK, so SAT is cool as well as useful, but how do we scale it up to interesting problems?  There are a few different ways to be smarter than the "enumerate all options" loop we just wrote: for example, many SAT problems have many possible satisfying assignments, so stochastic search can work well.  You can then parallelize searching across multiple CPUs or machines if you want.

The other way that's worth talking about is proving by *deduction*.  Deduction can be thought of as simplifying a logical formula by repeatedly transforming it into something equivalent but simpler.  If you know the old "all mascots are cute, and eggbug is a mascot; therefore eggbug is cute" inference, then you have an idea of how deduction works.

A deduction-based algorithm for solving SAT is DP, after *Davis and Putnam*, its designers.  This is the algorithm we'll talk about today.  DP makes a certain assumption about the *structure* of the input formula, namely, that it's laid out in *conjunctive normal form* (CNF).  A formula is in CNF if it can be described as "a conjunction of disjunctive clauses". In other words, if the formula is of the form: `C1 and C2 and C3 and ... Cn`, where each of the `C`s are of the form `b1 or b2 or ... vm`.  Our original formula, `(b1 or b2) and (not b3)`, was in CNF, as it happens.

So, the inner expressions (the "clauses") are boolean variables (either the variables themselves or negated), joined together by `or`s; and, the outer expression is made up of all those clauses, joined together by `and`s.
(If a formula isn't in CNF, there's an algorithm to convert it into that format as a preprocessing step, but I'll ignore that here.)

That's a bit of a mouthful, so let's write some Python classes to represent the structure a CNF formula.  Instead of our boolean values being, well, a boolean, let's create a proper class for a value and a value's negation.

```python
from dataclasses import dataclass
from typing import Union

@dataclass
class Var:
    name: str

@dataclass
class Neg:
    var: Var

Lit = Union[Var, Neg]
```

To keep the syntax minimal, clauses are lists of literals, and formulas will be lists of clauses.

```python
Ors = list[Lit]
Ands = list[Ors]
CNF = Ands

>>> (b1, b2, b3) = (Var("b1"), Var("b2"), Var("b3"))
>>> form: CNF = [[b1, b2], [Neg(b3)]] # The same thing as "(b1 or b2) and (not b3)", just as a list-of-list-of-Lits
```

We could probably make `form` look closer to our original boolean expression with operator overloading, but, eh, effort.  The regular structure of CNF makes this less important.

What's nice about the CNF structure is it gives us a nice way to decompose finding a SAT solution: because each inner expression is a disjunction (i.e. a bunch of values `or`ed together), we only need *one* of the booleans to be true in each one.  And if we can find just that one literal for each of the clauses in our CNF, when we `and` them all together, the expression will evaluate to `true`: a satisfied boolean expression, and we'll have solved SAT for that formula!

OK, so, the DP algorithm: the idea is that we're going to apply three weird tricks over and over to keep crunching the CNF formula down by until either:

1. The CNF formula has no more clauses in it; this case is trivially satisfiable, in the same way that in Python `all([]) == True`.
2. One of the clauses in the CNF formula has had all its literals removed; this case is trivially unsatisfiable, in the same way that in Python `any([]) == False`.

## Weird trick #1: Unit propagation

Suppose we have a clause in our CNF formula that only has one literal in it.  Our running example of this has such a clause: `[Neg(b3)]`.  We call a clause like this a *unit clause*.  Unit clauses are fantastic because they tell us exact how to satisfy them!  In this case, `Neg(b3)` has to be True (since all clauses in a CNF formula need to be ture), so `b3` has to be False.  Contrast this with our brute-force solver from earlier: half of the variable assignments we would have potentially tried would have `b3` set to the wrong value, so those assignments *could never* give us a good result!  One application of the unit propagation rule has cut our computational effort in half.

OK, let's suppose we've found a unit clause.  What else can we do with it?  We can *propagate* that information to other clauses in two ways:  Let's suppose our CNF formula looks like this

```python
>>> # aka: b1 and (b2 or not b3) and (b1 or b3) and (not b1 or b2)
>>> form = [[b1],          # our unit clause: we know b1 must be true
            [b2, Neg(b3)],
            [b1, b3],      # contains our unit literal
            [Neg(b1), b2]] # contains the negation of the literal
```

Let's substitute the information we know to all the other clauses:

```python
>>> form = [[True],
            [b2, Neg(b3)],
            [True, b3],
            [False, b2]]
```

Some of you may have noticed that we have satisfied all the literals in the first clause, so that clause doesn't actually add any new information to the formula and can be removed!  But, we can actually remove *more* than that one.  Remember that we just need one true value in each disjunctive clause.  So, we can remove the third one as well as the first!  Now we have:

```python
>>> form = [[b2, Neg(b3)],
            [False, b2]]
```

We can actually do one more thing, now: In the final clause, the `False` doesn't add anything to the disjunction; `false or b2` is just the same thing as `b2`, after all.  So, we can go through all remaining clauses and filter out any occurrences of `Neg(b1)` (which was how we got the `False` in the first place, remember). After we've completed unit propagation, where all clauses that contain `b1` are removed, and all occurrences of `Neg(b1)` are removed from all remaining clauses, we're left with:

```python
>>> form = [[b2, Neg(b3)],
            [b2]]
```

And the process begins anew.  Hey, after simplification, we've introduced another unit clause, so we could do it once again!

## Weird trick #2: The Pure Literal Rule

In order to understand the pure literal rule, let's look at a CNF formula that is *not* satisfiable:

```python
>>> form = [[b1, Neg(b2)],
            [Neg(b1), b2]]
```

If you squint a bit you can see that we simulaneously require each of the `b1` and `b2` values to be both true and false in different clauses.  The presence of variables and their negations laid out in this way ends up tying us in a knot.

By contrast, if a variable *only* exists as itself or only as its negation, it can't contribute to tightening that knot - in the worst case, it's a redundant variable and just doesn't give us any new information.  So, we can immediately assign True to all pure positive-only literals and False to pure negative-only literals, and then remove them from the formula.  In our example above,

```python
>>> # aka: b1 and (b2 or not b3) and (b1 or b3) and (not b1 or b2)
>>> form = [[b1],          # our unit clause: we know b1 must be true
            [b2, Neg(b3)],
            [b1, b3],      # contains our unit literal
            [Neg(b1), b2]] # contains the negation of the literal
```

since `b2` is a pure positive literal, we could remember that b2 should be true, and then remove all occurrences of that literal.

## Weird trick #3: Resolution

Imagine we've inspected our formula and discovered we can't apply weird tricks #1 or #2: we have no unit clauses, and we have no pure literals.  Take a moment and convince yourself that if the pure literal rule doesn't apply, then all we have are variables that are both negated and non-negated in different clauses.  How can we make progress?  Take a look at the following formula:

```python
>>> # aka (not b1 or b2) and (b1 or b3)
>>> form = [[Neg(b1), b2],
            [b1, b3],
            # ... and some other clauses; let's assume that Neg(b2)
            # and Neg(b3) exist in those, so we can't apply rule 2
           ]
```

*(Edit: as someone rightfully pointed out in the original comments, we could apply the pure literal rule here on `b2` or `b3`, so let's imagine that these two clauses are actually part of a larger formula where perhaps their negation is present, which we're ignoring for the discussion here.)*

Let's use some logical equivalence rules to rearrange this formula using the definition of logical implication:

```
   (not b1 or b2) and (b1 or b3) == (b1 -> b2) and (not b1 -> b3)
```

Informally, this says "if b1 is true, then so too is b2; and, if b1 is false, then b3 is true".  This is nice because we don't necessarily know *whether b1 is true or false*, but, we know that because either b1 is true or false, either b2 or b3 has to be true!  So, we can say that `(not b1 or b2) and (b1 or b3)` is *equivalent* to `b2 or b3` (The technical definition of this equivalence is called equisatisfiability, if you're looking for big words to throw around at dinner parties).

This process, called *resolution*, has essentially banished `b1` from our formula!  This happened because when we expanded the formula out we ended up combining `not b1` with `b1`, so they canceled each other out.  As the time complexity of solving SAT is a function of the number of variables, the fact that we've been able to eliminate one with just a bit of algebra is pretty awesome.  (In more complicated examples, can sometimes increase the number of total clauses, though.)  So, after resolution, we'd end up with:

```python
>>> form = [[b2 b3],
            # ... and some other clauses; let's assume that Neg(b2)
            # and Neg(b3) exist in those, so we can't apply rule 2
           ]
```

## Putting the weird tricks together

If we have an implementation for each of our weird tricks, we can just call each of them in turn until we hit either of our trivial cases!

```python
def dp(form: CNF) -> bool:
    while True:
        if form == []: return True  # Satisfiable!
        if [] in form: return False # Unsatisfiable!
        form = unit_propagate(form)
        form = pure_literal_rule(form)
        form = perform_resolution(form)
```

We know this function has to terminate, because each of our weird tricks will either reduce the number of clauses, or reduce the number of boolean variables.  And that's the DP algorithm!

The DP algorithm isn't a toy solution to SAT: it's the basis for how many industrial solvers actually solve it!  In practice, though, real solvers use a more complicated version of the algorithm called DPLL (the "L"s refer to Logemann and Loveland, who extended the original DP algorithm), but you know the core half of the story now.  Maybe another time I'll talk about the optimiziations DPLL adds.

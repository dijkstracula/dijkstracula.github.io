---
layout: post.njk
title: "Let's Build A Theorem Prover: Satisfiability Modulo Theory: Digital Deduction Saga"
date: 2022-12-19T16:19:44.248Z
tags: [post, sat, smt, logic, verification]
excerpt: "From propositional logic to first-order logic: introducing theories and equality reasoning into SAT solvers"
---

*This post originally appeared on [Cohost](https://web.archive.org/web/20241104063507/https://cohost.org/nathan/post/654021-let-s-build-a-theore).*

---

[Previously](/posts/lets-build-a-theorem-prover/), [previously](/posts/lets-build-a-theorem-prover-2/).

Last time we built a basic conflict-driven clause learning (CDCL) solver that solves the boolean satisfiability problem.  Recall that we started with a sentence in propositional logic containing boolean variables, and the solver told us whether there exists a *satisfying assignment* to those variables such that the whole boolean expression (which we called a *formula*) is true.

## The first order of business...

Propositional logic gave us a mechanism to describe *facts* (our boolean values) which may or may not hold, depending on their relation to other facts.  Usually, though, we're interested in richer questions than what can be encoded in propositional logic.  Just like how we program best at higher levels of abstractions[^1], a richer logic can let us formulate more interesting statements. *First-order logic* is really the workhorse of automated reasoning: it extends propositional logic's notion of *facts*, to those of *objects* (also called *terms*) and *relations* between them.

As my day job is to use systems of logic to reason about computer programs' correctness, most of the examples of first-order logical *propositions* I first think of relate to programs: "If there exists a node in a Paxos cluster that has decided a value, then all nodes in the cluster have decided that same value" and "if `l` is a Python list, `reversed(reversed(l)) == l`" come to mind.  The thing we want is a mechanism to reason about statements like these, just like we used CDCL to reason about propositional formulas!

First-order logic is distinguished from propositional logic in, let's say, three major ways:

- In propositional logic, every variable in a formula was "typed" as a Boolean.  In First-order logic, each term has a *domain*, which is sort of like a type: a term could be an element of a domain like an integer, or a person in a family tree, or a node in a distributed system.
- First-order logic lets us encode *functions*, which consume some number of terms and produce a term. `reversed` would be a function of one argument. *Relations* can be thought of as functions that produce a Boolean - `decided(n, v) == True` could represent the fact that in our Paxos system example, some particular node `n` decided some particular value `v`.
- A term `t` can be *bound* with *quantifiers*, of the form "there exists a `t` such that <some proposition involving `t`>" and "for all `t`, <some proposition involving `t`>".  So, we might say `for all Paxos nodes` `n`, there exists a `v` such that decided(n, v)`.

This sounds quite a bit richer than propositional logic, but there's bad news: while propositional logic has an algorithm to determine satisfiability (in fact, we've seen a few already - brute force enumeration, DP, DPLL, and CDCL!), arbitrary first-order propositions are *undecidable*, meaning there's *provably no algorithm* that's guaranteed to give us back an answer.  So, when we model things in first-order logic, we have to be really careful to use a restriction of the logic that keeps us in decidable algorithm territory.  We'll talk about so-called *decidable fragments* of first-order logic later on, but at a high level, the moment you introduce a quantifier into a proposition, know that you should be treading lightly.

Let's start small, though.  We're going to forget about most of the fancy features of first-order logic like non-Boolean domains and quantifiers, and gradually introduce things into propositional logic.  Where to begin?  How about equality of variables and functions?  How would reasoning about propositions like `x == y`, or `f(a) != f(b) and b == c` work?

## Equality, the accidental way

Today let's talk about equality.  Propositional logic's syntax has `and`, `or`, or `not` as connectives, but nothing about equality (which we could imagine as an `equals(x,y)` relation, or just an operator `==` for simplicity of notation).  We'd certainly need equality for the Python list proposition, for instance.  Knowing what we know about solving boolean satisfiability with CDCL, how could we ever determine a satisfying assignment to the expression `b1 != b2 and b2 == b3`?

Our CDCL implementation doesn't know anything about `==` and `!=`, but we can transform this statement into one with only the connectives of propositional logic.  You could imagine using the property that `x` is equal to `y` if and only if `(x and y)` (when they're both true), or `(not x and not y)` (when they're both false).  (Conversely, `x != y` is true when exactly one of `x` and `y` are true.)  Hey, two possibilities... that looks a lot like a case-split that we saw last time!  Here we have a way of *reducing* equality checks to the propositional logic that we already know how to solve!

As we'll see, this is *not* the best way to solve equalities using SAT, but it sure sounds as if it'll give us the right answer.  OK, let's see what we can do here... If we expand the definition of equality for the two clauses above, we get:

```python
   (b1 != b2)
=> (not ((b1 and b2) or (not b1 and not b2)))        # From expanding the definition of equality
=> (not b1 or not b2) and (not not b1 or not not b2) # By distributing `not` over `and` and `or`
=> (not b1 or not b2) and (b1 or b2)                 # By double-negation
   \________________/     \________/
    Both aren't true  and  Both aren't false
```

and,

```python
   (b2 == b3)
=> (b2 and b3) or ((not b2) and (not b3))            # From expanding the definition of equality
   \_________/    \_____________________/
 Both are true or    Neither is true
```

And so, our final propositional formula is:

```python
   (b1 != b2)                        and (b2 == b3)
=> (not b1 or not b2) and (b1 or b2) and ((b2 and b3) or ((not b2) and (not b3)))
```

If you're reading closely you might notice that our formula is not actually in conjunctive normal form; in order to pass it to our CDCL solver we'd have to transform it to have that particular structure.  It's not hard to do but it's tedious, so rather than using our hand-rolled implementation let's pivot to an industrial strength solver: [Z3](https://github.com/Z3Prover/z3) is one of the most popular ones and it has a nice Python interface.

As it happens, our transformation of the problem into propositional logic has a satisfying assignment:

```python
python3 -q
>>> from z3 import *
>>> b1, b2, b3 = Bool("b1"), Bool("b2"), Bool("b3")
>>> solve(And(Or(Not(b1), Not(b2)), Or(b1, b2), Or(And(b2, b3), And(Not(b2), Not(b3)))))
[b3 = False, b1 = True, b2 = False]
>>>
```

Critically, if we substitute those assignments into our original equality problem then we have `(True != False) and (False == False)` which is correct, so we've successfully *reduced* a boolean *equality* problem to a boolean *satisfiability* problem!

Interestingly, Z3 is smart enough to give us the same answer without us needing to manually transform the equalities into propositional logic:

```python
>>> solve(And(b1 != b2, b2 == b3))
[b3 = False, b1 = True, b2 = False]
>>>
```

So there's clearly an automated way of doing this: but, how?  The way we'll do this is by introducing *theories* into our solver.  The [textbook definition](https://en.wikipedia.org/wiki/Theory_(mathematical_logic)) of a theory is shockingly uninteresting; for our purposes a theory is a formal language with a set of axioms that tell us how to interpret sentences in the language.  As we'd expect `b1 != b2 and b2 == b3` is a perfectly valid sentence in the theory of equality, and we know how to reason about whether this proposition is true because we know something about how equality works.  A SAT solver that knows about theories is called an *SMT solver* - it can solve the Satisfiability problem, Modulo ("having overlaid atop") a Theory, by using propositional logic as a "low-level core".

What's the correct theory of equality that avoids an exponential blowup of case-split clauses, and how do we integrate it into a SAT solver?  We'll reveal that secret...another time...

[^1]: Though I've certainly spent enough of my career writing low-level code to have a healthy appreciation for when the abstraction tax becomes too high!

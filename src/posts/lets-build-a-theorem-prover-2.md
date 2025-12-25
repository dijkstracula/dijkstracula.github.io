---
layout: post.njk
title: "Let's Build a Theorem Prover: SATvatar 2: the way of solver"
date: 2022-12-16T22:02:43.482Z
tags: [post, sat, logic, verification, dpll, cdcl]
excerpt: "From Davis-Putnam to DPLL to CDCL: improving SAT solvers with backtracking and conflict-driven clause learning"
---

*This post originally appeared on [Cohost](https://web.archive.org/web/20241104063350/https://cohost.org/nathan/post/559376-let-s-build-a-theore).*

---

Last time we talked about the Davis-Putnam algorithm for solving the Boolean satisfiablity problem (SAT).  I think it would be fun to talk about how SAT can be used to reason about more interesting things than Boolean expressions, like linear arithmetic or array/pointer accesses.  But before that, it probably makes sense to finish the actual SAT algorithm discussion first.  (I also just wrote my ~very last final exam ever~, so I only have a pint-sized effortpost in me this afternoon.)

## Resolution ain't all it's cracked up to be

Remember that the DP algorithm had three tactics to crunch down the input formula: unit propagation, the pure literal rule, and when neither of those could be applied, resolution to "banish" a variable from the formula.

Remember how resolution worked: If I have a formula with two clauses like `(a or b) and (not a or c)`, I can "smash these clauses together" to yield `(b or c)`.  In this simple example, we are left with one fewer clause *and* one fewer variable: awesome, our formula is becoming smaller in two ways!

Here's an implementation of the resolution rule in Python:

```python
def resolve(p: Var, form: CNF) -> CNF:
    # 1. Find all the clauses that contain p, and the ones with p's negation.
    poses = filter(lambda c: p in c, form)
    negs = filter(lambda c: negate(p) in c, form)

    ret = [] # 2. For each clause with p and each with (not p)...
    for (pos, neg) in itertools.product(poses, negs):
        pos = filter(lambda p2: p != p2, pos)
        neg = filter(lambda p2: negate(p) != p2, neg)
        #... smash 'em together!
        new_clause = list(set(pos).union(set(neg)))
        ret.append(new_clause)
    return ret
```

I alluded to this in the earlier post, but while resolution always eliminates a variable, it doesn't always leave us with fewer clauses.  In fact, the `itertools.product` expression might give you a hint that in general, one might expect something like an `O(n^2)` blowup in the number of clauses, *each time we perform resolution*.  Not great, Bob!

## When there's only two candidates, there's only two choices!

The DPLL (the LL is for Logemann and Loveland, two more researchers) algorithm improves on this by replacing resolution with *backtracking search* - if we don't know whether `p` should be `True` or `False`, make a guess and see if that leads to a solution.  If not, backtrack to an earlier state and make the other guess!  This procedure's called a *case split on `p`*.

This might be a bit surprising given that this isn't fundamentally different from our strawman "try all examples" solver in the last post.  But, hopefully the majority of their assignments will follow from unit proagation and the pure literal rule, so we don't have to case-split on too many variables.

Here's what our first cut of what extending our DP implementation into DPLL might look like, with case splitting in place of resolution:

```python
def constraint_prop(form: CNF) -> CNF:
    """Perform unit propagation until we reach a fixed point"""
    while True:
        form2 = unit_propagate(form)
        if form == form2:
            return form
        form = form2

def dpll(form: CNF) -> bool:
    """Returns whether `form` has a satisfying assignment."""
    form = constraint_prop(form)

    # Do we have a solution yet?
    if form == []: return True  # Satisfiable!
    if [] in form: return False # Unsatisfiable!

    # If not, case split!
    p = choose_a_variable(form)
    return dp(form + [p]) or dp(form + [negate(p)])
```

(How `p` is chosen is up to us: a good heuristic might be "choose the unassigned variable that occurs in the largest number of clauses", but I'm sure real-world solvers have way fancier ones.)

This implementation of DPLL is nice and readable, and it'll return the right thing.  However, there's room for improvement.  Notice that in this recursive implementation, if we find a contradiction and return `False`, we backtrack exactly one level (that is, we return to the previous stack frame) and then try an alternative.  However: when we were forced to backtrack, we could have learned something about the state of the partial solution that led to that contradiction, but when we return to the caller we "forget" that observation.  Also, this means that we perhaps should have backtracked more than just one level if we made a wrong guess a long time ago.

So, we'll improve this by implementing *non-chronological backtracking search* (sometimes called "backjumping") in our implementation.  This is awkward to do with a recursive implementation unless we have a tidy way of unwinding the stack - we could possibly do this with exceptions (or better, continuations!), or if you're smarter than me you could use something bananas like the [search monad](https://hackage.haskell.org/package/logict), or, uh, `longjmp`???  But I think the tidier way is to modify our code to use loops.

Instead of producing new formulas in each recursive call, we'll accumulate the variable assignments we either deduce or guess in a list, and pop elements off it when we hit a contradiction and need to backtrack.  This means that we never modify our formula, which is nice!  But, the downside is that now `constraint_prop` and `choose_a_variable` both need to consume and return our list of choices.  As a result, our iterative `dpll` is going to look a lot less denotative than the recursive one.  But *adjusts my functional programmer enjoyer hat* that's the price we pay for state mutation!!!

## From DPLL to another four-letter acronym

OK, here's a rough sketch of how we might transform the recursive search procedure into an iterative one.

```python
def dpll_iter(form: CNF) -> bool:
    """An initial attempt at an iterative DPLL implementation."""
    choices: list[Lit] = [] # This serves the same purpose as our call stack did.
    while True:
        choices = constraint_prop(form, choices) # unit-propagate and add those to our choices list

        if is_unsat(form, choices):         # Contradiction!  We have to backtrack.
            match backtrack(choices):
                case [Var(v), *rest]:       # Try the other branch
                    choices = [Neg(Var(v)), *rest]
                case [Neg(Var(v)), *rest]:  # neither `p` nor `not p` worked here; "pop the stack"
                    choices = rest
                case []:                    # Inherent contradiction!
                    return False
        else:
            match choose_an_unassigned_var(form, choices):
                case None:
                    return True             # Every variable was assigned: Formula is satisfiable!
                case p:
                    choices.insert(0, p)    # Take a guess and push it onto the stack
```

Notice here that instead of making `form` an increasingly-smaller formula, we'll leave it unchanged.  Our `constraint_prop` and `choose_an_unassigned_var` helper functions now take in our choices list to make sure we don't attempt to propagate or guess the same variable twice.

Also, notice that we have implicitly come up with something really nice: by the time we return `True`, the `choices` list contains assignments for every variable, so not only do we know whether the formula is satisfiable, but we know how to make it satisfiable!

## Weird Trick 1: We know where we're going but we don't know where we've been

Let's first implement non-chronological backtracking by observing that there are two ways that our `choices` list can be modified.  Unit propagation can *derive* a value for a variable by constraint propagation, or, we can *guess* a value when we case-split.  In the above implementation, we don't distinguish between the two.  This wastes effort: imagine we began searching for a solution with a guess, and then constraint propagation was able to infer a whole bunch of other values.  That's great, except in the case where that initial guess was wrong!  The versions above would end up exploring different variations on the derived values, since we'd only ever explore the more-recent derived values first, but the root cause of the contradiction stemmed way back with our guess.  The thing we'd rather do is backtrack to the most recent guess, even if a bunch of constraint propagation happened since that guess.  After all, those derived values depended on some guessed value!

Non-chronological backtracking can solve this for us, so long as we can remember whether a variable was guessed or derived.  So, our choices list will now be a tuple containing an enum and the variable itself.

```python
Choice = Literal["DERIVED", "GUESSED"]

def backtrack(choices: list[(Choice, Lit)]) -> list[(Choice, Lit)]:
    " Unwind the stack, removing all derived assignments. "
    while True:
        match choices:
            case [("DERIVED", _), *rest]:
                choices = rest
            case _:
                return choices

def dpll_iter(form: CNF) -> bool:
    """Returns whether `form` has a satisfying assignment."""
    choices: list[(Choice, Lit)] = []
    while True:
        choices_with_constraint_prop = constraint_prop_iter(form, choices)

        if is_unsat(form, choices_with_constraint_prop): # Contradiction!
            match backtrack(choices):
                # We guessed a value, but now we know it has to be its negation!
                case [("GUESSED", v), *rest]:
                    choices = [("DERIVED", negate(v)), *rest]
                # Inherent contradiction!
                case []: return False
        else:
            match choose_an_unassigned_var(form, choices):
                case None:
                    return True # Every variable was assigned: Formula is satisfiable!
                case p:
                    choices = choices_with_constraint_prop
                    choices.insert(0, ("GUESSED", p))
```

This is a bit more complicated, but now we aren't going to repeatedly explore variable derivations that stemmed from a bad guess.  Our new `backtrack()` helper function unwinds our variable assignments until it finds a guess, and notice that we're able to say something about that guess: if we guessed `p`, and we guessed wrong, then we've actually *derived `not p`*!

## Weird Trick 2: Maybe one day I'll learn from my mistakes

There's one more thing we can do to wrap up a canonical DPLL implementation.  When we reach a contradiction, what can we say about all the choices that we made that led up to that point?  For example, if went back and looked in `choices`, and saw that we believed `p1 == False` and `p2 == False`, what does it mean given that we hit a contradiction?  Well, we have learned that `((not p1) and (not p2)) == false`, and so `(p1 or p2) == true`!  In other words, at least one of our choices needs to be inverted in order to avoid the contradiction.  That seems like a fact worth remembering.

And as it happens, "p1 or p2" is a disjunction, so we can *append that clause to our formula* and remember that fact while continuing the search down other avenues!  You could imagine a potentially smarter algorithm that learns more specific things about the formula -- indeed, real solvers find what's called the *unique implication point* to separate out the choices that actually led to the contradiction versus the ones that are unrelated -- but let's keep the discussion simple here.

This is an interesting change from the DP algorithm, which, if you remember, kept *removing* parts of the formula until we reach a trivial case.  Here the formula is *increasing* in size, like with resolution!  This is okay because we're only ever increasing the number of clauses by a constant factor, and, informally, we're not changing anything about the formula itself, just constraining the valid search space for the algorithm to search through. So, we'll never re-generate a `choices` list containing the same contradictory guesses a second time, ensuring we're only searching through new parts of the search space.  (A formal proof is in Kroening and Strichman's *Decision Procedures* if you're really curious.  If you end up understanding it better than me, maybe you can explain it to me!).

What we've seen here is a really simple example of *conflict-driven learning* - we *analyse* why we hit a contradiction, insert a new clause that encodes what we've learned, and then non-chronologically backtrack to before we went down "the bad path".  For this reason, this DPLL-with-extra-tricks is known as "conflict-driven clause learning", or CDCL for short.

At this point we have all the parts we need for an honest-to-goodness modern SAT solver.  Top-of-the-line solvers differentiate themselves mostly by their choice of heuristics (such as what variables to deal with first) or engineering concerns like optimizing redundant clauses for better memory use or more clever data structures than our "list of list of variables" ones here.  But, this is the core of it!

Of course, we're not usually interested in boolean satisfiability - particularly if you're like me and want to use logic to reason about computer programs, our satisfiability problems might be richer than just "expressions of booleans".  We might want to reason about equality (such as `b1 == b2 and b2 != b3`) or operate over richer datatypes like arithmetic, arrays, functions, or pointers (such as `*p < a[4] + 42`).  This is where *satisfiability theories* come into play - more complicated domains are mapped into a SAT problem, which the solver then chugs through.  Maybe next time we'll talk about how to come up with a simple theory or two.

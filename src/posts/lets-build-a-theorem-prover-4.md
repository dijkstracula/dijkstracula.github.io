---
layout: post.njk
title: "Let's Build a Theorem Prover: SMT 2: Not(Eq(urne))"
date: 2023-01-05T20:10:48.970Z
tags: [post, smt, sat, logic, verification, equality, lazy-solving]
excerpt: "Lazy SMT solving: building an SMT solver with iterative refinement and blocking lemmas"
---

*This post originally appeared on [Cohost](https://web.archive.org/web/20241104063507/https://cohost.org/nathan/post/789960-let-s-build-a-theore).*

---

So [last time](/posts/lets-build-a-theorem-prover-3/) we introduced the notion of *satisfiability theories* that extend propositional logic to solve the satisfiability problem for more interesting logical sentences than those made up of booleans and logical connectives.  We saw how formulas involving equality could be *encoded* by splitting on the two cases that make boolean equality true - both are true or both are false - yielding a new formula that is then passed to our CDCL solver.  However, in what seems like a classic problem for this series of posts, we paid for our particular encoding in a major way: exponential blowup, since `n` case splits will leave us with `2^n` clauses.  Also, this implementation was easy to come up with because there was a direct way to express equality of booleans in propositional logic - for more interesting theories this won't necessarily be true, though.

Determining satisfiability for a theory with the help of a SAT solver gives us an *satisfiability modulo theory* (SMT) solver, and we saw how Z3 (a real-world solver, versus the one we've been writing in Python in these posts) could either solve our example equality problem automatically for us.

In this post we'll go back to our Python implementation, since building our own versions of things is always more fun, and see how we can implement the theory of equality and extend our SAT solver into a more proper SMT solver!  Let's begin by creating a new datatype to model our theory with - in particular, we're going to add a new piece of syntax to our propositional CNF language to encode equality.  So, our data and type definitions now look like this:

```python
@dataclass(frozen=True)
class Var:
    name: str
    def __repr__(self): return self.name

@dataclass(frozen=True)
class Not:
    var: Var
    def __repr__(self): return f"!{self.var}"

PropLit = Var | Neg # The theory of propositional logic

@dataclass(frozen=True)
class Eq:
    " NEW: represents the fact that two propositional variables are true "
    lhs: PropLit
    rhs: PropLit
    def __repr__(self): return f"{self.lhs} == {self.rhs}"

EqLit = PropLit | Eq # The theory of equality and prop. logic
```

We could mechanise our case-splitting functionality by writing a function that consumes a CNF of EqLits and produces one of PropLits, transforming every `Eq(lhs, rhs)` literal into its split form in propositional logic, so really we haven't introduced anything new here.

OK, to review, let's look at how we solved an equality problem the hard way last time:

1. We began with a proposition with equalities, which is not expressible in propositional logic, and devised a way to *encode* those equalities as an equivalent SAT problem.  (This encoding was our case-split on "both are true" and "both are false".)
2. We passed the encoded problem to the CDCL solver, which gave us an answer in propositional logic.
3. Our original equality problem problem was satisfiable if and only if the our encoded SAT problem was, so we're done!

Our encoding was pretty nice because it was able to precisely encode the meaning of equality in propositional logic.  "Two booleans are equal if they are both true or if they are both false" is a straightforward definition into propositional logic; this means that we can find an exact satisfying assignment to the encoded form of the problem just with a single call into our SAT solver after we've done this translation.  In other words, the hard part was all in step `1`, and in step `3` there wasn't really anything to do at all.

This is called an *eager* SMT approach because everything happens the one time you call into the SAT solver with your encoded formula.  You can think of this as almost like a single-pass compiler that translates your high-level SMT "program" into a low-level SAT "machine code", and then solving the formula just means "executing the machine code".

By contrast, a *lazy* solver approach will *incrementally* build up the propositional formula through multiple iterations of passing the formula to the SAT solver, just like how our SAT solver had multiple rounds of constraint propagation that resulted in clause learning.  The hope here is that we can come up with an initially-imprecise encoding (in other words, reducing the amount of work we do in step `1`), at the expense of needing to iterate a bunch of times to get to a satisfying assignment.

## A lazy approach to equality

OK, here's a lazy approach to the equality theory:  Let's try and find a solution to the following sentence:

```python
not b1 and (b1 == b2) and (b2 == b3) and (b1 != b3)
```

Before continuing, take a moment and see if you can see whether this sentence is satisfiable.

As before, we'll begin with step 1: we'll take our sentence and encode it into propositional logic.  However, we'll do something different than before: this time, we'll *introduce new variables* in our encoding!  In particular, we'll have a variable for every distinct function call in our sentence.  So, we'll invent variables for each of the equalities `Eq(b1,b2)`, `Eq(b1,b3)`, and `Not(Eq(b1,b3))`.  The sentence with each of the new Boolean variables substituted in place is called the *propositional skeleton*.

```python
def eqlit_to_proplit(l: EqLit) -> PropLit:
    """ Transforms an equality literal into its propositional logic encoding:
    namely, a new boolean variable representing the true value of the equality."""
    match l:
        case Eq(lhs, rhs): return Var(str(l))
        case Not(v):       return Not(eqlit_to_skel(v))
        case Var(_):       return l

def eqcnf_to_skel(cnf: list[list[EqLit]]) -> list[list[PropLit]]:
    """ Encodes a CNF sentence in the theory of arrays into a CNF sentence
    in plain-old propositional logic."""
    return [[eqlit_to_proplit(e) for e in clause] for clause in cnf]
```

Our encoding actually has four boolean variables, three of which were constructed when we encoded each of the three equalities, and the fourth is a boolean value from the original formula:

```python
>>> b1, b2, b3 = Var("b1"), Var("b2"), Var("b3")                 # Our propositional variables...
>>> form = [[b1], [Eq(b1, b2)], [Eq(b2, b3)], [Not(Eq(b1, b3))]] # Our equality sentence...
>>> skel = eqcnf_to_skel(form)                                   #...encoded as propositional logic
>>> print("\t", skel)
         [[!b1], [(b1 == b2)], [(b2 == b3)], [(b1 != b3)]]
>>> #       \/    \________/     \________/    \________/
>>> #       b1    a new Var      a new Var     a new Var
```

The skeleton has had all notions of equality abstracted behind the boolean variables, so we could read it as `"!b1 and x and y and z"` if we'd named the variables differently, but it's probably good to give these new variables names that describe what equalities they're encoding.

What does our SAT solver think about our encoded formula?

```python
>>> print(dpll_iter(skel))
True
```

So the SAT solver has found a satisfying assignment; but, we would probably like to know precisely what the assignment is!  In other words, instead of returning a boolean, `dpll_iter` should return a `model`, a map from a propositional variable to a boolean value.  This is a really small change, since we keep track of that sort of mapping in our `choices` accumulator variable.  Let's refactor the code to return a model dictionary rather than a boolean:

```python
# NEW: a Model associates a propositional variable with a boolean value.
Model = Mapping[Var, bool]

def choices_to_model(choices: list[(Choice, PropLit)]) -> Model:
    " NEW: Converts our internal choices list to a Model dictionary. "
    ret = {}
    for (c, v) in choices:
        match v:
            case Var(s): ret[v] = True
            case Not(v): ret[v] = False
    return ret

def dpll_iter(form: list[list[PropLit]]) -> Optional[Model]:
    """Returns whether `form` has a satisfying assignment."""
    choices: list[(Choice, PropLit)] = []
    while True:
        is_unsat, choices2 = constraint_prop_iter(form, choices)
        if is_unsat:
                # NEW: An unsatisfiable formula has no model to return
                case []: return None
        else:
            match choose_an_unassigned_var(form, choices2):
                case None:
                    # NEW: Every variable was assigned: return what those assignments are!
                    return choices_to_model(choices2)
                # ...
```

Okiedoke, let's see what the assignments actually were:

```python
>>> print(dpll_iter(skel))
{(b1 == b3): False, (b2 == b3): True, (b1 == b2): True, b1: False}
```

Here, our SAT solver has found a satisfying assignment for our four variables! `b1` and `b1 == b3` are False, while `b1 == b2` and `b2 == b3` are True.  That's great, but this hasn't given us assignments for `b2` or `b3`, the original problem's other variables: it only says, "if `!b1`, `b1 == b2`, `b2 == b3`, and `b1 != b3`, then our sentence is satisfiable".

In other words, this statement *implies* the satisfiability of the whole sentence.  But, *is the antecedent to the implication even true*?  Can we have boolean assignments such that the implication holds?

If you stared at this formula for a bit earlier, you'll have likely concluded that there's no way to do it!  Take any two of the three equalities and you'll find the third remaining one will contradict it.  However, because the solver only "sees" the `!b1 and x and y and z` statement, we say that the sentence is satisfiable, but it's not T-satisfiable ("T" referring to the fact that our original problem was in some first-order "T"heory).  Sounds like we have some sort of contradiction on our hands.

Remember what we said earlier: if we have a statement that is false, then the negation of that statement has to be true:

```python
   not ((b1 != b3)  and   (b2 == b3)   and  (b1 == b2)   and  (!b1)) # The negation of our assignments from the SAT solver...
->       b1 == b3  or      b2 != b3  or      b1 != b2  or       b1 # ...This has to be true!
```

Now we can add that clause to our propositional formula, constraining the search space with what we learned the first time, and try the solver once more:

```python
>>> #                               b1==b3 or       b2!=b3 or        b1!=b2 or b1
>>> lemma: list[list[EqLit]] = [[Eq(b1, b3), Not(Eq(b2, b3)), Not(Eq(b1, b2)), b1]]
>>> skel.extend(eqcnf_to_skel(lemma))
>>> print(skel)
[[!b1], [(b1 == b2)], [(b2 == b3)], [!(b1 == b3)], [(b1 == b3), !(b2 == b3), !(b1 == b2), b1]]
>>> print(dpll_iter(skel))
None
```

This time we get a different answer: there's no satisfying assignment, which is the correct answer to our original problem.  There was no way to figure this contradiction out from the propositional skeleton in one attempt; the SMT solver had to:

1. translate from the SMT sentence into SAT with its *encoding* procedure:
2. check whether the encoding is satisfiable.  If it's not satisfiable, the original SMT sentence certainly isn't.  (In this way we say that the encoding is *sound*.)
3. If it *is* satisfiable, map its satisfying assignments *back into the original theory* and see whether they make sense.  If they do, we've found a solution, and the original sentence is T-satisfiable!  But if not, take the contradicting model as a *blocking lemma* and add it to the SAT formula, *propagating the theory* and returning to step 1.

Maybe you can see here where the "modulo" comes into play with the term "satisfiability modulo theory": 24 is not equal to 27, but in the theory of modular arithmetic, 24 *is* equal to 27, modulo 3.  I go back and forth on whether or not this is clever or an abuse of notation, but the intuition kind of holds at least.

I haven't given you the full story of equality, though: we should talk about exactly how we can mechanise mapping our SAT solution *back into SMT*, doing a sort of *decoding* into the original theory.  From there we'll talk about extending CDCL for solving arbitrary theories - I'll introduce the theory of `Equality and Uninterpreted Functions`, which is a suprisingly powerful way to reason about Prolog ass-looking logical sentences and uses the same mechanism we've been building up here this whole time... if that's isn't nerd bait then I don't know what is!

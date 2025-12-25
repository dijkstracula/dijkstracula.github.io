---
layout: post.njk
title: "Let's Build a Theorem Prover: Lazy and Basic? SAME"
date: 2023-01-17T20:04:09.810Z
tags: [post, smt, sat, logic, verification, equality, union-find]
excerpt: "Implementing the lazy CDCL(T) algorithm with Union-Find for equality reasoning"
---

*This post originally appeared on [Cohost](https://web.archive.org/web/20241104063507/https://cohost.org/nathan/post/861374-let-s-build-a-theore).*

---

Last time we built up a mechanism to determine whether boolean sentences with equalities are satisifiable, without needing to "translate down" equalities into propositional logic.  We saw that SMT solvers make use of two "translators": one that *encodes* the theory down into propositional logic, and a theory-specific checker that deduces blocking lemmas for the SAT solver to learn from, just like how CDCL learned when it stumbles into contradictions.  Generally speaking, this might look like this:

```
 /--------------------------\
 |  theory-specific solver  |
 \--------------------------/
  T-sentence             ^
   |                     |
   |        deduce blocking lemma (TODO: how???)
   |                     ^
   |                     |
   v                     |
 encoded SAT form        |
   |                     |
   v          Encoded vars' assignments
 /--------------------------\
 | propositional SAT solver |
 \--------------------------/
```

We've seen the downwards-facing arrow implemented in Python - that was our `eqcnf_to_skel()` function.  We don't have a way to formulate generating the blocking clause, though - last time we just "stared at it" until we knew the answer.  Let's tackle a function that creates that blocking clause first.

## and I say: try 'em all!!!

OK, how should we begin?  Well, remember that after the first round of solving, CDCL gave us as a model:

```python
>>> b1, b2, b3 = Var("b1"), Var("b2"), Var("b3")                   # Our propositional variables...
>>> form = [[b1], [Eq(b1, b2)], [Eq(b2, b3)], [Not(Eq(b1, b3))]]   # Our equality sentence (in CNF)...
>>> model: Mapping[PropLit, bool] = dpll_iter(eqcnf_to_skel(form)) # What does the model say?
>>> model
{(b1 == b3): False, (b2 == b3): True, (b1 == b2): True, b1: False}
```

What can we do with this information?  Here's a terrible idea: we can convert the model into a Python expression, and then evaluate that expression on all possible boolean assignments to `b1`, `b2`, and `b3`:

```python
>>> expr = " and ".join([f"({k} == {v})" for (k, v) in model.items()])
>>> expr
((b1 == b3) == False) and ((b2 == b3) == True) and ((b1 == b2) == True) and (b1 == False)
```

```python
>>> for b1, b2, b3 in itertools.product([True, False], repeat=3):
...     if eval(expr):
...        print(f"Satisfying assignments: b1={b1}, b2={b2}, b3={b3}")
...        break
... else:
...     print(f"No satisfying assignment!!!")
No satisfying assignment!!!
```

Of course, it makes no sense to do it this way: if we were okay with brute-forcing all possibilities then we could have avoided learning about better ways to solve SAT in the first place!

Instead, we're going to make use of facts about equalities that are universally true: such facts are called the theory's *axioms*, and the set of axioms are specific to a particular theory.

What axioms about equality are there?  Well, we know that equality is *reflexive* and *symmetric* - `x == x`, and if `x == y` then `y == x`, so axioms for equality would be `Eq(x,x)` and `Eq(x,y) ==> Eq(y,x)`.  We also know that equality is *transitive*, if we know both `Eq(x,y)` and `Eq(y,z)`, we can infer the fact that `Eq(x,z)`.  The technical term for this is an *equivalence relation* - and we can take advantage of equivalence relations to come up with a better way to solve this.

## In the beginning there was the graph

Something that might be non-obvious is that we are free to model our equivalence relations in a totally different way than variables in CNF if we want.  One such way that I can think of is an undirected graph structure.  In this graph, vertices are our Boolean variables, and for every equality literal we have an edge between the relevant variables.

```
Equality graph: b1 == b2 && b2 == b3 (three vertices; two edges)

      [b3]-
           \
            \
[b1]-------[b2]
```

The intuition is to think about *graph reachability*: by traversing the equality graph from some starting vertex `x`, what vertices (i.e. boolean variables) can I eventually get to, and how does that relate to equality?

- `Eq(x,x)` is represented by the fact that I don't need to traverse the graph at all if I'm starting at `x` and want to reach `x`: I'm already there!
- `Eq(x,y) ==> Eq(y,x)` is represented by the fact that if I can follow edges from `x` to `y`, I can take the same edges from `y` to get back to `x`, just in the reverse direction.
- `Eq(x,y) and Eq(y,z) ==> Eq(x,z)` is represented by the fact that if I can get from `x` to `y` and from `y` to `z`, I know how to get from `x` to `z`: I start at `x`, go to `y`, and then continue along to `z`!

Oh, but we have two kinds of equalities: `==` and `!=`!  So, we'll actually need a second graph to encode the *inequalities* in the formula too.  Here, edges indicate that the two vertices need to have different values:

```
Inequality graph: b1 != b3 (three vertices; one edge)

     -[b3]
    /
   /
[b1]       [b2]
```

OK, but how can we see from these graphs that this sentence isn't T-satisfiable in the theory of equality?

A *connected component* is a part of a graph where all vertices in the component are reachable by all other vertices in the component by following zero or more edges.  There's only one connected component in the equality graph: `{b1, b2, b3}`, so in terms of the theory of equality this means that `b1 == b2 == b3` -- they need to all have the same value.  By contrast, the inequality graph has two connected components: `{b1, b3}` and `{b2}` - starting in the former component, there's no path that will take you to the latter, and starting from the latter you can't go anywhere.  In terms of the theory of equality, this means that `b1` and `b3` each need to have different values.

Here's the trick: the fact that we have an edge `(b1, b3)` in the inequality graph, and a connected component in the equality graph that contains both `b1` and `b3`, is how we can formalize a contradiction.  The inequality edge says "b1 and b3 have to be different", but the connected components derived from the equality graph mean that b1 and b3 have to be equal.  Boom!

## There's power in a union-find

So we could go and code up a graph datatype, compute the connected components for the equality graph, and test each edge in the inequality graph to see if either endpoint shares a connected compoent.  However, the thing we're really after is modeling a set of disjoint sets, and the [Union-Find](https://en.wikipedia.org/wiki/Disjoint-set_data_structure) data structure is an ideal way of doing this.  (I've never actually needed one outside a Google coding interview, so it's a good excuse to acutally use it for something!)

A Union-Find contains a series of values partitioned into one or more *equivalence classes* - informally, this is like if you had a set of disjoint sets, where you promise that a value is present in only one of the inner sets.  Since a node in the equality graph can only exist in one connected component, this is exactly the property we're looking for!

As the name suggests, you can do two important things with a Union-Find.  First, you can *find* which equivalence class a value belongs to; if two values `v1` and `v2` are in the same equivalence class, then `v1 == v2` and hence `find(v1) == find(v2)`.  Second, you can take the *union* of two equivalence classes, merging them together.  After unioning, `find` will return the same thing for every value in either class.

```python
T = TypeVar("T")

@dataclass
class UFNode(Generic[T]):
    """ A node encapsulates a value in some equivalence class; the whole class
    is represented as a tree of these nodes.  Two nodes are in the same class
    class if you can follow their `parent` pointers up to the same root.
    root - the root is called the 'canonical node' for the equivalence class. """
    val: T
    parent: Optional["UFNode[T]"] = None

class UnionFind(Generic[T]):
    """ A Union-Find contains a collection of equivalence classes (that is,
    a bunch of UFNode trees)."""
    forest: Mapping[T, UFNode[T]]

    def __init__(self, *args: T):
        " Start with each element in their own singleton equivalence class. "
        self.forest = { t: UFNode(t) for t in args }

    def find(self, t: T) -> UFNode[T]:
        " Returns the canonical (root) node for `t`'s equivalence class. "
        n = self.forest[t]
        while n.parent is not None:
            n = n.parent
        return n

    def union(self, t1: T, t2: T):
        " Merges the equivalence classes containing `t1` and `t2`. "
        c1, c2 = self.find(t1), self.find(t2)
        if c1 != c2:
            c1.parent = c2
```

With this disjoint-set data structure, our work is surprisingly simple: we'll extract all the edges in the equality graph (essentially grabbing both sides of variables that resemble `"(lhs == rhs)"` and for which the model says their values are True), and unioning them together into the same equivalence class.  Then, all we need to do is get the edges of the inequality graph (as before, all the edges that resemble `"(lhs == rhs)"` but for which the model says their values are False) - if they reside in the same equivalence class, then according to the equality graph they're equal, contradicting the inequality graph.

```python
def model_assn_to_lit(var: Var, assn: bool) -> PropLit:
    " Converts a model assignment back into a literal. "
    if assn:
        return var
    else:
        return Neg(var)

def eq_blocking_lemma(m: Model) -> Optional[list[PropLit]]:
    """ If the given model is not T-satisfiable, construct a blocking
    lemma out of the contradiction by negating the model. """
    uf = UnionFind(*eq_var_names(m))

    for v1,v2 in equality_edges(m):
        uf.union(v1, v2)
    for v1,v2 in inequality_edges(m):
        cc1, cc2 = uf.find(v1), uf.find(v2)
        if cc1 == cc2:
            print(f"*** Not T-satisfiable: {v1} != {v2}, but {v1} == {cc1.val} && {v2} == {cc2.val}")
            return [negate(model_assn_to_lit(var, assn)) for var, assn in m.items()]
```

When we run this code on our running example, we see the thing we expect in our debug output: `b1 != b3` contradicts the fact that `b1 == b3` (equivalently: b1 is in b3's equivalence class because b1 == b2 and b2 == b3).  We've successfully mechanised the process of determining whether the result from the SAT solver was a blocking clause or not!

```python
>>> print(model)
{(b1 == b3): False, (b2 == b3): True, (b1 == b2): True, b1: False}

>>> print(eq_blocking_lemma(model))
*** Not T-satisfiable: b1 != b3, but b1 == b3 && b3 == b3
[[(b1 == b3)], [!(b2 == b3)], [!(b1 == b2)], [b1]]
```

And, what's more, the returned CNF formula matches the one we constructed by hand in the previous post:

```python
>>> print(skel)
[[!b1], [(b1 == b2)], [(b2 == b3)], [!(b1 == b3)]]

>>> skel.append(eq_blocking_lemma(model))
>>> print(skel)
[[!b1], [(b1 == b2)], [(b2 == b3)], [!(b1 == b3)], [(b1 == b3), !(b2 == b3), !(b1 == b2), b1]]

>>> print(dpll_iter(skel))
None
```

## Putting it all together: CDCL(T)

Even though it might not feel like it, we've finally hit a pretty awesome milestone.  We've now mechanised enough of the theory of equality and propositional logic to construct a solver that combines both of them together!

Going on what we just wrote, let's combine our lazy equality solver with our CDCL solver, to iteratively strengthen a propositional skeleton according to the blocking lemmas that our theory solver deduces.

```python
def lazy_basic_solver(form: list[list[EqLit]]) -> bool:
    """ Solves a propositional sentence in the theory of equality. """
    skel = eqcnf_to_skel(form)
    while True:
        print(f"** lazy_basic: {skel}")
        # 1. Attempt to solve the propositional skeleton.  If it is
        # unsatisfiable, the formula is certainly not T-satisfiable.
        model = dpll_iter(skel)
        if model == None:
            return False

        # 2. Try to deduce a blocking lemma from the model.  If there is
        # none to be found, the model is T-satisfiable, so we are done!
        # Otherwise, add the lemma to our skeleton and try again.
        lemma = eq_blocking_lemma(model)
        if lemma == None:
            return True
        skel.append(lemma)
```

```python
>>> b1, b2, b3 = Var("b1"), Var("b2"), Var("b3")
>>> form = [[Neg(b1)], [Eq(b1, b2)], [Eq(b2, b3)], [Neg(Eq(b1, b3))]]

>>> print(lazy_basic_solver(form))
** lazy_basic: [[!b1], [(b1 == b2)], [(b2 == b3)], [!(b1 == b3)]]
*** Not T-satisfiable: b1 != b3, but b1 == b3 && b3 == b3
** lazy_basic: [[!b1], [(b1 == b2)], [(b2 == b3)], [!(b1 == b3)], [(b1 == b3), !(b2 == b3), !(b1 == b2), b1]]
False
```

We can see that this does the right thing (and we could remove one of the contradictory clauses and see that the solver now tells us that it *is* satisfiable, as we'd expect), which is fantastic!  Any time we need to solve a sentence in the theory of equality, this function will do.  What's more, our university software engineering teachers would be pleased with how we've decoupled the SAT solver from the theory solver: if I'd bothered to pay attention in that class I might expect that they'd state that our implementation has *high cohesion and low coupling* (or is it the other way around?  I donno, I was going through my sanctimonious Scheme programmer phase that semester, and my bozo bit flips the moment a well-meaning manager starts commenting on design patterns in my PRs).  Nonetheless, following this logic, we often say that CDCL is now *parameterised* on the theory; when we introduce a second theory we'll have to distinguish between which particular `cnf_to_skel()` and `blocking_lemma()` functions we'll want to call.

As the name suggests, `lazy_basic_solver` can be improved at the expense of a bit more complexity, but we'll leave that for another time.  Next time, we'll introduce modeling functions, at which point we'll have enough core functionality to really start writing interesting things.

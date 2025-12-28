---
layout: post.njk
title: "Proving the Coding Interview II"
date: 2022-04-28T09:19:51-05:00
tags: [post, dafny, verification, provingthecodinginterview]
excerpt: "Integer.toString() 2 furious"
---

This is the second of a three part series:
[Part 1](/posts/proving-the-coding-interview/) |
Part 2 |
[Part 3](/posts/proving-the-coding-interview-3/)

Welcome back to Proving the Coding Interview!  In the [previous
article](/posts/proving-the-coding-interview/) we started to verify
and implement an implementation of Fizzbuzz in the Dafny programming
language.  But we left off one important piece: Dafny doesn't yet have built-in
functionality to convert a number value to a string, which we need to complete
`Fizzbuzz()`'s behaviour.  We'll attempt to write such a conversion today and
[fix up some implementation
details](/posts/proving-the-coding-interview-3/) in the next and
final post.

As it happens, I've _also_ been asked to do this in a programming interview, so
we're getting two practice problems for the price of one here!

We'll also take this opportunity to dig a bit deeper into the _philosophy_ of
formal verification.  Does formal verification supersede traditional testing
methodologies?  Does "verified" actually mean anything, anyway?  Should we
"verify" anything and everything we write?  Stay tuned...

## Our Problem statement:

As before, let's begin by writing out the concrete problem that we are going to
solve:

```
To convert a number `n` into a string:

1) If `n` is less than 10, we know only one digit suffices to represent it, so
just return the one-character string containing that digit and we are done.

2) If `n` is equal to or greater than 10, then more than one digit is needed; so:
    a): first compute the string for all but the 1's place,
    b): then compute the one-character string for the 1's place,
and then concatenate the two together into the final sequence.
```

This is a _recursive_ problem statement!  It isn't exactly obvious how we could
write this with the kind of logical statements we used last time.  The thing
we'd kind of like is to be able to hand Dafny a specification that's structured
like this problem statement.

### Dafny Functions are Ghost Code

So far, we've only written Dafny `method`s - as we saw, a method compiles down
into executable code, and can do everything that we'd expect from a
general-purpose programming language: it can call other methods, loop, recur,
declare local variables, modify state, allocate objects on the heap, perform
side-effects, whatever you like.  This means that somewhere inside our
`Fizzbuzz.dll` file we have .NET bytecode generated for `Fizzbuzz()` but not
any of the `requires` or `ensures` clauses.

A Dafny `function`, however, is a different beast: it's an example of _ghost_
code.  In formal verification, ghost constructs exist only as dialogue between
the programmer and the verifier, and get omitted from the final compiled
binary.  Remember from last time that pre- and post-conditions were also left
out; this makes `function`s another way to write more elaborate specifications.
(If you've heard of types being _erased_ after type-checking then the notion of
ghost state might feel familiar to you.)

The downside to `function`s is that their use is more restricted. `function`s
can't have side-effects since they never execute at runtime.  Conversely,
outside of specification clauses like `requires`, `ensures`, and `invariant`,
which themselves are ghost constructs, `function`s can't be called in a method.
In that sense, ghost code and real code really do occupy [distinct
universes](https://www.penguinrandomhouse.com/books/114263/the-city-and-the-city-by-china-mieville/).

## Our string-to-digits specification function

Here's my attempt at translating the English-language problem statement into
Dafny `function`s.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="c1">// Specifies how to convert a natural number to a string
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="kc">function</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">):</span> <span class="kc">string</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span><span class="o">|</span> <span class="o">==&gt;</span> <span class="s1">&#39;0&#39;</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)[</span><span class="nx">i</span><span class="p">]</span> <span class="o">&lt;</span><span class="p">=</span> <span class="s1">&#39;9&#39;</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="kc">if</span> <span class="nx">n</span> <span class="o">&lt;</span> <span class="nx">10</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// Base case: A nat on [0, 10) is just one character long.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">then</span> <span class="p">[</span><span class="nx">dtoc</span><span class="p">(</span><span class="nx">n</span><span class="p">)]</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// Inductive case: Compute all but the last character, then append the final one at the end
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">else</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="o">/</span><span class="nx">10</span><span class="p">)</span> <span class="o">+</span> <span class="p">[</span><span class="nx">dtoc</span><span class="p">(</span><span class="nx">n</span> <span class="o">%</span> <span class="nx">10</span><span class="p">)]</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl"><span class="c1">// Specifies how to convert a base-10 digit to an ASCII character
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="kc">function</span> <span class="nx">dtoc</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">):</span> <span class="nx">char</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="nx">0</span>  <span class="o">&lt;</span><span class="p">=</span>      <span class="nx">n</span>  <span class="o">&lt;</span><span class="p">=</span>  <span class="nx">9</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="s1">&#39;0&#39;</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">dtoc</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span> <span class="o">&lt;</span><span class="p">=</span> <span class="s1">&#39;9&#39;</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="s1">&#39;0&#39;</span> <span class="o">+</span> <span class="nx">n</span> <span class="kc">as</span> <span class="nx">char</span> <span class="c1">// `as` is the type-casting operator
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span>
</div>


Just like how loops need to provably terminate, recursion in Dafny must
reach a base case too.  If we left off the single-digit case in `ntos()` or
recurred with a non-decreasing argument Dafny would reject this.  (I'll stick
with the Dafny convention seen elsewhere that `function` names will be
lowercase, whereas methods will be CamelCase.)

### Specifications specify behaviour, not performance

Notice that `ntos()` seems higher-level and more declarative than the other
Dafny code we've written so far.  Our `Fizzbuzz()` method, by contrast, had a
bunch of loops and picky indexing that we had to think hard about.  This
contrast is intentional: our goal here is to state the problem abstractly as
clearly as we can, without worrying about practical concerns like performance
or whether we're using exactly the right data structures.

In a coding interview, it's not unreasonable for the interviewee to be asked
the time complexity of their solution.  If we suppose that the `+` string
concatenation operation is `O(n)`, and if we recurred for every digit, then our
solution here would be `O(n * log n)`.  We can probably imagine a different
solution with equivalent behaviour and better performance (say, if we
pre-allocated the structure to hold our digits in advance, avoided recursion,
or used machine word-sized integers instead of BigInteger `nat`s).

The tradeoff, of course, is that code that does more things has the opportunity
to get more things wrong.  But having a high-level, abstract specification
function and a lower-level, concrete implementation method gives us the best of
both worlds, so long as we can relate the behaviour of the two.

This is exactly where we are headed: our implementation will have an eye for
runtime efficiency and other practical concerns at the expense of clarity, and
Dafny will prove that whatever our implementation does is _modeled_ by the
abstract `function`.  This reduces the amount of trust we need to have in our
implementation, since now you only need to trust the high-level "easy to read"
specification.

## Can we really trust our friends?

A few words about `ntos()`'s `ensures` clause: This postcondition simply says
that each character in the string should be a valid base-10 digit.  This is of
course necessary, but I can hear some of you screaming that it isn't sufficient
to prove "correctness" of this function.  Don't worry, I agree!  This
post-condition tells us that the returned string must be a representation of a
number, but very little about how it relates to the supplied `nat`.  A constant
function that returns `"42"` on all inputs would satisfy this postcondition,
and we definitely wouldn't want to call that a "provably-correct solution".

When many folks first learn about cool things like automated theorem provers or
type theory, they end up with the misconception that the goal is
incontrovertible and exhaustive program correctness.  Others -- including some
who responded "vigorously" on certain colour-coded tech link aggregation
websites to part 1 of this series -- dismiss formal methods for the opposite
reason.  They end up feeling that formal methods _claim_ incontrovertible
correctness, which they dismiss as impossible.

The latter people are right on one point: "total correctness", whatever that
might mean, is a bar that we shouldn't expect to reach.  We saw this last time:
Our nominally-correct `Fizzbuzz()` was only as good as our (incomplete)
specification.  Whether we're talking about our programs' correctness, our
compiler's correctness, our compiler's compiler's correctness, or just life in
general, [we always have to trust
something](https://www.cs.cmu.edu/~rdriley/487/papers/Thompson_1984_ReflectionsonTrustingTrust.pdf).
Anyone who argues otherwise is probably uninformed or trying to sell you
something.

It's on all of us to treat formal methods as another powerful tool in our
toolbelt, but not as something that it has no hope of living up to.  Even
though `ntos()` is getting checked by a pretty cool verifier, the fact that its
specification has holes in it _is a valid concern_.  In the same way, we
shouldn't be completely convinced by the presence of unit tests or fancy
dependent types in other languages.  We can use all these techniques (perhaps
multiple ones together!) to increase our confidence of a correct
implementation, but "total" correctness lives and will forever live at the
rainbow-end of an asymptote.

That said, if we can do better then let's do so - let's improve our confidence
in our specification by being more precise about what it should do!

One property that feels reasonable is that if we convert some `nat` to a
string, and then somehow converted that string back to a `nat`, we should have
the same natural number again.  So, let's write another short `function` that
does just that!

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">function</span> <span class="nx">ston</span><span class="p">(</span><span class="nx">s</span><span class="p">:</span> <span class="kc">string</span><span class="p">):</span> <span class="kc">nat</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="o">|</span><span class="nx">s</span><span class="o">|</span> <span class="o">&gt;</span> <span class="nx">0</span>  <span class="c1">// Every string representation of a nat must be nonempty
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">requires</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="o">|</span><span class="nx">s</span><span class="o">|</span> <span class="o">==&gt;</span> <span class="s1">&#39;0&#39;</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">s</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">&lt;</span><span class="p">=</span> <span class="s1">&#39;9&#39;</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="kc">if</span> <span class="o">|</span><span class="nx">s</span><span class="o">|</span> <span class="o">==</span> <span class="nx">1</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// Base case: A string of length 1 only has one digit to consider
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">then</span> <span class="p">(</span><span class="nx">s</span><span class="p">[</span><span class="nx">0</span><span class="p">]</span> <span class="o">-</span> <span class="s1">&#39;0&#39;</span><span class="p">)</span> <span class="kc">as</span> <span class="kc">nat</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// Inductive case: Recur on all but the last character of &#39;s&#39;, then shift the digits over for the final one
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">else</span> <span class="nx">ston</span><span class="p">(</span><span class="nx">s</span><span class="p">[..</span><span class="o">|</span><span class="nx">s</span><span class="o">|</span> <span class="o">-</span> <span class="nx">1</span><span class="p">])</span> <span class="o">*</span> <span class="nx">10</span> <span class="o">+</span> <span class="p">(</span><span class="nx">s</span><span class="p">[</span><span class="o">|</span><span class="nx">s</span><span class="o">|</span> <span class="o">-</span> <span class="nx">1</span><span class="p">]</span> <span class="o">-</span> <span class="s1">&#39;0&#39;</span><span class="p">)</span> <span class="kc">as</span> <span class="kc">nat</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


As an example, we can see that `ntos(12345) == "12345"`, and `ston("12345") ==
12345`, so `ston(ntos(12345)) == 12345`.  Our general claim here is that for
arbitrary `nat`s, `ston(ntos(n)) == n`.  This general fact is pretty important
and ought to stand on its own, so let's factor it out into its own _lemma_.  A
lemma is akin to a "helper proof" that we can make use of in a larger context.
Here's our lemma, which checks out according to Dafny:

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">lemma</span> <span class="nx">sninv</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">ston</span><span class="p">(</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">))</span> <span class="o">==</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl"><span class="p">{}</span>
</span></span>
</div>

Notice that the body of the `lemma` is empty: the only reason it exists is for
Dafny to verify that its postcondition is satisfied!

Okay, could we increase our confidence further?  What about proving
invertibility in the opposite direction?  We might say "well, by a similar
argument, `ntos(ston("12345")) == "12345"`", so can we write another lemma
stating this as a general property too?  If so, then we've bootstrapped _two
correctness proofs in terms of each other_, which would be pretty cool.  Let's
try that and see how far we get.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">lemma</span> <span class="nx">nsinv</span><span class="p">(</span><span class="nx">s</span><span class="p">:</span> <span class="kc">string</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">ston</span><span class="p">(</span><span class="nx">s</span><span class="p">))</span> <span class="o">==</span> <span class="nx">s</span> <span class="c1">// Will Dafny accept this without complaint?
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{}</span>
</span></span>
</div>

Dafny immediately starts complaining out of the gate: it tells us that "a
function precondition might not hold", and gives us the counterexample string
`"%"`.  Aha, of course!  In the first lemma, we implicitly used the fact that
every `nat` has a string representation, but not every string can be converted to a `nat`,
so this makes sense.  Let's fix this lemma with some preconditions, stating that
we are only concerned with strings that satisfy the precondition for `ston()`.
That way, we're restricting our inputs to the space of strings that the
conversion function would provably accept anyway.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">lemma</span> <span class="nx">nsinv</span><span class="p">(</span><span class="nx">s</span><span class="p">:</span> <span class="kc">string</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="o">|</span><span class="nx">s</span><span class="o">|</span> <span class="o">&gt;</span> <span class="nx">0</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="o">|</span><span class="nx">s</span><span class="o">|</span> <span class="o">==&gt;</span> <span class="s1">&#39;0&#39;</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">s</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">&lt;</span><span class="p">=</span> <span class="s1">&#39;9&#39;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">ston</span><span class="p">(</span><span class="nx">s</span><span class="p">))</span> <span class="o">==</span> <span class="nx">s</span>
</span></span><span class="line"><span class="cl"><span class="p">{}</span>
</span></span>
</div>


Is Dafny satisfied now?  Interestingly, no!  And the counterexample it finds is
pretty awesome.  Dafny gives me the string `"04"` as an example where
`ntos(ston(s)) != s`, and this makes sense!  The presence of leading zeroes
means that `nat`s don't have a _unique_ string representation:
`ntos(ston("04")) == "4"`!  There are any number of ambiguous strings, too: `4
== ston("4") == ston("04") == ston("00000004")`.  I wonder how many [format
string
vulnerabilities](https://owasp.org/www-community/attacks/Format_string_attack)
have come about because of a tacit assumption like this?

There are ways to make more precise _which of the equivalent strings will be
generated_, and encode that as part of our specification.  But, let's leave
that discussion until the very end of the post.

## How does this tie back into Fizzbuzz()?

...Hey, remember that we were trying to write `Fizzbuzz()` at some point?

This is where we left `Fizzbuzz()` off last time: remember that we didn't have
a way of specifying the "otherwise, produce the number in string form"
post-condition.  We simply left it out, as a result.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">...</span>
</span></span><span class="line"><span class="cl"><span class="c1">//ensures forall i :: 0 &lt;= i &lt; n ==&gt; i % 3 != 0 &amp;&amp; i % 5 != 0 ==&gt; ret[i] == i // TODO
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl"><span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">j</span> <span class="o">&lt;</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">    <span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="c1">//invariant forall i :: 0 &lt;= i &lt; j ==&gt; i % 3 != 0 &amp;&amp; i % 5 != 0 ==&gt; ret[i] == i // TODO
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="p">...</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="p">(</span><span class="nx">curr_modified</span><span class="p">)</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="p">...</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;TODO: convert j to a string&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


What can `ntos()` buy us here?  Well, the specification for `Fizzbuzz()` ought
to say that `ret[i]` must be the string representation of `i`, _which we now
have a way to specify_!  Concretely, our postcondition can state that `ret[i]
== ntos(i)`!

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">...</span>
</span></span><span class="line"><span class="cl"><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span> <span class="c1">// Yay!
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl"><span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">j</span> <span class="o">&lt;</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">    <span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span> <span class="c1">// Woo!
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="p">...</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="p">(</span><span class="nx">curr_modified</span><span class="p">)</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="p">...</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;TODO: convert j to a string&#34;</span><span class="p">;</span> <span class="c1">// Hmm...
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="p">}</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


Of course, we're not done yet: Dafny tells us that our loop invariant isn't
being maintained because we're still assigning that TODO string in the
implementation.  What happens if we change that assignment to `ret[j] :=
ntos(i)`?  Dafny tells us, `A call to a ghost function is allowed only in
specification contexts`.  This fits our understanding of ghost constructs
living in two parallel worlds.

One simple solution is to mark `ntos()` as _both_ a `function` and a `method`.
So-called `function method`s can be thought of as methods whose runtime behaviour
is restricted enough that they can't perform any operation that a `function`
couldn't, like mutate state.  Since `ntos()` is side effect-free and only
computes a return value, we can mark it as a `function method` and Dafny will
let us use it in both specifications and implementations.


<div class="dafny-code">
<span class="line"><span class="cl"><span class="c1">// Specifies how to and implements to convert a natural number to a string
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="kc">function</span> <span class="kc">method</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">):</span> <span class="kc">string</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span><span class="o">|</span> <span class="o">==&gt;</span> <span class="s1">&#39;0&#39;</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)[</span><span class="
nx">i</span><span class="p">]</span> <span class="o">&lt;</span><span class="p">=</span> <span class="s1">&#39;9&#39;</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="kc">if</span> <span class="nx">n</span> <span class="o">&lt;</span> <span class="nx">10</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// Base case: A nat on [0, 10) is just one character long.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">then</span> <span class="p">[</span><span class="nx">dtoc</span><span class="p">(</span><span class="nx">n</span><span class="p">)]</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// Inductive case: Compute all but the last character, then append the final one at the end
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">else</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="o">/</span><span class="nx">10</span><span class="p">)</span> <span class="o">+</span> <span class="p">[</span><span class="nx">dtoc</span><span class="p">(</span><span class="nx">n</span> <span class="o">%</span> <span class="nx">10</span><span class="p">)]</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">...</span>
</span></span><span class="line"><span class="cl"><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span> <span class="c1">// Yay!  Calling a function method as a function!
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl"><span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">j</span> <span class="o">&lt;</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">    <span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span> <span class="c1">// Woo!  Calling a function method as a function!
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="p">...</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="p">(</span><span class="nx">curr_modified</span><span class="p">)</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="p">...</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">);</span> <span class="c1">// Nice! Calling a function method as a method!
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="p">}</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


This change is enough to get our `Fizzbuzz()` verified and compiling!!  Let's
run it and see how it looks.

```bash
$ ~/code/dafny/Binaries/Dafny Fizzbuzz.dfy && dotnet Fizzbuzz.dll | head -n 20

Dafny program verifier finished with 8 verified, 0 errors
Compiled assembly into Fizzbuzz.dll
fizzbuzz
1
2
fizz
4
buzz
fizz
7
8
fizz
buzz
11
fizz
13
14
fizzbuzz
16
17
fizz
19
$
```

Look at that!  At long last, we have a working solution!

## But nobody will actually do this, Nathan!

Hopefully you've found this a fun way to learn a bit of formal methods and a
funny thought experiment.  Some of the more literally-minded among you may be
wondering whether I'm _actually_ advocating for readers doing their next
interview loop in Dafny.  By all means go ahead, but choosing an uncommon
language might be slightly-high risk for you.  If I can get bounced from a
phone screen for not using the interviewer's favourite language (Ruby
developers can be... a lot sometimes), you might be setting yourself up for a
frustrating job hunt.

That said, I do genuinely think that there are lessons here that can apply to
your next whiteboard interview, even if you're sticking with Python or Java or
whatever your favourite interviewing language is.

In both blog posts, we began thinking through the problem by way of writing a
textual problem statement.  This did more than just kill a few minutes of time:
I really do think this helps ground the interviewee within the problem before
any code actually gets written.  This is also a great time to write example
calls with expected outputs; we did that this time when trying to concoct a
general lemma for `ntos()`'s relationship to `ston()`, for instance.

Yes, it's true that most languages don't have compile-time invariant checks,
nor pre- and post-condition clauses.  That's okay, though - nothing stopping
you from simply writing those as at-runtime `assert()` statements, or even just
informal comment blocks.  Jon Bentley's [articles on writing correct code](https://www.cs.tufts.edu/~nr/cs257/archive/jon-bentley/correct-programs.pdf), which he collated into his book
Programming Pearls, has great examples of stating invariants in comment blocks
not to _prove_ your code correct but to guide your thinking towards correct
code.

In an interview, of course, there's no underlying formal methods magic to
verify that your invariants are right, but just like how ghost code set up a
dialogue between the programmer and the verifier, doing this informally sets up
a similar dialogue between the programmer and interviewer.  And if you're
interviewing at a more forward-thinking company where you're given an actual
text editor and unit test suite to pass, if you write them as `assert()`s
you'll at least have runtime failures.  Those assertion failures will also
likely occur closer to where the bug lies, giving you a leg up on fixing the
issue.

## Next time: a more realistic `ntos()`!

Using `ntos()` as a `function method` might be enough to satisfy you, or your
whiteboard interviewer.  But remember from earlier that we intentionally traded
a bit of performance in `ntos()` for writing it in a clearer, more declarative
style.  We're leaving some cycles on the table that we don't necessarily have
to here!  Writing implementation code in Dafny shouldn't feel like programming
in a functional language (or, worse, writing proofs on a whiteboard!); it gives
us loops, mutable structures, and other traditional programming language
constructs, so why shouldn't we make use of those if we can?

[Next time](/posts/proving-the-coding-interview-3/), we'll leave
`ntos()` as it was as a mere `function`.  We'll instead port [a real-world,
optimised int conversion implementation from another
language](https://hg.openjdk.java.net/jdk7u/jdk7u6/jdk/file/8c2c5d63a17e/src/share/classes/java/lang/Integer.java#l327)
to Dafny and prove that it satisfies `ntos()`.  Hopefully this should help
convince you that we don't need to just verify silly or naive problems in
Dafny, but rather that it's expressive enough for real-world software that's
both mission-critical as well as high-performance.

We'll also extend the "...but nobody will actually do this!" criticism from
specifically interview problems and discuss the practicalities of verifying
your -- yes, your! -- production software like this.

## Your turn:

Until [next time](/posts/proving-the-coding-interview-3/), here are
some ideas to get you playing around with some of the things we did today:

* If you're familiar with first-order logic, you might be interested in seeing
precisely what formulas Dafny generates and asks its underlying
[prover](https://github.com/Z3Prover/z3) to validate.  Using Dafny's `/proverLog`
command-line flag, dump the formulas for `ntos()` and see if you can follow
along with them.  (Dafny will generates _tonnes_ of output here, so it's best
to hand it a file that contains only the parts of the file you're actually
interested in.)
* We also saw that writing the inverse composition specification was tough
because of the leading zero ambiguity.  Come up with a way to extend `ntos()`
and `ston()`'s specifications in order to satisfy Dafny.  (One idea might be to
define the notion of a "canonicalized" string, which is one with no unnecessary
digits, and convince Dafny that `ntos()` only returns canonicalized strings.)

As always, if you do, [drop me a line and let me know](https://www.twitter.com/ntalyour).

## Thanks!

Thanks to
Sammy Thomas and Cole Vick
for feedback on early drafts of this post!

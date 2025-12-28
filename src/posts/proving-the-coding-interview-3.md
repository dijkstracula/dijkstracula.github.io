---
layout: post.njk
title: "Proving the Coding Interview: verifying the JDK's `Integer.toString()`"
date: 2022-04-30T20:47:23-05:00
tags: [post, dafny, verification, provingthecodinginterview]
excerpt: "A faster, but just as correct, nat -> string converter"
---

This is the third of a three part series:
[Part 1](/posts/proving-the-coding-interview/) | 
[Part 2](/posts/proving-the-coding-interview-2/) |
Part 3

Welcome back to the final installment of Proving The Coding Interview!  In the
[previous article](/posts/proving-the-coding-interview-2/) we
completed our verification of the venerable `Fizzbuzz()` interview question by
implementing a nat-to-string conversion `function method`.  That helper was
correct but suboptimal in terms of performance, and not really structured the
way a developer would really implement it in an OOP language.

Since we're already familiar with Dafny by now, I thought it'd be fun to
port an actual, real world int-to-string conversion routine to Dafny.  In
particular, our implementation'll be heavily drawn from Java's
[Integer.toString()](https://hg.openjdk.java.net/jdk7u/jdk7u6/jdk/file/8c2c5d63a17e/src/share/classes/java/lang/Integer.java#l327)
implementation.  Our version will be slightly simplified -- we'll elide some of
the more esoteric bitwise-twiddling hacks -- but the broad strokes will be the
same. 

## Why implement this a second time?

Some of you might rightfully be wondering what's going to be different this
time around.  What's the value in looking at the same problem twice?

Last time we begun with an English-language representation of the interview
problem and concluded with `ntos()`, a declarative specification that Dafny
could still compile down into executable code.  Here, we imagine a different
style of interview: One could imagine _defining the problem in terms of
supplying the specification_ and asking the candidate to build a refined
implementation, maybe with some performance constraints like improving time
complexity or minimising the number of reallocations.

## Previously...

Here's our specification from last time and our implementation's skeleton.
I've added some comments outlining the major components, and written a single
postcondition: whatever the function returns must match what the specification
would have!


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
</span></span><span class="line"><span class="cl"><span class="c1">// Implements compilable code that behaves equvialently to `ntos()`
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="kc">method</span> <span class="nx">NatToString</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="kc">string</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// The implementation&#39;s external behaviour must match the specification&#39;s,
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="c1">// even though internally the two will look very different from each other!
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">ensures</span> <span class="nx">ret</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="c1">//1. Preallocate an array of size equal to the number of digits of `n`.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl">    <span class="c1">//2. Work backwards from the end of the array, filling in each digit in turn...
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="c1">//  a. Fast path when n &gt;= 2^16: write two digits per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="c1">//  b. Slow path when n &lt; 2^16: write one digit per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span>
</div>


Remember that because we want this code to actually run, we're writing
`NatToString()` as a `method` rather than a `function`.  Similarly, `ntos()`
should now be only ghost code, so I've reverted it back to a `function` instead
of a `function method`.

Looking at the comment pseudocode, already we can see a bunch of implementation
details that are absent from the specification: Rather than building up the
string by concatenating substrings each time, we'll compute how much memory we
need in advance and then write digits into each element.

Also, our business logic is more complicated: our specification doesn't
indicate that larger `nat`s should be processed differently than smaller ones,
but our specific implementation will.

## Step 1: Preallocating the array of characters

Our first task is to allocate an array of characters big enough to hold our
`nat`'s digits.  In a conventional programming language, we might write
something like `new char[int(log10(n) + 1)]`, but -- surprise! -- Dafny doesn't
have a `log10()` function.  Instead, let's write some code to iteratively
compute how long the array needs to be.  We could implement this right in
`NatToString()` but it's always nice to pull it out into a helper method, which
I'm calling `StringSize()`.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">StringSize</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">digits</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// TODO: What should the specification be for this method?
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// TODO: What should the implementation be for this method?
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span>
</div>

It's not enough to just write this method; we want to know that it satisifies
some formal specification.  What can we say about a good specification for
`StringSize()`?  At first blush it might feel as though we need to write an
entire functional reimplementation of it as we did with `ntos()`.  I can hear
you groaning already.  But we can actually reuse `ntos()`: whatever string it
returns would be of a certain length, and that's exactly the value we want
`StringSize()` to return!  So, our specification for `StringSize()` should
state that its return value equals _the length of the string returned by
`ntos()`_.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">StringSize</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">digits</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">digits</span> <span class="o">==</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span><span class="o">|</span> <span class="c1">// recall that |s| is the length of s
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// TODO: What should the implementation be for this method?
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span>
</div>

Something that's really cool about this line of thinking is that, even though
`ntos()` is ghost code, we were able to make use of properties of its return
value (like its length) in other ghost clauses.  So long as we're operating in
the "ghost world" of our specification, we can almost treat it like an
ordinary, traditional "function" that we can call!  Hopefully you can start to
see that in general a specification is like "a library of ghost code" that a
verifier can make use of throughout a larger program.  

What's more, using `ntos()` multiple times in different contexts increases our
confidence that it accurately models our implementation, since there are more
opportunities for an incorrect spec to get trapped in a contradiction elsewhere
in our correctness proof.

All right, it's now time to write the body of `StringSize()`.  This was my
first attempt; this is probably what I'd have scribbled on a whiteboard if
someone had asked me to do it in an interview.  Bad news for my future job
prospects: I didn't get it right on the first try.  In fact, made the same
mistake twice in two different places.  Can you spot it?

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">StringSize</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">digits</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">digits</span> <span class="o">==</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span><span class="o">|</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">// We start with i, a natural number of a certain number of digits.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">var</span> <span class="nx">i</span><span class="p">:</span> <span class="kc">nat</span> <span class="o">:=</span> <span class="nx">n</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="nx">digits</span> <span class="o">:=</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">i</span> <span class="o">&gt;</span> <span class="nx">0</span>
</span></span><span class="line"><span class="cl">        <span class="c1">// Since each time through the loop we divide out one digit from `i` and
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="c1">// add one to `digits`, this formula should always hold.  ...Or does it?
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="kc">invariant</span> <span class="nx">digits</span> <span class="o">+</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span><span class="o">|</span> <span class="o">==</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span><span class="o">|</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="nx">digits</span> <span class="o">:=</span> <span class="nx">digits</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="nx">i</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">/</span> <span class="nx">10</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">// We end having incremented `digits` once for every digit in `i`, so
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="c1">// digits must be equal to how many digits `i` began with.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span>
</div>

My first mistake was a little bit embarrasing: the case where `n == 0` is
flat-out wrong!  We'll never increment `digits`, so we'll report that the
string representation of the number zero is itself of length zero, when of
course it should be of length one (since `len("0") == 1`!).

The second place is more interesting.  Dafny tells me that my loop invariant is
always maintained, and gives me the following counterexample where it breaks:

```bash
        n : int = 7
        i : int = 0
        digits : int = 1
```

Since `i == 0`, we know the counterexample has to do when the loop guard is
false and we're about to break out and return.  What's happening here is: After
dealing with the one's place and dividing `i` to become zero, `digits`
increases but the length of `ntos(i)` will _not_ decrease, since `ntos(0)` is
not a shorter string than `ntos(7)`!

We can solve this either by making the loop invariant more complicated or by
handling the 1s place outside the loop; I chose the latter.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">StringSize</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">digits</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">digits</span> <span class="o">==</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span><span class="o">|</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">i</span><span class="p">:</span> <span class="kc">nat</span> <span class="o">:=</span> <span class="nx">n</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="nx">digits</span> <span class="o">:=</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">i</span> <span class="o">&gt;=</span> <span class="nx">10</span> <span class="c1">// Handle the 10s, 100s, 1000s, etc. cases
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="kc">invariant</span> <span class="nx">digits</span> <span class="o">+</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span><span class="o">|</span> <span class="o">==</span> <span class="o">|</span><span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span><span class="o">|</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="nx">digits</span> <span class="o">:=</span> <span class="nx">digits</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="nx">i</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">/</span> <span class="nx">10</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl">    <span class="nx">digits</span> <span class="o">:=</span> <span class="nx">digits</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span> <span class="c1">// Handle the 1s case outside the loop to keep the invariant simpler.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span>
</div>


Here we see an interesting design tradeoff: in order for the verifier to
properly understand our code we had to either make the implementation gnarlier
or the spec gnarlier.  Which of the two's simplicity should be sacrificed?  As
with all complicated things in life, the answer is that [it
depends](https://programmingisterrible.com/post/162346490883/how-do-you-cut-a-monolith-in-half).
Sometimes contorting a specification even slightly can cause [verification
times to explode
nonlinearly](https://www.cs.utexas.edu/~bornholt/papers/symfix-vmcai20.pdf).
Conversely, contorting an implementation might end up in the unfortunate place
where the verifier -- but only the verifier -- understands what the heck the
code is even doing!

And it depends on not just technical concerns but social ones, too.  What do
you and your team prioritize?  In what does your team's expertise lie, and is
that expertise evenly distributed within the team?  And who's going to be
reading and maintaining your code six months from now, and what will _they_
prioritize?

## Step 2: Digit calculation

All right!  With step 1 completed we are now able to correctly allocate the
char array that will hold our string's characters.  Let's look at what we
can fill in so far:

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">NatToString</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="kc">string</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// The implementation&#39;s return value must match the specification&#39;s
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">ensures</span> <span class="nx">ret</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="c1">//1. Preallocate an array of size equal to the number of digits of `n`.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">var</span> <span class="nx">len</span> <span class="o">:=</span> <span class="nx">StringSize</span><span class="p">(</span><span class="nx">n</span><span class="p">);</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">chars</span> <span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="nx">char</span><span class="o">&gt;</span> <span class="o">:=</span> <span class="kc">new</span> <span class="nx">char</span><span class="p">[</span><span class="nx">len</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//2. Work backwards from the end of the array, filling in each digit in turn.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">var</span> <span class="nx">i</span><span class="p">:</span> <span class="kc">nat</span> <span class="o">:=</span> <span class="nx">n</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">charPos</span><span class="p">:</span> <span class="kc">nat</span> <span class="o">:=</span> <span class="nx">len</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//  a. Fast path when i &gt;= 2^16: write two digits per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">while</span> <span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="c1">// TODO: i /= 100 and charPos -= 2 on each iteration...
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//  b. Slow path when 0 &lt;= i &lt; 2^16. write one digit per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">while</span> <span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="c1">// TODO: i /= 10 and charPos -= 1 on each iteration...
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">assert</span> <span class="nx">charPos</span> <span class="o">==</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">assert</span> <span class="nx">chars</span><span class="p">[..]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">);</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="nx">chars</span><span class="p">[..];</span> <span class="c1">// slice the entire char array into the return string.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span>
</div>

Here, we'll have two variables that get modified the fast path and slow path
loops: `i` is the current value that we're writing into the `chars` array, and
`charPos` refers to the first character of our partially-completed string.

Okay, here's the easy part: let's take the Java implementation (lines 355-373
of
[`Integer.java`](https://hg.openjdk.java.net/jdk7u/jdk7u6/jdk/file/8c2c5d63a17e/src/share/classes/java/lang/Integer.java#l356))
and just transliterate it into Dafny.  The only real change for us is that
`nat`s in Dafny don't have left-shift operators, so I'll simply turn those
subexpressions into their equivalent multiplication by a power of two.
(Arguably, a good compiler should be able to do that transformation for us
anyway!)

<div class="dafny-code">
<span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">onesPlace</span> <span class="o">:=</span> <span class="s2">&#34;0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">tensPlace</span> <span class="o">:=</span> <span class="s2">&#34;0000000000111111111122222222223333333333444444444455555555556666666666777777777788888888889999999999&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//2.1. Fast path when i &gt;= 2^16: write two digits per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">while</span> <span class="nx">i</span> <span class="o">&gt;=</span> <span class="nx">65536</span>
</span></span><span class="line"><span class="cl">        <span class="c1">// TODO: what should our loop invariants be?
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">{</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">q</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">/</span> <span class="nx">100</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">r</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">-</span> <span class="p">((</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">64</span><span class="p">)</span> <span class="o">+</span> <span class="p">(</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">32</span><span class="p">)</span> <span class="o">+</span> <span class="p">(</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">4</span><span class="p">));</span> <span class="c1">// Originally r = i - ((q &lt;&lt; 6) + (q &lt;&lt; 5) + (q &lt;&lt; 2))
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl">        <span class="kc">assert</span> <span class="nx">r</span> <span class="o">==</span> <span class="nx">i</span> <span class="o">-</span> <span class="p">(</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">100</span><span class="p">);</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span> <span class="o">-</span> <span class="nx">1</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">onesPlace</span><span class="p">[</span><span class="nx">r</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">        <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span> <span class="o">-</span> <span class="nx">2</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">tensPlace</span><span class="p">[</span><span class="nx">r</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">charPos</span> <span class="o">:=</span> <span class="nx">charPos</span> <span class="o">-</span> <span class="nx">2</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">i</span> <span class="o">:=</span> <span class="nx">q</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//2.2. Slow path when i &lt; 2^16. write one digit per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">while</span> <span class="kc">true</span>
</span></span><span class="line"><span class="cl">        <span class="c1">// TODO: what should our loop invariants be?
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">q</span> <span class="o">:=</span> <span class="p">(</span><span class="nx">i</span> <span class="o">*</span> <span class="nx">52429</span><span class="p">)</span> <span class="o">/</span> <span class="p">(</span><span class="nx">524288</span><span class="p">);</span>  <span class="c1">// Originally q = (i * 52429) &gt;&gt;&gt; (16+3);
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="kc">var</span> <span class="nx">r</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">-</span> <span class="p">((</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">8</span><span class="p">)</span> <span class="o">+</span> <span class="p">(</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">2</span><span class="p">));</span> <span class="c1">// Originally r = i - ((q &lt;&lt; 3) + (q &lt;&lt; 1))
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl">        <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span> <span class="o">-</span> <span class="nx">1</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">onesPlace</span><span class="p">[</span><span class="nx">r</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">        <span class="nx">charPos</span> <span class="o">:=</span> <span class="nx">charPos</span> <span class="o">-</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">i</span> <span class="o">:=</span> <span class="nx">q</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="nx">i</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="kc">break</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span>
</div>


In the original Java code, there's something amusing on [line
358](https://hg.openjdk.java.net/jdk7u/jdk7u6/jdk/file/8c2c5d63a17e/src/share/classes/java/lang/Integer.java#l358):
there's a comment following some gnarly bit-twiddling that says "here's an
equivalent, simpler expression".  In Dafny we don't have to leave this as a
comment: I translated that comment into an `assert` clause, which the verifier
will _prove_ and block compilation if it could ever not hold!

### Coming up with our loop invariants

Unsurprisingly, just like with `Fizzbuzz()` and `StringSize()`, Dafny needs
some help understanding how our loops relate to our final postcondition.
Unlike those methods, though, we'll need to supply it with more than one loop
invariant.

Let's sketch out how this method might operate over some concrete input, like
the `nat` 1234567:  First, it will allocate an array of length 7.  Since n
is larger than 2^16, we'll execute the fast path first.  Upon entering the
loop for the first time, our state looks like this:

```
n = 1234567             ._._._._._._._.
i = 1234567     chars = | | | | | | | |
                                      ^--- charPos
```

On the second iteration, we'll have shaved two digits off of `i`, and populated
the final two values of `chars`:

```
n = 1234567             ._._._._._._._.
i = 12345       chars = | | | | | |6|7|
                                  ^--- charPos
```

At this point, the fast path condition is no longer satisfied, so we'll enter
the slow path, in which case we shave one digit off `i` and populate one more
value of `chars`:

```
n = 1234567             ._._._._._._._.
i = 1234        chars = | | | | |5|6|7|
                                ^--- charPos
```

And we keep iterating until i == 0; namely, we are out of digits to write into
`chars`!

```
n = 1234567             ._._._._._._._.
i = 0           chars = |1|2|3|4|5|6|7|
                        ^--- charPos
```

At this point we can start to see the invariant brewing!  In each of these
figures, the string representation of whatever `i` is, concatenated with
whatever we've filled into `chars` (namely, from the index at `charPos` to the
end of the string), is the string representation of `n`.  Hey, that's what the
whole method is supposed to compute!  So, our main loop invariant is:

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">NatToString</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="kc">string</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="c1">//  a. Fast path when i &gt; 2^16: write two digits per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">while</span> <span class="nx">i</span> <span class="o">&gt;=</span> <span class="nx">65536</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span> <span class="o">+</span> <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span><span class="p">..]</span> <span class="p">=</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//  b. Slow path when i &lt;= 2^16. write one digit per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">while</span> <span class="kc">true</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span> <span class="o">+</span> <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span><span class="p">..]</span> <span class="p">=</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span>
</div>

At this point we're almost home.  The above is the only loop invariant that
requires any real creativity on our parts; Dafny is pretty specific about
the remaining things it can't figure out without our help.  Concretely, it
tells us it's confused on two minor points: because we index into `chars` with
a variable that isn't our loop variable `i`, we need to remind Dafny that
`charPos` will always be in bounds.  And because the slow path's loop guard
strangely doesn't involve `i`, we need to tell Dafny how the loop will
terminate: that the loop gets closer to terminating as `i` gets smaller.  So,
our final Dafny method is:

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">NatToString</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">nat</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="kc">string</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="c1">// The implementation&#39;s return value must match the specification&#39;s
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">ensures</span> <span class="nx">ret</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="c1">//1. Preallocate an array of size equal to the number of digits of `n`.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">var</span> <span class="nx">len</span> <span class="o">:=</span> <span class="nx">StringSize</span><span class="p">(</span><span class="nx">n</span><span class="p">);</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">chars</span> <span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="nx">char</span><span class="o">&gt;</span> <span class="o">:=</span> <span class="kc">new</span> <span class="nx">char</span><span class="p">[</span><span class="nx">len</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//2. Work backwards from the end of the array, filling in each digit in turn.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">var</span> <span class="nx">i</span><span class="p">:</span> <span class="kc">nat</span> <span class="o">:=</span> <span class="nx">n</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">charPos</span><span class="p">:</span> <span class="kc">nat</span> <span class="o">:=</span> <span class="nx">len</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">onesPlace</span> <span class="o">:=</span> <span class="s2">&#34;0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">tensPlace</span> <span class="o">:=</span> <span class="s2">&#34;0000000000111111111122222222223333333333444444444455555555556666666666777777777788888888889999999999&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//2.1. Fast path when i &gt;= 2^16: write two digits per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">while</span> <span class="nx">i</span> <span class="o">&gt;=</span> <span class="nx">65536</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="nx">charPos</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">len</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span> <span class="o">+</span> <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span><span class="p">..]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">q</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">/</span> <span class="nx">100</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">r</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">-</span> <span class="p">((</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">64</span><span class="p">)</span> <span class="o">+</span> <span class="p">(</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">32</span><span class="p">)</span> <span class="o">+</span> <span class="p">(</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">4</span><span class="p">));</span> <span class="c1">// Originally r = i - ((q &lt;&lt; 6) + (q &lt;&lt; 5) + (q &lt;&lt; 2))
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl">        <span class="kc">assert</span> <span class="nx">r</span> <span class="o">==</span> <span class="nx">i</span> <span class="o">-</span> <span class="p">(</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">100</span><span class="p">);</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span> <span class="o">-</span> <span class="nx">1</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">onesPlace</span><span class="p">[</span><span class="nx">r</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">        <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span> <span class="o">-</span> <span class="nx">2</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">tensPlace</span><span class="p">[</span><span class="nx">r</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">charPos</span> <span class="o">:=</span> <span class="nx">charPos</span> <span class="o">-</span> <span class="nx">2</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">i</span> <span class="o">:=</span> <span class="nx">q</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="c1">//2.2. Slow path when i &lt; 2^16. write one digit per iteration.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">while</span> <span class="kc">true</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">charPos</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">len</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span> <span class="o">+</span> <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span><span class="p">..]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">        <span class="kc">decreases</span> <span class="nx">i</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">q</span> <span class="o">:=</span> <span class="p">(</span><span class="nx">i</span> <span class="o">*</span> <span class="nx">52429</span><span class="p">)</span> <span class="o">/</span> <span class="p">(</span><span class="nx">524288</span><span class="p">);</span>  <span class="c1">// Originally q = (i * 52429) &gt;&gt;&gt; (16+3);
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="kc">var</span> <span class="nx">r</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">-</span> <span class="p">((</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">8</span><span class="p">)</span> <span class="o">+</span> <span class="p">(</span><span class="nx">q</span> <span class="o">*</span> <span class="nx">2</span><span class="p">));</span> <span class="c1">// Originally r = i - ((q &lt;&lt; 3) + (q &lt;&lt; 1))
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl">        <span class="nx">chars</span><span class="p">[</span><span class="nx">charPos</span> <span class="o">-</span> <span class="nx">1</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">onesPlace</span><span class="p">[</span><span class="nx">r</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">        <span class="nx">charPos</span> <span class="o">:=</span> <span class="nx">charPos</span> <span class="o">-</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">i</span> <span class="o">:=</span> <span class="nx">q</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="nx">i</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="kc">break</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="nx">chars</span><span class="p">[..];</span> <span class="c1">// Slice the entire array as the return string
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl">    <span class="kc">assert</span> <span class="nx">charPos</span> <span class="o">==</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">assert</span> <span class="nx">ret</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">n</span><span class="p">);</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>

## The home stretch: integrating it into Fizzbuzz()

...Hey, remember that we were trying to write `Fizzbuzz()` at some point?

What's the very last change we need to do?  Why, get rid of the TODO string
assignment and replace it with a method call into `NatToString()`!

At long, long last, here's our final, complete `Fizzbuzz()`:

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="kc">requires</span> <span class="nx">n</span> <span class="o">&gt;=</span> <span class="nx">0</span>
</span></span><span class="line"><span class="cl"><span class="kc">ensures</span> <span class="nx">n</span> <span class="o">==</span> <span class="nx">ret</span><span class="p">.</span><span class="nx">Length</span>
</span></span><span class="line"><span class="cl"><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizz&#34;</span>
</span></span><span class="line"><span class="cl"><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;buzz&#34;</span>
</span></span><span class="line"><span class="cl"><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span>              <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizzbuzz&#34;</span>
</span></span><span class="line"><span class="cl"><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="kc">new</span> <span class="kc">string</span><span class="p">[</span><span class="nx">n</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">j</span> <span class="o">:=</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">j</span> <span class="o">&lt;</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">    <span class="kc">invariant</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">j</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">    <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;buzz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span>              <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizzbuzz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="nx">ntos</span><span class="p">(</span><span class="nx">i</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">curr</span> <span class="p">:</span> <span class="kc">string</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="nx">curr</span> <span class="o">:=</span> <span class="p">[];</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">curr_modified</span> <span class="p">:</span> <span class="nx">bool</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="nx">curr_modified</span> <span class="o">:=</span> <span class="kc">false</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="p">(</span><span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span><span class="p">)</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">curr</span> <span class="o">:=</span> <span class="nx">curr</span> <span class="o">+</span> <span class="s2">&#34;fizz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">            <span class="nx">curr_modified</span> <span class="o">:=</span> <span class="kc">true</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="p">(</span><span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span><span class="p">)</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">curr</span> <span class="o">:=</span> <span class="nx">curr</span> <span class="o">+</span> <span class="s2">&#34;buzz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">            <span class="nx">curr_modified</span> <span class="o">:=</span> <span class="kc">true</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="p">(</span><span class="nx">curr_modified</span><span class="p">)</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">curr</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">NatToString</span><span class="p">(</span><span class="nx">j</span><span class="p">);</span> <span class="c1">// Booyah!
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">j</span> <span class="o">:=</span> <span class="nx">j</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


...and here's our final implementation running, functionally identical to our
version from the end of the previous post:

```bash
$ ~/code/dafny/Binaries/Dafny Fizzbuzz.dfy && dotnet Fizzbuzz.dll | head -n 20

Dafny program verifier finished with 10 verified, 0 errors
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

## Your turn:

Thanks so much for making it to the end of this series of posts!  Let me leave
you with a suggestion to extend this code if you're so inclined: This whole
time we've been using BigInteger-style `nat`s to represent numbers.  In the
previous post I mentioned that implementation code can operate on fixed-width
machine datatypes, which we might want for performance reasons, while the
specification can still speak about unbounded `nat`s instead.  In this way,
the specific representation of `n` is an implementation detail, just like the
precise algorithm that we use to compute the string's elements; this also means
`ntos()` could specify the behaviour for all of `UInt32ToString()`,
`UInt16ToString()` or `UInt64ToString()`.

Concretely: Try changing the argument of `NatToString()` to take an argument of
type `bv32` instead - this is a _bitvector_ of 32 bits.  This will let you use
the bitwise operators in the Java implementation that we had to turn into
multiplication, making the Dafny code look even closer to the original.  You
shouldn't need to change anything inside `ntos()` but you might have to modify
your method's postconditions to satisfy the typechecker.

Happy trails and happy proving!

Thanks to
Sammy Thomas,
Cole Vick,
and
Dani Wang
for debugging assistance and feedback on early drafts of this post!

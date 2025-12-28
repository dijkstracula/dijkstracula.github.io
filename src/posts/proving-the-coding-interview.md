---
layout: post.njk
title: "Proving the Coding Interview"
date: 2022-04-17T14:18:48-05:00
tags: [post, dafny, verification, provingthecodinginterview]
excerpt: "Applying interesting research to uninteresting interview problems"
---

This is the first of a three part series:
Part 1 |
[Part 2](/posts/proving-the-coding-interview-2/) |
[Part 3](/posts/proving-the-coding-interview-3/)

Enjoying programming interview questions is one of those things that nobody
should admit to in polite company.  But as with so many other things in life, a
good gimmick can make the most tedious chore bearable if not outright pleasant.
And if you're a grad student and can use that chore as a procrastination
tactic, then all the better! (Sorry,
[James](https://www.cs.utexas.edu/~bornholt/), if you're reading this, I'll get
on whatever it is tomorrow!)

As it happens, it's summer internship interview season, and with a new set of
interview loops comes a need for yet another gimmick.  This time, I figured:
given my research interests in practical uses of formal verification, why not
put my "checkable correctness proof" money where my "bug-ridden half-hearted
implementation" mouth is, and try to formally verify the correctness of my
practice problems' solutions?  I can't honestly claim this will convince a
company to give me a summer job, but at least I'll have briefly entertained
myself in the process.

My first task was to choose an interview problem that only formal methods could
make briefly interesting.

## Our problem statement

I can't think of an interview problem that's both as widely popular and yet
wildly uninteresting as [FizzBuzz](https://en.wikipedia.org/wiki/Fizz_buzz).
The problem's arbitrary and divorced from any real use-cases, it's never
terribly satisfying to implement, and is fiddly enough that it's easy to trip
over an off-by-one error or incorrect if/else statement.  It's the poster child
for misguided tech company interviews, and yet I've actually been asked it before!

Okay, here's the Fizzbuzz problem:

```
Print `n` lines of output, where:

1) Every third line (unless it's a multiple of 15) reads "fizz";
2) Every fifth line (unless it's a multiple of 15) reads "buzz";
3) Every fifteenth line reads "fizzbuzz";
4) Every other line should read the number of lines previously printed out.
```

As any careful programmer will tell you, reasoning about side-effects like
printing in unit tests is difficult, and the same is true when it comes to
coming up with a good formal model for program behaviour.  So, let's break this
problem into two steps: first we'll generate an array of values and then state
properties that the array has to satisfy.  Then, we'll just print that array
out:

```
First, construct a list of strings of length `n`, such that the following hold
for all indexes `i` from 0 to n:

1) If i is a multiple of 3 (but not of 5) then the `i`th element equals "fizz";
2) If i is a multiple of 5 (but not of 3) then the `i`th element equals "buzz";
3) If i is a multiple of 15 then the `i`th element equals "fizzbuzz";
4) Otherwise, the `i`th element equals the string representation of `i`.

Then, print out, separated by a newline, every element in the list.
```

## The Dafny programming language

There are many new languages that make formally verifying real software easier
than ever before: One such language is called
[Dafny](https://github.com/dafny-lang/dafny), originally designed at Microsoft
Research and now under the stewardship of folks at
[AWS](https://www.youtube.com/watch?v=9NEQbFLtDmg&t=988s).  Dafny is a great
gateway to software verification because the style of programming looks so
similar to what you'd write in an OOP language like Java or C#, and does its
best to automate most of the correctness-proving mechanics away from you.  

Let's write some Dafny code!  Don't worry too much about every individual piece
of syntax.  The broad strokes should feel familiar-ish to you and I'll explain
the weird stuff as we come across it.  

Here's the skeleton of our program that calls our `Fizzbuzz()` implementation
and prints out the array it returns.  In Dafny, a method may or may not be
associated with an object - since it doesn't make sense to use classes for this
particular problem these ones won't be.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="kc">new</span> <span class="kc">string</span><span class="p">[</span><span class="nx">n</span><span class="p">];</span> <span class="c1">// the `ret` variable is the one returned to the caller.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Main</span><span class="p">()</span>
</span></span><span class="line"><span class="cl"><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">n</span> <span class="o">:=</span> <span class="nx">100</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">fb</span> <span class="o">:=</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">);</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">i</span> <span class="o">:=</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="kc">print</span><span class="p">(</span><span class="nx">fb</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">+</span> <span class="s2">&#34;\n&#34;</span><span class="p">);</span>
</span></span><span class="line"><span class="cl">        <span class="nx">i</span> <span class="o">:=</span> <span class="nx">i</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


Already the Dafny compiler complains about two potential problems.  See if you
can spot one of the issues before continuing - I'll give you a hint: it
involves allocating the array of strings...

## Adding pre- and post-conditions

### Preconditions require things to be true

The first error might feel familiar to any C programmer who's ever passed a
signed integer to `malloc()`:

```bash
$ Dafny Fizzbuzz.dfy
...
Fizzbuzz.dfy(157,22): Error: array size might be negative
...
Dafny program verifier finished with 8 verified, 2 errors
```

Even though our program only calls `Fizzbuzz()` with a positive argument, Dafny
tells us that _there could exist a call to fizzbuzz with a negative argument_,
in which case instantiating the array will go awry.

We can solve this problem in two ways: one way would be to simply change the
argument type from `int` to `nat`, another built-in Dafny datatype.  In that
case, the typechecker would ensure that `i` will never be negative and the
error would disappear.  Let's fix this in a more general way, though: Let's add
a _precondition assertion_ to `Fizzbuzz()`: a precondition is a logical
statement (which you can think of as a boolean expression) that must be true
when the function is called:

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="nx">n</span> <span class="o">&gt;=</span> <span class="nx">0</span>         <span class="c1">// On entry, the caller of Fizzbuzz() needs to know that n is nonnegative
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="kc">new</span> <span class="nx">array</span><span class="p">[</span><span class="nx">n</span><span class="p">];</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


The `requires` keyword makes this a _precondition_. This states the caller of
`Fizzbuzz()` needs to be able to prove to Dafny that its argument is
nonnegative.  In our case, this is easy: in `Main()`, we simply assigned 100 to
a local variable and then passed it to `Fizzbuzz()`.  If we tried to, say, pass
-1 to it, the Dafny compiler would complain because that boolean expression
would no longer be true.

### Postconditions ensure that things are true

The second error is more subtle: Back in our `Main()` method, our while-loop
indexes into the array returned by `Fizzbuzz()` on the interval `[0, n)` (that
is, from 0 to but not including `n`).  The other error that Dafny gives us is:


```bash
$ Dafny Fizzbuzz.dfy
...
Fizzbuzz.dfy(170,16): Error: index out of range
...
Dafny program verifier finished with 8 verified, 2 errors
```

This isn't saying that the index is _necessarily_ out of range, but rather that
Dafny isn't sure how the length of the array relates to the loop variable.
Thinking about it a bit deeper: We've implicitly made an assumption with the
array that `Fizzbuzz()` returned: namely, that it's long enough for us to loop
over from `0` to `n`!  Think about all the times you've assumed something about
the length of an array only to find you were wrong!  Dafny won't let you make
that mistake here.

But it's not hard to stare at this code for a minute and convince ourselves
that the returned array is of length `n` and to conclude that, as before,
Dafny's not (yet!) smart enough to figure that fact out without some help from
us.  So, let's write a _postcondition assertion_ on `Fizzbuzz()` that states
that tells Dafny that whatever `n` we supply to `Fizzbuzz()` will correspond to
the output array's length.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="nx">n</span> <span class="o">&gt;=</span> <span class="nx">0</span>         <span class="c1">// On entry, the caller of Fizzbuzz() needs to know that n is nonnegative
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">ensures</span> <span class="nx">n</span> <span class="o">==</span> <span class="nx">ret</span><span class="p">.</span><span class="nx">Length</span> <span class="c1">// On return, Fizzbuzz() promises the caller that the length matches the input
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="kc">new</span> <span class="nx">array</span><span class="p">[</span><span class="nx">n</span><span class="p">];</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>

If we screwed up and returned, say, an array of length `n-1` or `n+1` or `42`
Dafny would notice and report a compilation error.  But with this
postcondition, Dafny now understands that accessing elements on `[0, n)` is
safe to do, and stops complaining to us.

If we were programming in Python, we could imagine doing these sorts of checks
at runtime through `assert` statements:

```python
$ python3 -q
>>> def Fizzbuzz(n: int) -> list[str]:
...     assert n >= 0, "we were given a negative input"
...     ret = [""] * n
...     assert len(ret) == n, "we would have returned a list of the wrong length"
...     return ret
...
>>>
```

Of course, in this case, we won't actually know until the program is running
that something went wrong.  It's far better to know beforehand than hope for
the best and wait for your program to crash in production!

We can start to see that Dafny is doing something similar but at compile-time:
we thread facts through our program using `requires` and `ensures` statements,
which it uses to prove to itself, and us, that there are no situations where
something _could_ go wrong.  

We also saw that just because something is "obviously true" to the programmer
doesn't mean it's obviously true to Dafny, so sometimes we need to "state the
obvious" to guide the compiler to understanding our intention.

## Converting our specification into pre- and post-conditions

Because the whole point of using Dafny is to ensure our `Fizzbuzz()`
implementation satisfies a specification, we need to convert our 
problem statement into Dafny.  Since our problem statement is all about facts
concerning the returned array (i.e. "if `j` satisfies some property then 
`ret[j]` will satisfy some other property"), it makes sense to use
postcondition assertions to express this.

Here's my first attempt at this: notice how similar this looks to our English
specification from above.  (`==>` is [logical
implication](https://en.wikiversity.org/wiki/Logical_implication), a boolean
operator like `||` or `&&` that you may not have seen in other programming
languages.) 

<div class="dafny-code">
<span class="line"><span class="cl"><span class="c1">// 1) If i is a multiple of 3 (but not of 5) then the `i`th element equals &#34;fizz&#34;;
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizz&#34;</span>
</span></span><span class="line"><span class="cl"><span class="c1">// This property ensures all integers i in the range of 0 to n for which i mod
</span></span></span><span class="line"><span class="cl"><span class="c1">// three is zero and i mod five is not zero, ret[i] shall be &#34;fizz&#34;
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl"><span class="c1">// 2) If i is a multiple of 5 (but not of 3) then the `i`th element equals &#34;buzz&#34;;
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;buzz&#34;</span>
</span></span><span class="line"><span class="cl"><span class="c1">// This property ensures all integers i in the range of 0 to n for which i mod
</span></span></span><span class="line"><span class="cl"><span class="c1">// five is zero and i mod three is not zero, ret[i] shall be &#34;buzz&#34;
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl"><span class="c1">// 3) If i is a multiple of 15 then the `i`th element equals &#34;fizzbuzz&#34;;
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span>              <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizzbuzz&#34;</span>
</span></span><span class="line"><span class="cl"><span class="c1">// This property ensures all integers i in the range of 0 to n for which i mod
</span></span></span><span class="line"><span class="cl"><span class="c1">// fifteen is zero, ret[i] shall be &#34;fizzbuzz&#34;
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span><span class="line"><span class="cl"><span class="c1">// 4) Otherwise, the `i`th element equals the string representation of `i`.
</span></span></span><span class="line"><span class="cl"><span class="c1">// TODO: Will Dafny complain about the expression `ret[i] == i`?
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="nx">i</span>
</span></span><span class="line"><span class="cl"><span class="c1">// This property ensures all integers i in the range of 0 to n for which i mod
</span></span></span><span class="line"><span class="cl"><span class="c1">// three and i mod 5 is zero, ret[i] shall be i
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>
</span></span>
</div>

Just like before, our specification will sit at the top of the `Fizzbuzz()`
function, just after the method signature.  There's an issue with the fourth
and final postcondition: The problem is, of course, that `str[i]` is a string
but `i` is an int.  The [Dafny standard
library](https://github.com/dafny-lang/libraries) is still a work in progress
and doesn't yet have a conversion method, so we'll have to eventually write
one.  For the moment, though, let's just put that on the back burner and only
treat parts 1-3 of our problem statement as our specification.  Let's take
stock of our `Fizzbuzz()` specification and "skeleton implementation", and 
see what Dafny tells us when we try to compile it:

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="nx">n</span> <span class="o">&gt;=</span> <span class="nx">0</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">n</span> <span class="o">==</span> <span class="nx">ret</span><span class="p">.</span><span class="nx">Length</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;buzz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span>              <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizzbuzz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="c1">//ensures forall i :: 0 &lt;= i &lt; n ==&gt; i % 3 != 0 &amp;&amp; i % 5 != 0 ==&gt; ret[i] == i // TODO
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="kc">new</span> <span class="kc">string</span><span class="p">[</span><span class="nx">n</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">    <span class="c1">//TODO: return a list of strings `ret` such that
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="c1">//our problem statement is satisfied...
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">}</span>
</span></span>
</div>


```bash
$ Dafny Fizzbuzz.dfy && dotnet Fizzbuzz.dll
Fizzbuzz.dfy(161,0): Error: A postcondition might not hold on this return path.
Fizzbuzz.dfy(157,8): Related location: This is the postcondition that might not hold.
Fizzbuzz.dfy(158,8): Related location: This is the postcondition that might not hold.
Fizzbuzz.dfy(159,8): Related location: This is the postcondition that might not hold.

Dafny program verifier finished with 10 verified, 3 errors
```

As you might expect, the three postconditions that Dafny can't prove the
correctness of are the three `ensures forall` postconditions we just added.
This of course makes sense: we haven't actually implemented the algorithm yet.
Just like how in test-driven development we'd expect our unit tests to
initially all fail, we similarly expect our specification to not match the
implementation.  And just like in the TDD model, we'll know when we've got
a working `Fizzbuzz()` solution: when Dafny verification begins to succeed!

## Loop invariants and our first implementation

Let's implement the core `Fizzbuzz()` logic.  Since Dafny's a straightforward
imperative programming language, we can implement it just like we would in Java
or C#.  There are many different possible implementations but I'm going to stick
with one that very closely resembles the specification: since the spec gives us
four distinct cases to handle, I'll have four distinct if/else statements.

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="nx">n</span> <span class="o">&gt;=</span> <span class="nx">0</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">n</span> <span class="o">==</span> <span class="nx">ret</span><span class="p">.</span><span class="nx">Length</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizz&#34;</span>      <span class="c1">// 1.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;buzz&#34;</span>      <span class="c1">// 2.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span>              <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizzbuzz&#34;</span>  <span class="c1">// 3.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="c1">//ensures forall i :: 0 &lt;= i &lt; n ==&gt; i % 3 != 0 &amp;&amp; i % 5 != 0 ==&gt; ret[i] == i         // 4.
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="kc">new</span> <span class="kc">string</span><span class="p">[</span><span class="nx">n</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">j</span> <span class="o">:=</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">j</span> <span class="o">&lt;</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;fizz&#34;</span><span class="p">;</span> <span class="c1">// Part 1. of the spec
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;buzz&#34;</span><span class="p">;</span> <span class="c1">// Part 2. of the spec
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;fizzbuzz&#34;</span><span class="p">;</span> <span class="c1">// Part 3. of the spec
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;TODO: convert j to a string&#34;</span><span class="p">;</span> <span class="c1">// Part 4. of the spec (not yet handled)
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="p">}</span>
</span></span><span class="line"><span class="cl">        <span class="nx">j</span> <span class="o">:=</span> <span class="nx">j</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


At this point we might think that Dafny will have nothing to complain about -
after all, as before, we can alternate staring deeply at the implementation and
staring deeply at the specification until we have convinced ourselves we did it right.
Each time through the loop, we modify the `j`th element in the array based on
our loop counter's value in a way that precisely matches what the spec tells
us.  All should be well.

However, Dafny complains with exactly the same errors as before: `A
postcondition might not hold`!  The reason is also the same as before: we
haven't told Dafny enough facts about our implementation for it to understand
_why_ our postconditions are true.  In general, loops are hard for automated
tools to reason about; in particular, it's hard for Dafny to know precisely how
many times a loop will be executed.  If Dafny doesn't know for sure then it can't
reason about actually got stored in the output array's elements.  Maybe the
loop skipped over some elements, or overwrote previously-written values!  We,
the humans, know that neither of those things happened, but we have to explain
that to Dafny.

To do so, we'll introduce a new kind of logical clause called a _loop
invariant_.  This is, like an `ensures` or `requires` clause, another logical
statement that must be true at the top of each loop iteration (i.e. before the
loop's guard condition, `j < n`, is checked).

What can we say about the values in the array when the loop's guard is true and
we (re-)enter the loop body?  Well, all the elements from 0 to `j` are filled
in with the right value from previous loop iterations.  For example, when `j ==
5`, we know that elements 0, 1, 2, 3, and 4 have their correct values.  And of
course, at the end of that iteration, so too will element 5, which sets us up
for the next time 'round when `j == 6`.


```
      0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
ret | x | x | x | x | x |   |   |   |   |   |   |   |   |   |   |   |
    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
    \------------------/^
      fizzbuzz values   |
       are filled in    j == 5: this element will be filled in by the
                                end of the current loop iteration...
```

And what can we say when we exit the loop body for the last time?  Well, `j ==
n`, so by a similar argument, all elements from 0 to `n` are filled in with
the right value, from previous loop iterations.  Hey, that's the entire array,
which is the thing we wanted!

```
      0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
ret | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x | x |
    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
    \--------------------------------------------------------------/^
                fizzbuzz values are filled in!                      |
                                                                    j == 16
```

So, our loop invariants will actually match very closely our postconditions:
instead of saying "for all elements indexed from 0 to _the size of the list_, the
following statements are true", we only have to say "the following statements
are true for all elements from _0 to our loop counter_": With one more
tiny assertion to remind Dafny that our loop counter will never exceed `n`, our
final specification and implementation looks as follows:

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl">    <span class="kc">requires</span> <span class="nx">n</span> <span class="o">&gt;=</span> <span class="nx">0</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="nx">n</span> <span class="o">==</span> <span class="nx">ret</span><span class="p">.</span><span class="nx">Length</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;buzz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">ensures</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">n</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span>              <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizzbuzz&#34;</span>
</span></span><span class="line"><span class="cl">    <span class="c1">//ensures forall i :: 0 &lt;= i &lt; n ==&gt; i % 3 != 0 &amp;&amp; i % 5 != 0 ==&gt; ret[i] == i
</span></span></span><span class="line"><span class="cl"><span class="c1"></span><span class="p">{</span>
</span></span><span class="line"><span class="cl">    <span class="nx">ret</span> <span class="o">:=</span> <span class="kc">new</span> <span class="kc">string</span><span class="p">[</span><span class="nx">n</span><span class="p">];</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">j</span> <span class="o">:=</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">j</span> <span class="o">&lt;</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">j</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">n</span> <span class="c1">// Another one of those &#34;obvious&#34; facts that Dafny needs to be told explicitly
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>        <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizz&#34;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;buzz&#34;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span>              <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizzbuzz&#34;</span>
</span></span><span class="line"><span class="cl">        <span class="c1">//invariant forall i :: 0 &lt;= i &lt; n ==&gt; i % 3 != 0 &amp;&amp; i % 5 != 0 ==&gt; ret[i] == i
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;fizz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;buzz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;fizzbuzz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;TODO: convert j to a string&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">        <span class="nx">j</span> <span class="o">:=</span> <span class="nx">j</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span><span class="line"><span class="cl"><span class="p">}</span>
</span></span>
</div>


This is enough for Dafny to be convinced that our postconditions are satisfied:
after the final loop iteration, `j == n`, which perfectly matches our actual
specification!  We have, at long last, an implementation that Dafny has proven
satisfies our specification, and so we're able to generate executable code
from our program!

```bash
$ Dafny Fizzbuzz.dfy

Dafny program verifier finished with 11 verified, 0 errors
Compiled assembly into Fizzbuzz.dll
$
```

## What if we'd gotten the implementation wrong?

I've never been a good test-taker and one of my favourite things about grad
school is that, generally, the only classes that would make me write exams
are the ones I wouldn't want to take anyway.  Let's imagine my nerves had
gotten the better of me and that I'd made a silly mistake in my implementation:
here's a mistake I make figuratively-literally every time I write a
`while`-loop: I simply forget to bump the loop counter so my program hangs
forever.  If I take out that `j := j + 1` statement and recompile, Dafny tells
us that it isn't sure that our loop will ever actually terminate:

```bash
$ Dafny Fizzbuzz.dfy
Fizzbuzz.dfy(165,4): Error: cannot prove termination; try supplying a decreases clause for the loop
Dafny program verifier finished with 10 verified, 1 error
$
```

A `decreases` clause helps Dafny understand how, at each iteration of the
loop, the loop counter is getting "closer" to the loop's termination condition.
For us, our clause would be `decreases n - j`, since at each iteration that
expression becomes smaller (since `j` becomes bigger!), and the loop never
iterates when `n - j <= 0`.  Dafny has become good enough at infering this
clause out for simple loops that we usually don't need to state it explicitly.
In this case, the problem isn't that we've not explained to Dafny why our loop
eventually terminates - we wrote the loop wrong and it doesn't!

Already we can see that Dafny is checking more powerful program properties than
our business logic: it will complain if it isn't convinced that our program
will ultimately terminate!  (And, no, this doesn't circumvent the Halting
Problem: deciding termination in general-purpose programming languages is [an
area of active
research](https://swt.informatik.uni-freiburg.de/berit/papers/termination-proofs....pdf).)

### Counterexample generation

Let's introduce a more annoying bug.  imagine that I'd written the following
loop body instead - can you spot the error?  

<div class="dafny-code">
<span class="line"><span class="cl"><span class="kc">method</span> <span class="nx">Fizzbuzz</span><span class="p">(</span><span class="nx">n</span><span class="p">:</span> <span class="kc">int</span><span class="p">)</span> <span class="kc">returns</span> <span class="p">(</span><span class="nx">ret</span><span class="p">:</span> <span class="nx">array</span><span class="o">&lt;</span><span class="kc">string</span><span class="o">&gt;</span><span class="p">)</span>
</span></span><span class="line"><span class="cl"><span class="p">...</span>
</span></span><span class="line"><span class="cl">    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;fizz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;buzz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;fizzbuzz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;TODO: convert j to a string&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">        <span class="nx">j</span> <span class="o">:=</span> <span class="nx">j</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span>
</div>

Here I simply flipped the conditions where "fizz" should be appended versus
"buzz".  Could you honestly say you might not make the same mistake in a job
interview?  If you were interviewing me and I wrote this out, would you even
notice?

This is one of the reasons why Fizzbuzz is a terrible interview question: it's
super easy to invert a silly conditional, and if your interviewer is sharp-eyed
and in a mean mood that day, you might get written up for it.  Dafny catches
this for us, though, and tells us that loop invariants 1 and 2 are no longer
satisfied:

```bash
$ Dafny Fizzbuzz.dfy
Fizzbuzz.dfy(92,14): Error: This loop invariant might not be maintained by the loop.
Fizzbuzz.dfy(92,14): Related message: loop invariant violation
Fizzbuzz.dfy(93,14): Error: This loop invariant might not be maintained by the loop.
Fizzbuzz.dfy(93,14): Related message: loop invariant violation
Dafny program verifier finished with 10 verified, 2 errors
$
```

We can even do one better: Dafny can _show us potential values_ that violate
the invariant!  By adding the `/extractCounterexample` flag (or, if you're
using the Visual Studio Code plugin, directly in your editor), you can ask
Dafny to give us a specific _counterexample_ that violates the specification.
It's definitely easier to understand in an IDE, but here's the relevant 
output on the command-line:

```bash
...
Counterexample for first failing assertion:
Fizzbuzz.dfy(84,0): initial state:
        n : int = 6
        ret : ? = ()
...
Fizzbuzz.dfy(88,4): after some loop iterations:
Fizzbuzz.dfy(106,18):
        n : int = 6
        @1 : seq<char> = ['f', 'i', 'z', 'z']
        ret : _System.array?<seq<char>> = (Length := 6, [5] := @1) 
```

In this example, Dafny's underlying solver has found a code path where
`Fizzbuzz()` is called with `n == 6`; at some point during program execution,
index 5 of our `ret` array holds the string "fizz" (which the prover assigned
to a temporary variable named `@1`; however, since 5 is divisible by 5, this
violates the specification's requirement that it be equal to "buzz"!

Remember: at no point did our implementation ever actually execute: Dafny found
this counterexample _symbolically_, by exploring the space of program executions
and validating that whatever values are assigned to `ret` match our invariants
and postconditions.

## A verifiable "optimisation"

When I was asked to implement Fizzbuzz on the whiteboard the interviewer
followed up with, "...and how could we make this more _efficient_?".  After
some frustrating back-and-forth about what that could _possibly_ mean, it turns
out they were slightly unhappy with the number of branches in my conditional
and wanted me to reduce the number of `else if`s in my solution.  That this
company was the darling of my regional tech scene and that they thought this
would "make fizzbuzz run faster" did not inspire much confidence in me!

Anyway, sigh, fine, with a bit of refactoring this isn't difficult to do: we'll
have a mutable string variable to build up "fizz", "fizzbuzz", or "buzz"
incrementally.  It might not be faster to execute, or easier to read, but at least
the garbage collector will get more of a workout when it runs!

The body of our loop now looks like this:

<div class="dafny-code">
<span class="line"><span class="cl">    <span class="kc">var</span> <span class="nx">j</span> <span class="o">:=</span> <span class="nx">0</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="kc">while</span> <span class="nx">j</span> <span class="o">&lt;</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">j</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">n</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizz&#34;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">!=</span> <span class="nx">0</span> <span class="o">&amp;&amp;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;buzz&#34;</span>
</span></span><span class="line"><span class="cl">        <span class="kc">invariant</span> <span class="kc">forall</span> <span class="nx">i</span> <span class="p">::</span> <span class="nx">0</span> <span class="o">&lt;</span><span class="p">=</span> <span class="nx">i</span> <span class="o">&lt;</span> <span class="nx">j</span> <span class="o">==&gt;</span> <span class="nx">i</span> <span class="o">%</span> <span class="nx">15</span> <span class="o">==</span> <span class="nx">0</span>              <span class="o">==&gt;</span> <span class="nx">ret</span><span class="p">[</span><span class="nx">i</span><span class="p">]</span> <span class="o">==</span> <span class="s2">&#34;fizzbuzz&#34;</span>
</span></span><span class="line"><span class="cl">        <span class="c1">//invariant forall i :: 0 &lt;= i &lt; n ==&gt; i % 3 != 0 &amp;&amp; i % 5 != 0 ==&gt; ret[i] == i
</span></span></span><span class="line"><span class="cl"><span class="c1"></span>    <span class="p">{</span>
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">curr</span> <span class="p">:</span> <span class="kc">string</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="nx">curr</span> <span class="o">:=</span> <span class="s2">&#34;&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="kc">var</span> <span class="nx">curr_modified</span> <span class="p">:</span> <span class="nx">bool</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="nx">curr_modified</span> <span class="o">:=</span> <span class="kc">false</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">3</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">curr</span> <span class="o">:=</span> <span class="nx">curr</span> <span class="o">+</span> <span class="s2">&#34;fizz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">            <span class="nx">curr_modified</span> <span class="o">:=</span> <span class="kc">true</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="nx">j</span> <span class="o">%</span> <span class="nx">5</span> <span class="o">==</span> <span class="nx">0</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">curr</span> <span class="o">:=</span> <span class="nx">curr</span> <span class="o">+</span> <span class="s2">&#34;buzz&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">            <span class="nx">curr_modified</span> <span class="o">:=</span> <span class="kc">true</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="kc">if</span> <span class="nx">curr_modified</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="nx">curr</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span> <span class="kc">else</span> <span class="p">{</span>
</span></span><span class="line"><span class="cl">            <span class="nx">ret</span><span class="p">[</span><span class="nx">j</span><span class="p">]</span> <span class="o">:=</span> <span class="s2">&#34;TODO: convert j to a string&#34;</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">        <span class="p">}</span>
</span></span><span class="line"><span class="cl">
</span></span><span class="line"><span class="cl">        <span class="nx">j</span> <span class="o">:=</span> <span class="nx">j</span> <span class="o">+</span> <span class="nx">1</span><span class="p">;</span>
</span></span><span class="line"><span class="cl">    <span class="p">}</span>
</span></span>
</div>

Here, our implementation really no longer looks like our specification.  To
mutably build the string when j is divisible by 3 and/or 5 means we never
explicitly check divisibility by 15.  Also, we created a new `curr_modified`
piece of state, but our spec says nothing about it existing.  This sort of code
refactoring is always a dangerous process - there's always a chance that your
modifications actually changed the program semantics, and if your test suite
isn't comprehensive then maybe you've introduced a bug.  

The good news is that Dafny can still prove that this gnarlier implementation
satisfies our existing set of straightforward postconditions and loop
invariants!  And if we got it wrong -- say, if I wrote `else if j % 5 == 0` or
swapped the order that the two modulus checks execute -- then the compiler
would tell us that we broke our solution and we could ask it for a
counterexample!

## The home stretch...or are we?

We never actually ran the executable that Dafny proved correct for us, so why
don't we do that now?  Dafny, by default, generates .NET assemblies but can
also _extract_ to Java .class files and even Golang code, which is pretty neat.
But despite being nominally "verified", the output isn't quite what we want:

```bash
$ dotnet Fizzbuzz.dll | head -n 20
fizzbuzz
TODO: convert j to a string
TODO: convert j to a string
fizz
TODO: convert j to a string
buzz
fizz
TODO: convert j to a string
TODO: convert j to a string
fizz
buzz
TODO: convert j to a string
fizz
TODO: convert j to a string
TODO: convert j to a string
fizzbuzz
TODO: convert j to a string
TODO: convert j to a string
fizz
TODO: convert j to a string
$
```

This is because our implementation isn't complete!  We still need a way of
converting our loop counter into a string, remember?  And because our
specification is not complete, either - remember that we commented out the
final postcondition - Dafny had no way of knowing that our implementation is
wrong.  It's important to remember that software verification isn't a panacea;
if our specification can't be trusted to validate the right thing, [we have no
business assuming that it means anything that our implementation conforms to
that specification](https://www.cs.umd.edu/~gasarch/BLOGPAPERS/social.pdf).

Don't worry, though, we'll close the loop on this gimmick by completing
`Fizzbuzz()` [in the next
post](/posts/proving-the-coding-interview-2/), where we'll have to
implement a (verified!) helper method to convert a natural number to a string.
Hey, that's not a bad interview question in its own right!!

## Your turn - modify the spec

Eagle-eyed readers may notice that our specification of fizzbuzz slightly
deviates from the standard one: typically, `Fizzbuzz(n)` iterates on `[1, n]`,
so the beginning lines read "1", "2", "fizz", and so on.  We instead iterate
from `[0, n)`, so our final implementation will begin with "fizzbuzz", "1",
"2", ...  Why not try installing Dafny (there's a good installation guide
[here](https://www.cs.utexas.edu/~bornholt/courses/cs395t-22sp/homework/hw4/))
and try your hand at changing first the specification, then the implementation?
If you do, [let me know how it went for you](https://twitter.com/ntalyour).

## Thanks

Thanks to
[Scott Andreas](https://twitter.com/cscotta/),
[Rustan Leino](http://leino.science),
[Brian Lin](https://twitter.com/linteriscoming),
[Kelly Shortridge](https://twitter.com/swagitda_),
Paul Vanetti,
and
[Leif Walsh](https://twitter.com/leifwalsh)
for their feedback on early drafts of this post!


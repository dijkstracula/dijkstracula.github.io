---
layout: post.njk
title: "FRP in Lean: Intermezzo: fully quantified luxury dependent signals"
date: 2026-07-30
tags: [post, lean, reactive-programming, frp]
excerpt: "Squaring the circle to support every LTL connective in an FRP type"
series: lean-ltl
inlineCodeLang: lean4
series_title: "Intermezzo: Signals with quantifiers"
draft: true
---

<script src="/js/frp/runtime.js"></script>

## Welcome back!

Last time we implemented a series of combinators that transformed not just data
values that might flow through a functional reactive program, but invariants
about that data.  We introduced a _signal of refinements_, where at each time step
we bundle the signal's value with a local proof that that timestep-dependent
value maintains a given property:

{% lean "Examples/Ltl7.lean", "rsignal-review-sig-of-refinements" %}

We also saw _refined signals_, where instead of each time step producing a
pair, the signal itself is a pair of a signal and a _global_ safety property,
asserting the property is true at all time steps:

{% lean "Examples/Ltl7.lean", "rsignal-review-refined-sig" %}

Lastly, we saw that `RSignal.split` and `RSignal.collect` were the bridges
between these two worlds: `split` shards a refined signal into a signal of
refinements, and `collect` goes the other way.

{% lean "Examples/Ltl7.lean", "rsignal-review-split-collect" %}

## Refined signals are _quantified_ signals

::: margin-note
Conversely, `Signal.split` _instantiates_ a local proof by supplying the
quantified proof with whatever `t` timestep we're currently at.
:::
A logical proposition with a quantifier is shaped like "for all ..." or "there
exists ...".  Since a safety property covers every timestep, we'd expect a `∀`
symbol somewhere, and indeed if we unfold the definition of an `RSignal` and
`LTL.always`, that's what we get:

{% lean "LtlFrp/FRP/Verified.lean", "rsignal-simplified" %}
{% lean "LtlFrp/LTL.lean", "always" %}

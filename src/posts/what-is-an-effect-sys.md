---
layout: post.njk
title: "But what is an effect system, really?"
date: 2026-02-05T00:00:00-05:00
tags: [post, ocaml, effects]
draft: true
excerpt: "I'm not smart enough to read a POPL paper, but I might be smart enough to read some C"
---

At my day job, we've spent the last few months migrating our legacy OCaml
codebase to use Multicore OCaml, and with it came us starting to use new
libraries like [Eio](https://github.com/ocaml-multicore/eio) that take
advantage of OCaml 5's new effect system.

Lots of my coworkers were super jazzed about being able to use effects in our
codebase, but, out of ignorance, I wasn't really sharing their enthusiasm. When
it comes to technological choices I skew naturally conservative - unless I see
a clear and obvious benefit to the new and shiny thing, I'll stick with the
trusted and true thing instead, thank you very much.  But, that doesn't mean I
should be let off the hook from understanding the new and shiny thing!

So, "but what is an effect system, really", I'd cry (into a search engine box).
Half of the Stack Overflow posts I saw talked about effects being "a better,
more composable monad", which might be reasonable: the _effect_ of using
effects seem to be _kind of_ like the _effect_ of programming monadically,
since the canonical examples people seem to keep bringing up for both are for IO,
non-determinism, mutating state, and so on.  The problem is that when I needed
to program monadically at my first job, I ignored the cutsy burrito metaphors
and [read the
source](https://github.com/twitter/util/blob/develop/util-core/src/main/scala/com/twitter/util/Future.scala).
If effects are a feature of the _language_ it's a lot harder to open the
standard library and stare at the important datatypes.

(This also means that it's hard to reason about its performance, if it
criss-crosses the compiler, the runtime, the standard library, and finally user
code.  It's a bit like how the best wisdom we have for the performance of
exceptions is "they're slow" or "they're normally slow, but ours are
uncharacteristically fast".  By contrast, after looking at how `Monad[T]` in
Scala works, say, I shouldn't be surprised that stack traces deep inside
monadic code are all but useless.)

The other half of those posts talked about how effects are a natural
progression of exceptions, generators, and continuations.  Well, I certainly
know how exceptions work, I like to use `yield` in Python, and I _kind of_
remember how continuations work, but it's far less clear to me how those things
connect to the classic problems that monads solve.  

::: margin-note
I attended POPL one year and spent most sessions sitting at the back of the
hall, befuddled.  I'd just as soon avoid that feeling again, all things being
equal!  Feel free to insert your own _Nazaré Confusa_ variation here.
:::
There's clearly something interesting about effect systems in here that I haven't
yet grasped, but I also know I'm not going to get anywhere with the fundamental
research papers in the space - show me a page of operational semantics notation
and my eyes glaze over.  Not to say there's no value in POPL papers, just that
as a practitioner I'm not the right audience for them.

What I'm more comfortable with is popping the hood and seeing how a mechanism
works.  I did that 15 years ago with `com.twitter.util`'s `Future[T]`, so why
not do the same with OCaml's effects system?

In this post, we're going to do just that:  We'll read some runtime code, maybe
set a breakpoint or two, and see what falls out.

# Warmup: but what is an exception?

I think it's instructive to ground ourselves with a language feature that
everyone knows, first.

Here's a silly program that implements a "truncation-safe" division by two.
The point is just to have a trivial program that might throw an exception:

```ocaml
type exn += WasOdd of int

let div2 n = if n mod 2 = 0 then n lsr 1 else raise (WasOdd n)

let () =
  Printexc.record_backtrace true;
  Printexc.register_printer (fun e -> match e with
    | WasOdd(n) -> Some (sprintf "div2 would have truncated %d" n)
    | _ -> None
  );

  Printf.printf "div2 42 = %d\n\n" (div2 42);
  Printf.printf "div2 41 = %d\n\n" (div2 41)
```

::: warning
```
$ ocamlc -g foo.ml && ./a.out
div2 42 = 21

Fatal error: exception Foo.WasOdd(41)
Raised at Foo.div2 in file "foo.ml", line 3, characters 46-62
Called from Foo in file "foo.ml", line 9, characters 33-42
```
:::

Nothing unexpected here.  But what's the path that we take from kicking
off the compiler to generating a binary, and running the binary that 
leads to this output?

## The view from the typechecker: `WasOdd` is a variant of `exn`

Usually, OCaml programmers would write the first line `exception WasOdd of int`
but I intentionally desugared it here.  The `+=` operator has nothing to do
with addition: since `exn` is an [extensible
variant](https://ocaml.org/manual/5.4/extensiblevariants.html), we can add
new constructors to this datatype, and then later on _pattern match_ on that
newly-added constructor whenever we're operating on an exception (as we do
inside the exception printer).

### 

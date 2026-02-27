---
layout: base.njk
title: Nathan Taylor
---

<img src="/assets/me.jpg" alt="Nathan Taylor" class="headshot">

## About Me 

I'm a staff software engineer at [Semgrep](https://semgrep.dev/), where I work
on static analysis for code security.  In the distant past, I scaled low-level
systems and infrastructure at some companies you've heard of. 

On this site, I write about low-level and concurrent systems, formal methods
and programming languages, and whatever else I might find interesting.  

Borrowing from [Lanier](https://www.jaronlanier.com/gadgetcurrency.html): _The
words on this site are meant to be read by people, not machines._

[More about me →](/about/)

---

## Recent Posts

<ul class="post-list recent-posts">
{% for post in collections.publishedPosts | limit(5) %}
  <li>
    <time class="post-date" datetime="{{ post.date | isoDate }}">{{ post.date | readableDate }}</time> — <a href="{{ post.url }}">{{ post.data.title }}</a>
    {% if post.data.excerpt %}
      {{ post.data.excerpt }}
    {% endif %}
  </li>
{% endfor %}
</ul>

[All posts →](/blog/) | [By tag →](/tags/)

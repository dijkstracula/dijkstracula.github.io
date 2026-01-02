---
layout: base.njk
title: Nathan Taylor
---

## About Me 

I'm a staff software engineer at [Semgrep](https://semgrep.dev/), where I work
on static analysis for code security.  Prior to joining Semgrep, I was a PhD
student at UT Austin, where I worked on applying formal methods to concurrent
and distributed systems.  In the distant past, I was lucky enough to live in
beautiful [Oakland, CA](https://localwiki.org/oakland/), where I scaled
low-level systems and infrastructure at some companies you've heard of. Outside
of industry, I was a contract developer at [Microsoft
Research](https://web.archive.org/web/20250320000332/https://www.microsoft.com/en-us/research/theme/ai-for-systems/)
and a computer science instructor at [Macewan
University](https://www.macewan.ca/academics/academic-departments/computer-science/)
and the [University of Toronto](https://web.cs.toronto.edu/).

On this site, I write about systems programming, formal methods and programming
languages, and whatever else I might find interesting.  Borrowing from
[Lanier](https://www.jaronlanier.com/gadgetcurrency.html): _The words on this
site are meant to be read by people, not machines._

[More about me →](/about/)


---

## Recent Posts

<ul class="post-list recent-posts">
{% for post in collections.publishedPosts | limit(5) %}
  <li>
    <time class="post-date" datetime="{{ post.date | isoDate }}">{{ post.date | readableDate }}</time> — <a href="{{ post.url }}">{{ post.data.title }}</a>
  </li>
{% endfor %}
</ul>

[All posts →](/blog/)

Kaplan & Tarjan katas
=====================

Kaplan and Tarjan wrote a series of article on efficient purely
functional and immutable data structures.

- [*Persistent lists with catenation via recursive slow-down*](http://portal.acm.org/citation.cfm?doid=225058.225090), Kaplan & Tarjan (1995)
- [*Purely functional, real-time deques with catenation*](http://portal.acm.org/citation.cfm?doid=324133.324139), Kaplan & Tarjan (1999)
- [*Simple Confluently Persistent Catenable Lists*], Kaplan, Okasaki & Tarjan (2000)

These articles are notoriously hard to read, and supporting
implementation are not provided. This repository is an attempt at
providing reference implementation for the data structure these
articles introduce.

### Licence ###

The files in this repository are distributed under the Creative Commons licence [cc by 4.0](http://creativecommons.org/licenses/by/4.0/).


Coding style
------------

The goal of this repository is entirely pedagogical. Therefore, the
implementation does not aim for maximal efficiency. The code is amply
documented and the reader is encouraged to signal any piece of unclear
documentation so that the quality of the presentation can be improved.

As much as possible, invariants are enforced by typing. This both act
as a form of documentation and as an invitation to play with the code
to get a deeper understanding of the data structures.

The language chosen for this demonstration is the
[Ocaml](http://ocaml.org/) language. A flexible functional language in
which purely functional programming, both strict and lazy, and
assignements are easy and convenient to use. All three are used in
Kaplan & Tarjan's data structures.

I am still in the process of figuring out most of these data
structures myself, so this is still very much work in progress.


Organisation
------------

Each article corresponds to one directory, each data structure is
implemented in a dedicated file. The files are independent.

- The `simple` directory contains implementations for the 2000 article.

# Global transition system for the half-quotient routing code

Date: 2026-08-24

Owner: codex-sol-3

Scope: `BinarySizeTwoCyclicPackingBound`; `GAP A-REG-NONBIP`

## Purpose

The first half-quotient pairing invariant is block-local.  Reciprocity does
not carry one whole folded block to another: it scatters its darts among many
target blocks.  This note records a global object in which the scattering
disappears.  It is a transition system on the *undirected routing edges*, so
reciprocal darts are identified before any paths are followed.

The construction is exact and q-generic.  The proposed obstruction is not
yet proved: the missing step is to translate the same-fiber common-neighbor
cap into a rank or circuit restriction in this transition system.

## Construction before cancellation

Let a routing dart in the block `(x,t)` have relative row and column
coordinates `(r,p)`.  Reciprocity identifies it with the reverse dart in its
target block.  Write `[x,t,r,p]` for this reciprocal pair.  These reciprocal
pairs are the **central vertices** of the global transition graph.

It is important here to retain the two lifts separately.  Do not first cancel
coincident cells modulo two.  In a fixed block `(x,t)`, attach the central
vertex `[x,t,r,p]` to the two local coordinate nodes

```text
((x,t), R, r mod m),     ((x,t), C, p mod m),   q = 2m.
```

Every non-hole row residue has exactly two incident darts, one for each of
its two lifts.  Each row-hole residue has exactly one.  The same holds for
columns.  Consequently every local coordinate node has degree two except
the four boundary nodes

```text
R_(t mod m), R_((t+1) mod m), C_0, C_(-1),
```

which have degree one.  Suppressing the degree-two coordinate nodes gives a
canonical pairing of central-vertex incidences.  The degree-one nodes leave
four dangling incidences in each block.

A central vertex comes from one undirected routing edge and is seen from its
two endpoint blocks.  It has a row and a column incidence at each endpoint,
hence four incidences in total.  After choosing a pairing of the four dangling
incidences in every block, every central vertex has degree four.  The result
is a canonical 4-regular multigraph equipped with a transition system.
Parallel transition edges are intentional: when two lifted routes occupy the
same folded cell, the row and column coordinate nodes pair the same two
central vertices separately.  Cancelling that cell over `F_2` would erase
precisely this lifted information.

## Relation to the block-local pairing

Inside one block, alternate through central vertices and the suppressed row
or column coordinate nodes.  Before boundary completion this yields the two
boundary paths and the cycles classified in
`SIZE_TWO_CYCLIC_HALF_QUOTIENT_PAIRING_PROBE.md`.  Their three-valued endpoint
pairing is therefore the connectivity induced by the internal transitions.

The new point is that a central vertex is shared by the two reciprocal block
views.  Following a transition through that vertex moves between the two
views without reconstructing a scattered reverse path.  Reverse-fragment
matching is literal adjacency in the global graph rather than an additional
coherence assertion.

There are three possible completions of the four boundary incidences in each
block.  Completing by the block's induced pairing closes its two boundary
paths separately; either other completion splices them.  Thus local pairing
data becomes a choice of vertex state in the standard circuit-partition
language.

## Literature interface

For a 4-regular graph with an Euler system, the extended Cohn--Lempel equality
expresses the number of circuits in a circuit partition as the nullity over
`F_2` of a modified interlacement matrix (up to the component correction).
No canonical Euler system is required: choose one Euler circuit in every
connected component.  Relative to this choice, each circuit-partition
transition has one of three exact matrix operations: delete its row and
column if it follows the Euler circuit, retain them unchanged for the other
orientation-consistent transition, or retain them and flip the diagonal for
the orientation-inconsistent transition.  Traldi's Theorem 4 states

```text
number of partition circuits = nullity(I_P) + components(G).
```

The transition-matroid formulation packages the three local transitions at
each 4-valent vertex, while the touch-graph formulation identifies the
resulting nullspace with a cycle space.  Useful primary references are:

- Lorenzo Traldi, *Binary nullity, Euler circuits and interlace polynomials*,
  arXiv:0903.4405, Theorem 4.
- Lorenzo Traldi, *The transition matroid of a 4-regular graph: an
  introduction*, arXiv:1307.8097.
- Lorenzo Traldi, *Circuit partitions and signed interlacement in 4-regular
  graphs*, arXiv:1607.04233.
- Richard Arratia, Bela Bollobas, and Gregory Sorkin, *The Interlace
  Polynomial of a Graph*, arXiv:math/0209045.

These results do not themselves give the Erdős-85 contradiction.  They give
the correct linear-algebraic consumer once the routing cap is stated as a
transition restriction.

The 4-valent vertices in this application are reciprocal dart pairs, not
folded cells.  Uncancelled folded coordinate nodes supply the transitions
between them.  This distinction is essential: a coincident folded cell gives
parallel row and column transitions, whereas mod-two cancellation would erase
both and destroy the four-valent graph before the theorem can be applied.

## Candidate chain to `A-REG-NONBIP`

The intended chain is:

```text
two-hole routing + reciprocity
  -> global 4-regular transition system                 [construction above]
  -> same-fiber cap forbids a specified transition minor [GAP GT1]
  -> cap restriction stated as allowed matrix operations [GAP GT1b]
  -> interlacement/touch-graph nullity forces a violation [GAP GT2]
  -> contradiction for q = 2^k                           [GAP GT3]
  -> BinarySizeTwoCyclicPackingBound
  -> A-REG-NONBIP size-two branch
```

`GT1` is the next bounded target.  A useful executable probe must retain the
uncancelled lifted routes, build central vertices by reciprocal dart pairs,
and report which short circuits or transition minors are changed by enabling
one same-fiber cap.  Merely recounting the already-cancelled block pairing or
its voltage cannot test `GT1`.

## Falsification criteria

Stop this mechanism if either of the following occurs in q=8 controls:

1. every candidate transition minor forbidden by the half-fiber cap is also
   absent in a relaxed SAT model; or
2. the interlacement nullity and touch-graph cycle rank vary freely among
   relaxed models with the same cap interface.

Conversely, a q=8 separation is only evidence.  Progress toward the outline
requires a q-generic statement of `GT1` or `GT2`, not a finite certificate.

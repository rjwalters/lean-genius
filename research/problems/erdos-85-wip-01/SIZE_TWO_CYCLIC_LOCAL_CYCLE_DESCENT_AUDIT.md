# Local column-cycle descent audit

Node: cap-preserving defect-rank descent beneath
`BinarySizeTwoCyclicPackingBound`.

## Local move

In the permutation normal form, a source `(x,t)` carries a bijection

```text
psi : R -> R,                 R=Z/q\{0,1},
u(r) = -t-r-psi(r).
```

Its defect rank is the number of allowed colours omitted by `u`.  Permuting
the values of `psi` on a set of row labels preserves both local exact
projections automatically: rows are unchanged and the column labels remain
the same set `R`.  The move is locally valid when all new colours are allowed
and no new dart is a loop.

A one-occurrence sharp repair cannot have this property: changing a single
column label destroys the column permutation.  The first possible physical
local move is therefore a transposition of two `psi` values, followed if
necessary by a longer column cycle.

## Complete q8 census

`size_two_cyclic_local_cycle_descent_census.py` exhausts all `6!` local
permutations for every allowed source fibre and all four unordered hole
placements.  For every locally valid permutation above minimum defect rank,
it first searches all column transpositions and then both orientations of
every three-cycle.

Result: **every q8 nonminimum local matching strictly descends by a cycle of
length at most three**, while preserving row hits, column hits, allowed
target fibres, and looplessness.

Transpositions alone are not sufficient.  The numbers requiring a genuine
three-cycle, listed by allowed source fibre, are

```text
a=0: t 1,2,3,4,5,6 -> 7,0,8,8,0,7
a=1: t 0,2,3,4,5,7 -> 3,3,4,4,3,3
a=2: t 0,1,3,4,6,7 -> 2,4,0,0,4,2
a=3: t 0,1,2,5,6,7 -> 10,0,11,11,0,10
```

There are no cases stuck after three-cycles.  The checker recomputes the
local minimum rather than assuming it, and prints the full nonminimum count
for each fibre.

## Nonbinary control

The same exhaustive checker at q10, a1 cuts any arbitrary-even
generalization.  Fibres 2 and 7 each have 108 nonminimum matchings stuck
after every two- and three-cycle; fibres 4 and 5 each have eight.  Moreover
the local minimum is zero in fibres 2 and 7, because the `4|q` odd weighted-
moment obstruction is absent.

Thus “three-cycles always suffice” is only established at q8 and should be
investigated as a binary/2-adic statement, not stated for all even orders.
The q10 failure is a mandatory control for any proposed proof that does not
use the power-of-two hypothesis.

## What this proves and what it does not

This is positive evidence for a q-generic local assignment lemma: a
nonminimal punctured matching may admit a short alternating-cycle move that
reduces diagonal-colour deficiency.  It also gives the correct move size for
future SAT/core searches; a transposition-only switch theorem is false even
at q8.

The move is **not** yet a code descent.  Changing a dart at one source must
be mirrored at its target by reciprocity.  That propagated change may break
the target's local permutation or create a repeated same-fibre owner pair.
Thus the remaining theorem has two separate parts:

1. prove a local column-cycle descent (possibly with length beyond three) at
   general binary `q`; and
2. lift a collection of those cycles through shifted-base reciprocity while
   preserving every cap.

The first part is no longer speculative at q8.  The second is exactly where
the reflection-orbit cap obstruction and global closure must enter.

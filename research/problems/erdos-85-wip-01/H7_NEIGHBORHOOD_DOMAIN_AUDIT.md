# H7 neighborhood-domain exact-cover probe

Date: 2026-08-26

The divergence-round proposal was to replace 861 independent low-edge bits by
one choice of a complete low-neighborhood row for each of the 42 low vertices.
Every candidate row is generated only if it simultaneously satisfies:

* the exact residual degree `7-|support(x)|`;
* `BC=J`, equivalently its selected neighbors' high supports partition all
  seven labels exactly once;
* the pinned empty-empty edges when `x` is an empty-support vertex.

The probe then performs one exact forward-check layer: after selecting a root
row, every other row is filtered by adjacency symmetry and by the full C4
common-neighbor cap, including fixed common high neighbors.

## F6/t2 result

The exact row-domain counts are:

```text
empty rows:    210, 210, 840, 672, 672, 672, 672
singleton:     9147 each (14 rows)
pair:          2020 each (21 rows)
total choices: 174426
```

The unconstrained product of row-domain sizes is approximately `10^143.75`.
The smallest root has 210 choices.  Every one of those 210 choices survives
the exact one-row forward check; by residual symmetry they leave the same
domain-size product.  The best/median remaining product is approximately
`10^130.86`, with 96,278 surviving row choices in total and individual
remaining domains ranging from 128 to 4,954.

Thus the row formulation compresses the raw `2^861` edge cube, but it does not
produce early exact-cover propagation.  A one-hot CNF would introduce 174,426
choice variables before compatibility clauses—larger than either reviewed H7
encoding—and pairwise row compatibility would be enormous.

## Verdict

The naive neighborhood one-hot/exact-cover formulation is **cut**.  It
repackages rather than removes the hard global symmetry/C4 coupling.  Do not
build its full compatibility CNF or a DLX search from these domains alone.

The reusable artifact is `sat49/probe_h7_neighborhood_domains.py`, which gives
an exact row-domain inventory and bounded forward-check metric for any of the
43 masks.  A future row-based mechanism should proceed only if it supplies an
additional global invariant that reduces the 9,147-element singleton domains
before search (for example, a proven orbit canonicalization or a new spectral
row signature).


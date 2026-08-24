# Characteristic-two quotient audit

This audits divergence round 15's alternating-rank candidate against the
actual no-empty `SizeTwoCyclicSameDifferenceCode` interface.  It records a
clean invariant quotient, but cuts the proposed parity contradiction.

Let `q=2^k`, `d=q-2`, and reduce the reciprocal adjacency matrix `K` modulo
two.  For every absolute row `y`, let `r_y` be its indicator.  For every
absolute column `y` (the coordinate `x+t`), let `c_y` be its indicator.
The exact-hit equations give, independently of the particular code,

```
K r_y = 1 + c_y + c_(y-1),
K c_y = 1 + r_y + r_(y+1),
K 1   = d 1 = 0.                                          (1)
```

(Indices are cyclic; reversing both displayed shifts is only a convention.)
Thus `U = span{r_y,c_y}` is a `K`-invariant labelled subspace.  For `q>=4`
the only intersection of the row-constant and column-constant spaces is the
constant vector, so `dim U = 2q-1`.

## Dyadic module calculation

On augmentation-zero coefficients, (1) is multiplication by `1+S` and
`1+S^-1` in

```
F_2[C_q] = F_2[S]/((S+1)^q).
```

Each multiplier has a one-dimensional kernel.  Direct elimination in the
basis `r_0,...,r_(q-1),c_0,...,c_(q-2)` gives

```
rank(K|U) = 2q-3,        nullity(K|U) = 2.                 (2)
```

This odd rank does **not** contradict the even-rank theorem for alternating
matrices.  The ambient dot product restricted to `U` has rank `2q-2` and a
one-dimensional radical.  Therefore `U` is degenerate; one cannot split off
`U` orthogonally and add alternating ranks.  After quotienting its radical,
the apparent odd-rank effect disappears.  Gaussian elimination checks the
dimension/rank/radical triples

```
q=4:  (7, 5, 1)    q=8:  (15, 13, 1)
q=16: (31,29, 1)   q=32: (63, 61, 1).
```

The formulas above prove the general pattern through the cyclic group-ring
description; the finite rows are calibration, not evidence for the theorem.

## Why the cap is lost

The same-difference cap is the integer assertion

```
0 <= (K^2)_(v,w) <= 1
```

for distinct sources `v,w` in one fibre.  Reduction modulo two remembers
only the parity of the number of common targets.  It cannot distinguish the
allowed value `1` from the forbidden values `3,5,...`, or `0` from `2,4,...`.
Consequently (1), (2), alternating rank, Pfaffian parity, and any identity
formed only from `K mod 2` are already consequences of reciprocity and the
exact hits; they cannot use the inequality that separates the reciprocal
no-cap q8 models from the UNSAT full-cap instance.

## Verdict

The **pure** characteristic-two alternating-rank/quotient route is cut.  Its
interesting odd-dimensional invariant space is necessarily degenerate, and
the full cap vanishes under parity reduction.  A future minor identity would
need additional integer or lifted variables recording the actual entries of
the same-fibre blocks of `K^2`; calling the global adjacency alternating is
not enough.  The labelled identities (1) may still be useful inside an
integer pair-rooted certificate, but they do not themselves approach
`SizeTwoCyclicPackingExclusion`.

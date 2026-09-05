# Size-two matching-union symmetric-difference audit

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: exact pairwise localization; parity/lower-bound route cut at the
abstract matching-union interface.

## Exact localization

Use the reviewed matching unions `A_i` from
`NONBIP_MIXED_SIZE_TWO_RAINBOW_CENTER_SELF_INDEX.md`.  Each `A_i` is
`n`-regular on `C\W_i`, isolates the two vertices of `W_i`, and is the union
of `n` edge-disjoint perfect matchings.  For `i!=j`, the reviewed intersection
formula and `gamma_ij=n-delta_ij-p_ij` give

```text
|A_i intersect A_j| = n^2-n-delta_ij,
|A_i \ A_j| = |A_j \ A_i| = 2n+delta_ij.                (1)
```

There is no `A_i`-edge inside `W_j`.  Indeed, the pair
`W_j=N_H_C(c_j)` already has ambient common center `c_j`; an `A_i` selector
on the same pair would supply a second center, while `c_j` is not an ambient
neighbor of any `f in S_i`.  Since `A_i` is `n`-regular at both vertices of
`W_j`, exactly `2n` edges of `A_i\A_j` meet `W_j`.  Therefore, with

```text
X_ij=C\(W_i union W_j),
```

the pairwise disagreement away from the four forced holes is exactly

```text
|E(A_i[X_ij]) \ E(A_j[X_ij])| = delta_ij,               (2)
|E(A_j[X_ij]) \ E(A_i[X_ij])| = delta_ij.               (3)
```

Thus the companion defect count is precisely the core edit distance per
color; it is not merely an upper bound.

## Alternating-trail interpretation

Color `A_i\A_j` red and `A_j\A_i` blue.  At every vertex of `X_ij`, the
red and blue degrees agree because both original graphs have degree `n`.
At `W_j` there are `2n` red boundary incidences and no blue ones; at `W_i`
there are `2n` blue boundary incidences and no red ones.  Standard pairing
of opposite colors at each core vertex decomposes the difference into

* `2n` alternating paths whose `4n` endpoints are the red incidences at
  `W_j` and blue incidences at `W_i`, and
* optional alternating cycles contained in `X_ij`.

A path may pair two red endpoints or two blue endpoints; such paths occur in
balancing numbers.  Pairwise regularity alone does not force every path to
run from `W_j` to `W_i`.

The `delta_ij` red and `delta_ij` blue core edges are exactly the internal
steps distributed among those paths and cycles.  When `delta_ij=0`, all
paths have length two.  Evenness of `n` makes every uncolored difference
degree even at the holes as well, but yields no further color constraint.

## A q-generic zero-core-disagreement ledger

The matching-union axioms alone permit `delta_ij=0`.  For any `n>=1`, split
the `2n` vertices of `X_ij` into `P,Q` of size `n` and take the common core

```text
K_(n,n) minus one perfect matching,
```

which is `(n-1)`-regular.  Put one vertex of `W_j` on each side and join it
to every vertex of the opposite core side.  The resulting `A_i` is exactly
`K_(n+1,n+1)` minus a perfect matching: it is `n`-regular, isolates `W_i`,
and decomposes into `n` perfect matchings.  Construct `A_j` identically with
`W_i` in place of `W_j`, sharing the same core.  Then (1)--(3) hold with
`delta_ij=0`, and the difference consists of `2n` length-two paths from
`W_j` to `W_i`.

This is an abstract matching-union ledger, not a realization of the ambient
graph, its owner colors, or all three families simultaneously.  It is enough
to cut any proposed proof that uses only regularity, the two holes,
factorization, and symmetric-difference parity to force
`delta_ij>0` or a contradiction.

## Disposition

Equation (2) is the useful residue: any terminal must constrain the
`delta_ij` core edits through companion/owner labels or through simultaneous
compatibility of all three families.  Pairwise alternating-path structure by
itself is flexible and should not be pursued as a parity lemma.

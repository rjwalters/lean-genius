# Same-fibre owner Gram audit

Node: `BinarySizeTwoCyclicPackingBound`, positive-variance branch.

## Owner incidence

Let `F_t` be a source fibre and let `P_t` be its unordered base pairs.
For `p={x,z} in P_t` and a cell `v`, put

```text
R_t(p,v) = K((x,t),v) K((z,t),v).
```

Thus the row indexed by `p` records the common targets (owners) of the two
cells in `p`.  The same-fibre packing cap is exactly

```text
sum_v R_t(p,v) <= 1.                                  (1)
```

Consequently every row of `R_t` is either zero or a standard basis vector.
Moreover

```text
number of nonzero rows of R_t
  = sum_v choose(n_t(v),2)
  = V_t / 2.                                          (2)
```

This is the sharp owner formulation of the labelled load variance.

## The uncoloured owner Gram is automatically positive

Concatenate the matrices `R_t` vertically and form `G=R R^T`.  Index a
nonzero owner row by `(t,p)`, and write `o(t,p)` for its unique owner cell.
Then

```text
G((t,p),(s,r)) = 1  iff  o(t,p)=o(s,r),
                  0  otherwise.                      (3)
```

After sorting rows by their owner, `G` is a direct sum of all-ones matrices,
plus zero rows.  Hence it is positive semidefinite for **every** partial
owner function satisfying (1).  All principal minors and all Schur
complements of this uncoloured Gram are therefore tautologies.

The same observation kills the apparent three-fibre strengthening.  For
distinct fibres `t,s,r`, arbitrarily many endpoint pairs, one from each
fibre, may have the same owner: the packing hypothesis caps owners only for
a fixed same-fibre pair.  Such a merger merely enlarges one positive
all-ones block in (3).  No determinant involving `R_t R_s^T`,
`R_s R_r^T`, and `R_r R_t^T` can turn it into a contradiction.

In particular, (2) and positivity cannot improve the existing cap ceiling

```text
V_t / 2 <= choose(q,2).
```

The exact mean-one row/column laws constrain the two incident darts that
create an owner, but they impose no further linear condition on the owner
function after those darts have been forgotten.  This agrees with the
banked SAT block-degree relaxation: aggregation before applying transpose
loses the decisive base-position information.

## What a surviving Gram or flag certificate must retain

A useful matrix cannot index a flag merely by `(endpoint pair, owner)`.
It must retain at least

```text
(t; x,z; v; slot of (x,t)->v; slot of (z,t)->v),      (4)
```

where a slot includes the target row, absolute target column, and target
fibre.  Reciprocity must identify each dart in (4) with its reversed dart
*before* the two darts are multiplied or summed.  Equivalently, a viable
degree-six flag matrix needs rooted wedges extended by reciprocal darts;
the degree-four owner Gram `R R^T` is cut.

This does not rule out an exterior-minor or coloured-wedge certificate.
It gives a precise falsification criterion: if its variables factor only
through the partial owner function `o(t,p)`, its PSD constraints reduce to
(3) and cannot prove positive-variance amplification.  The first genuinely
new constraints must compare the slot labels of at least two wedges (hence
at least three sources/fibres) through entrywise block transpose.


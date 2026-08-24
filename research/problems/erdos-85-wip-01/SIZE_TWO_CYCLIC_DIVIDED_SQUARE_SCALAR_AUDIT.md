# Scalar divided-square audit

## Candidate

Divergence round 12 proposed retaining the all-ones rectangle over the
integers or `Z/4`, where it contributes `2`, rather than applying the
exterior square over `F2`, where its two terms cancel.  The cheapest proposed
invariant was the scalar divided square of the empty-fibre incidence matrix.

Let `B` have one row for each of the `q` source cells in the empty fibre and
one column for every allowed absolute target cell.  Put

```text
m(w) = sum_x B(x,w),
G = B B^T.
```

Then the exact integer identity is

```text
sum_w m(w)^2
  = sum_x G(x,x) + 2 sum_{x<z} G(x,z)
  = q(q-2) + 2 sum_{x<z} codeg(x,z).
```

Under the full cap, each off-diagonal codegree is `0` or `1`, so the last
sum is exactly the edge count of the simple owner-pair graph.  Thus the
scalar `Z/4` value is only the parity of the collision-token count (the
constant `q(q-2)` vanishes modulo four when `4 | q`).  It is not a new
quadratic datum.

## Row/column projection supplies no boundary residue

Could the two affine projections determine that parity?  For a fixed source
cell `(x,t)`, aggregation by absolute target row gives the indicator of the
complement of

```text
{x+t, x+t+1},
```

while aggregation by absolute target column gives the indicator of the
complement of

```text
{x-1, x}.
```

For two source bases `x,z`, the two coarse inner products are equal.  Indeed,
both are

```text
q - |{x,x+1} union {z,z+1}|,
```

after translation.  This equality is pointwise in the owner pair; summing
over fibres or invoking transpose reciprocity cannot create a leftover
boundary term.

Expanding either coarse inner product gives

```text
coarse overlap
  = precise common-target count
    + same-row (respectively same-column) different-cell mismatches.
```

Since the two coarse overlaps and the precise common-target count are the
same, the *scalar totals* of the row-mismatch and column-mismatch terms are
equal automatically.  Subtracting the row and column divided-square
identities yields `0=0`.  The consecutive holes leave no scalar `Z/4`
residue.

## Verdict

The scalar divided-square/Pontryagin candidate is **cut**: it is exactly the
already-banked collision mass, and the row-versus-column projection identity
is pairwise tautological.  It cannot strengthen the formal threshold
`two_mul_q_le_sizeTwoCyclicAgreement_support_card_of_noAdj`.

This does **not** cut the fully colored integer `Sym^2` candidate.  Any
surviving quadratic identity must retain which two different target cells
form each mismatch—at least their target fibre and displacement—rather than
summing them before comparing the row and column expansions.  Equivalently,
the missing object is a colored transport law on mismatch pairs.  A scalar
norm, trace, total permanent coefficient, or `Z/4` quadratic value has
already forgotten the only information on which reciprocity could act.

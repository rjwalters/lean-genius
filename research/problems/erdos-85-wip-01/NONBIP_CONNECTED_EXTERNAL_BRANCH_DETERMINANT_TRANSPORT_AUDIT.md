# NONBIP-CONNECTED external-branch determinant transport audit

Date: 2026-08-26.  Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **Smith/Fitting transport mechanism cut exactly**.

## Proposed sharpening

For a root `x`, let `B_x` be the zero-one incidence matrix whose rows are
indexed by `y in N_A(x)` and whose row support is

```text
E_x(y) = N_A(y) \ ({x} union N_A(x)).
```

The rooted Schur audit proved

```text
B_x B_x^T = diag(q-1-epsilon_y),                     (1)
```

where `epsilon_y=1` on the `2t_x` neighbors that lie in triangles through
`x`, and is zero otherwise.  Since `q=2^k` with `k>=3`,

```text
v_2 det(B_x B_x^T) = 2t_x.                           (2)
```

Thus a canonical integral equivalence between the rooted matrices at the two
ends of every defect edge, whose Gram determinants changed by valuation
divisible by eight, would imply `t_x=t_y (mod 4)`.  This audit asks whether
ordinary integral module invariants or the cross-star partial matching supply
such an equivalence.

## All determinantal ideals of `B_x` are trivial

C4-freeness makes the supports `E_x(y)` pairwise disjoint.  Their cardinalities
are `q-2` or `q-1`, hence are nonzero for `q>=8`.  Choose one coordinate
`c_y in E_x(y)` for every row.  On the selected `q` columns, `B_x` is a
permutation matrix.  More generally, selecting any `r` rows and their chosen
coordinates gives an `r` by `r` minor equal to one.

Consequently every nonzero determinantal ideal is the unit ideal:

```text
I_r(B_x) = Z,              1 <= r <= q.               (3)
```

Equivalently, `B_x` has Smith normal form

```text
[ I_q  0 ].                                              (4)
```

This is independent of `t_x`.  The cokernel is free, every Fitting ideal is
trivial in the relevant range, and reduction modulo `2^a` remains a split
surjection for every `a`.  Compound matrices do not rescue the proposal:
each exterior power `wedge^r B_x` again contains a unit coordinate.  Hence
none of the standard integral, local, or compound-minor equivalence invariants
of `B_x` sees the valuation in (2).

## Why the Gram valuation is metric data, not module data

Equation (2) survives because the standard Euclidean metric remembers the
*sizes* of the disjoint row supports.  Smith equivalence allows arbitrary
unimodular column operations, and those do not preserve `B_x B_x^T`.
Indeed (4) sends every rooted matrix to the same integral normal form while
their Gram determinants range through

```text
(q-2)^(2t_x) (q-1)^(q-2t_x).                           (5)
```

Only an integral isometry of the coordinate lattices (in this zero-one
setting, canonically a signed coordinate permutation) would transport (5).
Such an isometry is strictly stronger than an isomorphism of the incidence
modules.

For a defect edge `xD y`, the ambient edges between `N_A(x)` and `N_A(y)`
give only a partial matching.  It canonically identifies the matched
coordinates, but supplies no bijection on the unmatched coordinates and no
isometry between all external branch supports.  The full q=4 calibration has
cross-star matching ranks `2,3,4,7`, so the deficiency is real and variable,
not a dimension count that square order fills.  Completing the partial
matching requires arbitrary extra pairs; the determinant or signed unit class
of such a completion is therefore additional coordinate data.

Nor can one compare only the matched restriction: deleting the unmatched
columns changes the row norms by uncontrolled, root-dependent amounts.  Its
Gram valuation is no longer (2), so the restriction has lost exactly the
triangle statistic that the proposed transport was meant to propagate.

## Verdict

The determinant observation (2) is exact and potentially useful, but it does
not descend to Smith, Fitting, cokernel, modular-rank, or compound-minor data:
all those invariants are already trivial by the unit transversal minor.  The
cross-star matching is only partial and therefore supplies no canonical
metric isometry capable of transporting the Gram determinant.  The proposed
integral determinant/Fitting route is cut under the current graph axioms.

A successor must independently construct full star coordinates or an
isometry (for example from genuine finite geometry).  Choosing an arbitrary
completion and then reading its determinant would insert precisely the extra
structure that remains to be proved.

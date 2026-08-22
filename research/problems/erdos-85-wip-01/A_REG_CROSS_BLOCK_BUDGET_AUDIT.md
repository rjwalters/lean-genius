# A-REG cross-block budget audit

Status: q-generic negative result for `A-REG-NONBIP`, 22 August 2026.

## Question

Do the parameter-free cross-block identities

- `c4Free_crossBlock_trace_zero`,
- `c4Free_sameBlock_offDiagonal_gram_zero`, and
- `c4Free_crossBlock_twoWalk_add_defect_eq_card_mul`

add pressure when combined with the owner/selector budgets of the regular
square-order core?

They do not at the scalar level.  After specialization to distinct defect
components, the saturation identity is the sum of the already proved unique
cross-selector law, and both orthogonality identities merely say that the
unique common-neighbor owner has one color.  The budgets have **zero slack**.

## Exact ledger

Let `c,d` be distinct defect components, with

```text
|c| = q m_c,    |d| = q m_d.
```

Every ambient vertex has exactly `m_c` neighbors in `c` and `m_d` neighbors
in `d`.  Thus its two component selectors cover `m_c m_d` pairs in `c x d`.
There are `q^2` ambient vertices, so selector capacity is

```text
q^2 m_c m_d = |c| |d|.                              (1)
```

The theorem `existsUnique_mem_cross_componentNeighborFinsets` says that this
capacity partitions `c x d`: every cross pair has exactly one ambient owner.
Equivalently,
`transpose_defectComponentNeighborIncidenceMatrix_mul_eq_ones` is the
entrywise matrix version of (1).  Since the defect graph has no cross edge,
`c4Free_crossBlock_twoWalk_add_defect_eq_card_mul` specializes to precisely
the sum of this all-ones matrix.  It supplies no new inequality.

Classify the unique owners by the defect component containing the owner.
Owners lying in `c` account for

```text
|c| m_c m_d = q m_c^2 m_d
```

cross pairs, and owners lying in `d` account for

```text
|d| m_c m_d = q m_c m_d^2.
```

The two supports are disjoint by uniqueness; this is exactly what
`c4Free_crossBlock_trace_zero` sees.  The residual is

```text
q^2 m_c m_d - q m_c m_d (m_c + m_d)
  = q m_c m_d (q - m_c - m_d).                       (2)
```

Because the component weights sum to `q`, (2) is exactly the contribution
from owners in all third components.  It is not a deficit.  With two
components it is zero; with three or more it has the same exact size as the
third-component selector budget.  In asymptotic language, for bounded
`m_c,m_d` the two named supports are `Theta(q)` inside a `Theta(q^2)`
universe and the `Theta(q^2)` remainder is fully accounted for.  If the
weights scale with `q`, equation (2), rather than a weaker order estimate,
still gives exact equality.

The same calculation applies to ordered nondefect pairs inside `c`.  Their
number is

```text
q^2 m_c (m_c - 1).
```

Owners from a component of weight `m_e` account for

```text
q m_e m_c (m_c - 1),
```

and summing over `e` again gives equality because `sum_e m_e = q`.
Consequently `c4Free_sameBlock_offDiagonal_gram_zero` only records the
disjointness of already unique owner-color classes.

## Algebraic countermodel to a scalar terminal

The insufficiency is visible without a candidate graph.  Let `F` be a finite
field of order `q`.  Take `q^2` formal points `(j,y)` in `F x F` and `q^2`
formal selectors indexed by `(a,b) in F x F`, with

```text
S_(a,b) = { (j, a*j+b) : j in F }.
```

Partition the `q` coordinate fibers `{j} x F` into arbitrary aggregate
blocks of weights `m_c` summing to `q`.  Every selector meets an aggregate
block `c` in exactly `m_c` points.  Points in distinct coordinate fibers
belong to a unique common selector, while two distinct points in the same
fiber belong to none.  Hence this model satisfies:

- every uniform component-selector cardinality;
- every cross-block unique-selector and all-ones incidence identity;
- both common-neighbor support orthogonalities; and
- the exact two-walk/defect scalar saturation ledger.

It exists for every prime-power `q` and every partition of the coordinate
fibers, including all parts at least two.  It is intentionally only an
incidence/budget model: an aggregate block of weight greater than one is a
union of coordinate fibers, not a connected component of its formal defect
relation.  This isolates the missing information exactly.

## Consequence for the critical path

The generic Gram cuts plus scalar owner/selector budgets do **not** define a
proper child of `A-REG-NONBIP`.  Any successful child must use information
discarded by the countermodel, such as

- connectivity and internal adjacency of each true defect component;
- compatibility of selector rectangles with those internal edges; or
- a non-scalar rank, determinant, or spectral restriction coupling several
  owner colors to the internal component operators.

The newly generic defect-cut spectral pipeline is compatible with this
diagnosis: its next genuine input must produce an internal mode whose
transport is nonzero and impossible outside.  Cross-block orthogonality and
the scalar budgets alone cannot produce that mode.

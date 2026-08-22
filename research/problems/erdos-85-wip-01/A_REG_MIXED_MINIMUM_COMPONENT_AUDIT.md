# A-REG mixed minimum-component audit

Status: q-generic negative audit under `A-REG-NONBIP / NONBIP-MIXED`,
22 August 2026.

## Candidate mechanism

Every binary square-order candidate has a nonempty triangle-free edge graph

```text
T = triangleFreeEdgeGraph G = A ∩ D.
```

For a defect component `c` of normalized weight `m_c`, the existing uniform
theorems give

```text
deg_T(x) <= m_c,
deg_T(x) is even.
```

Could a minimum component, especially when all weights are at least three,
force the support of `T` to propagate through connected `D_c` and yield a cut
contradiction?

## Weight three gives only cycles and isolated points

If `m_c=3`, the two displayed facts imply

```text
deg_T(x) in {0,2}  for every x in c.                 (1)
```

Thus the restriction of `T` to `c` is a disjoint union of cycles and isolated
vertices.  Unlike the size-two lane, degree two does not saturate the
three-point component selector.  The proof of
`binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_adj`
therefore does not extend: a third internal selector point remains, and a
`D_c` edge can join a `T`-cycle vertex to a `T`-isolated vertex without
violating (1).  Connectivity of `D_c` supplies no support propagation.

Nonemptiness of global `T` also does not say that `T` meets a minimum-weight
component; all of its edges may lie in a larger component.

## Uniform reduced control

The failure persists after imposing every scalar `T` ledger currently in the
outline.  Let `q=2^k`, `k>=4`, and take the normalized partition

```text
3 + (q-3) = q.
```

On each block of size `qm`, use the connected nonbipartite circulant defect
graph with step set

```text
{ +/-1, ..., +/-(q-2)/2, qm/2 }.
```

It is `(q-1)`-regular, connected because step 1 is present, and nonbipartite
because steps 1 and 2 give a triangle.  Put all `T` edges in the weight-three
component and take:

- a 5-cycle when `k` is even;
- a 7-cycle when `k` is odd (then `k>=5`).

The circulant contains these cycles: for length five use successive steps
`1,1,2,-1,-3`; for length seven use `1,1,1,1,1,1,-6`.  All other vertices
are `T`-isolated.  Consequently the reduced data satisfy:

- every defect component is connected, nonbipartite, and `(q-1)`-regular;
- all normalized weights are at least three;
- `T` is nonempty, Eulerian, and has girth at least five;
- `deg_T <= m_c` in every component.

They also satisfy the exact global triangle-free-edge congruence.  Since
`q mod 3` is `1` for even `k` and `2` for odd `k`,

```text
q^3/2 mod 3 = 2  (k even),
q^3/2 mod 3 = 1  (k odd).
```

The chosen cycle lengths `5` and `7` have precisely those residues, so

```text
#triangles = (q^3/2 - |E(T)|) / 3
```

is a nonnegative integer and the identity
`binarySquare_regular_triangleFreeEdge_card_eq_pow_sub_three_mul_triangles`
is numerically satisfied.

This is intentionally a reduced `(D,T)` control, not an ambient graph `G`.
It proves that component sizes, `D` connectivity, pointwise evenness/bounds,
`T` nonemptiness/girth, and the global triangle ledger cannot by themselves
yield the proposed propagation or cut contradiction.

## Disposition

The minimum-component `T`-support route is closed at the present interface.
A proper child of `NONBIP-MIXED` must use an incidence-level relation absent
from the control, for example compatibility of the component selectors with
the *locations* of internal `D` edges.  Component weight and `T` degree data
alone are exhausted.

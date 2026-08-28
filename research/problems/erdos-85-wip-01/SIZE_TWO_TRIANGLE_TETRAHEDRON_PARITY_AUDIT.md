# Triangle tetrahedron-parity audit

Node: `A-REG-NONBIP / all size-two`; divergence round 102.

## 1. A branch-wide nonlinear invariant

In the all-weight-two branch put `X_ij=A[C_i,C_j]`.  Every block has row and
column sum two, `X_ji=X_ij^T`, and for `i!=k`

`sum_e X_ie X_ek=J`.

Nonnegativity makes the supports of the products disjoint.  They partition
all cells between `C_i` and `C_k` by the component containing the unique
two-step intermediate vertex.

For three distinct component colors define

`T_ijk=tr(X_ij X_jk X_ki)`.

This is the number of triangles having one vertex in each of the three
components.  Let `P_iik` be the number of triangles with two vertices in
`C_i` and one in `C_k`.  The `4q` cross edges between `C_i,C_k` split exactly
as

```text
4q = 2 P_iik + 2 P_ikk + sum_(j != i,k) T_ijk.       (1)
```

The repeated-color terms are even also directly at matrix level:

`tr(X_ii X_ik X_ki)=2 P_iik`,

because the symmetric off-diagonal entries occur in both orientations.
Reducing (1) modulo two shows

`sum_(j != i,k) T_ijk=0 mod 2`

for every color pair.  Therefore the set of color triples on which `T_ijk`
is odd is a simplicial 2-cycle over `F_2`.  The full color simplex is
contractible, so every such cycle is a sum of boundaries of color
tetrahedra.  For `q=8`, where there are exactly four components, the sole
nonzero possibility is:

> all four distinct-color triangle counts are odd.

This uses the simultaneous 0/1 placement, not spectra, tree arithmetic, or
affine normalization.

## 2. Local neighborhood matching law

Every cross-component A-edge has exactly one common neighbor and hence lies
in a unique triangle.  In a C4-free graph the graph induced on `N_A(x)` has
maximum degree one, so the triangles through `x` pair incident A-edges.

A vertex in a size-two component has `q-2` cross-component neighbors and two
same-component neighbors.  Since `q-2` is even, the number of its internal
neighbors used in triangles is either zero or two.  Consequently the
triangular edges of the diagonal two-factor `X_ii` form a union of whole
cycles.

This suggested that (1), lifted modulo four and combined with the internal
cycle selection, might exclude a tetrahedron boundary.  It does not.

## 3. Exact `q=8` aggregate counterledger

Take four colors and prescribe

`T_012=T_013=T_023=T_123=7`.

For every unordered color pair, the two relevant face counts sum to fourteen,
so (1) requires

`P_iik+P_ikk=9`.

Orient the six pair totals by

```text
P_001=0,  P_002=7,  P_003=9,
P_112=0,  P_113=7,  P_223=5,
```

with the reverse-majority count on each pair equal to `9` minus the displayed
number.  The totals of triangular internal edges in the four components are

`16,16,16,6`.

These are realized at the cycle-ledger level by three fully triangular
`C_16` diagonal factors and by selecting the `C_6` but not the `C_10` in a
`C_6 disjointUnion C_10` factor.  There are no all-internal triangles in the
ledger.

Every exact count now matches:

```text
two-color triangles:       54
distinct-color triangles:  28
cross-edge count:           2*54 + 3*28 = 192 = 6*(4q).
```

The aggregate local matching capacities match as well.  In each of the first
three components, all sixteen vertices use both internal neighbors, leaving
`16*2=32` cross-cross triangle slots.  The three distinct-color faces supply
21 incidences and incoming minority two-color triangles supply 11.  In the
last component, six used vertices and ten unused vertices give
`6*2+10*3=42` slots, split as 21 plus 21.

The dependency-free verifier `verify_q8_tetrahedron_triangle_ledger.py`
checks every pair equation, oriented majority total, cycle total, global
cross-edge count, local capacity, and odd face parity.

## 4. Scope of the falsifier

This is an aggregate outer ledger, not a graph and not a realization of the
nonedge rectangle tilings.  It decisively cuts arguments that use only:

- the mod-2 color 2-cycle;
- equations (1) modulo four;
- the 0/2 internal-neighbor rule;
- whole-cycle selection in the diagonal two-factors; and
- aggregate per-component triangle-matching capacity.

A surviving terminal must use pointwise placement.  The sharp next target is
the nonedge-route coupling: each intermediate support `supp(X_ie X_ek)` is a
union of `2q` labeled `K_2,2` rectangles and the intermediate supports
partition **all** cells, not only the cross A-edges counted above.  Equivalently,
one must either realize the ledger by reciprocal blocks or find the first
pointwise rectangle/transposition obstruction.  No further aggregate
triangle congruence is justified by the current data.

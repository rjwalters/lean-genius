# Mixed defect components survive the least-eigenvalue condition

Date: 6 September 2026. Node: `A-REG-NONBIP / NONBIP-MIXED`.
Status: uniform defect-only construction; no ambient A is constructed.

The connected least-eigenvalue terminal in
`NONBIP_CONNECTED_LITERATURE_DIVERGENCE.md` uses that both degrees of a
bipartite biregular line-graph root divide q². For a component of order
mq, the degrees instead divide mq. That distinction is essential.

For every q=2^k with odd k>=3 there exists a simple (q-1)-regular graph D
of order q² with exactly two connected nonbipartite components, each of
order divisible by q, and with least eigenvalue at least -2. Neither
component is a clique. Thus these conditions alone cannot extend the
connected terminal to the mixed branch.

## Construction

Put r=q/2 and c=(q-2)/3. Odd k gives q=2 modulo 3, so c is a positive
integer. Construct a bipartite graph H1 with right vertices Z/rZ and left
vertices (i,j), where i is in Z/rZ and 1<=j<=c. Join (i,j) to i,i+1,i+2.
Since r>=4 these are three distinct neighbors. The left degree is 3 and
the right degree is 3c=q-2. Consecutive right vertices share a left
neighbor, so H1 is connected. It has

```text
e1 = 3rc = q(q-2)/2
```

edges. Its line graph D1 is connected and has degree 3+(q-2)-2=q-1.

For H2, take two disjoint copies of K_(r+1),r. In each copy designate an
edge u_i v_i, delete the two designated edges, and insert u_0 v_1 and
u_1 v_0. The new edges were absent, all degrees are preserved, and each
copy minus its designated edge remains connected. Hence H2 is simple,
connected, and bipartite biregular with degrees r and r+1. It has

```text
e2 = 2r(r+1) = q(q+2)/2
```

edges. Its line graph D2 is connected and has degree r+(r+1)-2=q-1.

Let D be the disjoint union of D1 and D2. Their orders sum to q² and
their component weights (order divided by q) are

```text
m1=(q-2)/2,                 m2=(q+2)/2,               m1+m2=q.
```

Both roots have a vertex of degree at least 3, whose incident edges give
a triangle in its line graph. Both components are therefore nonbipartite.
Their orders exceed q, whereas a (q-1)-regular clique has order q.

For the unsigned vertex-edge incidence matrix B of either simple root,
`B^T B = 2I + adjacency(line graph)`: each edge has two endpoints and
two distinct edges share at most one endpoint. Positivity of B^T B proves
the asserted least-eigenvalue bound without a classification theorem.

## Verification and scope

An exact finite root check at q=32 and q=128 verified edge uniqueness,
connectedness, endpoint-degree sum q+1 on every edge, and the total q²
edge count. The resulting component orders are (480,544) and
(8064,8320), respectively. The construction above proves the whole
odd-exponent family; these finite checks are only calibration.

This D is not asserted to admit a symmetric binary zero-diagonal matrix A
with `A^2=(q-1)I+J-D`, nor even a real square root satisfying all ambient
constraints. In particular, its component sizes and least eigenvalue do
not establish the required self-indexed neighborhood incidences. The
construction closes only the attempt to use the connected root-divisibility
argument unchanged in the mixed branch. Further work must use an actual
constraint linking A to these line-graph components; no additional
defect-only classification or Lean wrapper is proposed here.

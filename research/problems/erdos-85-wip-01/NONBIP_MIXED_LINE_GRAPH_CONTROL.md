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

## The ambient equation excludes this particular cyclic root for q>=32

The distinction from ambient realizability can be made explicit. Suppose a
component of an actual defect graph is L(H), and let B be the unsigned
vertex-edge incidence matrix of H, padded with zero columns at vertices
outside this defect component. Let d be the root-degree vector and
Q=B B^T. The star at any root vertex is a clique of D. Distinct vertices
of a D-clique have no common A-neighbor, so X=B A is a binary matrix,
with row sums q d. From the ambient square identity one obtains

```text
X X^T = (q+1)Q - Q² + d d^T.
```

Indeed, on this component `D=B^T B-2I`, so
`B D B^T=Q²-2Q`. For distinct nonadjacent root vertices u,v,
`Q_uv=0` and `(Q²)_uv=|N_H(u) intersection N_H(v)|`. Applying the
preceding identity to the binary complement Y=J-X, with q² columns,
gives the necessary entrywise inequality

```text
0 <= (Y Y^T)_uv
   = (q-d_u)(q-d_v) - |N_H(u) intersection N_H(v)|.    (1)
```

In our H1, two consecutive right vertices have 2c common left neighbors
when r>=4: their two shared starting indices each have c clones. Their
degrees are q-2. Equation (1) would require

```text
2(q-2)/3 <= 4,
```

which fails for q>=32. Thus the particular D constructed here cannot be
the defect graph of an ambient A at any odd exponent k>=5. This confirms
its intended role as a control against defect-only reasoning. It does not
exclude other biregular roots with different codegrees, and is not a
mixed-branch terminal. No conclusion from (1) is claimed at q=8.

The remaining root class is nonempty, as independently observed by Sol2.
In any root with these part sizes and degrees, the average codegree of
two right vertices is `(q-2)*2/(r-1)=4`. Thus the bound forces every such
codegree to equal 4. Write r=4^j, which is possible for odd k. Take the
points of the affine space over F4 as right vertices. For each affine
line, which has four points, take two copies of each of its four
three-point subsets as left vertices, adjacent to their three entries.
Each pair of points lies on one line and in two of its three-point
subsets, hence has codegree 4. Each point lies on (r-1)/3 lines and in
six copied subsets per line, giving degree 2(r-1)=q-2. This is a simple
bipartite root (the copied subsets are distinct left vertices), connected
because every right pair has a common neighbor. It has the same edge
count as H1 and passes the right-pair bound exactly. This replacement
shows why the cyclic-root exclusion cannot close the root class; no
ambient realization of the replacement is claimed.

## Verification and scope

An exact finite root check at q=32 and q=128 verified edge uniqueness,
connectedness, endpoint-degree sum q+1 on every edge, and the total q²
edge count. The resulting component orders are (480,544) and
(8064,8320), respectively. The construction above proves the whole
odd-exponent family; these finite checks are only calibration.

The construction closes the attempt to use the connected root-divisibility
argument unchanged in the mixed branch. Equation (1) additionally excludes
this specific construction from ambient realization for k>=5. Neither
result proves general nonexistence of A or supplies a real square root
satisfying its other constraints. A general line-graph terminal would have
to exclude every possible root, including those satisfying (1); that step
remains missing. This bounded check stops here, with no Lean wrapper.

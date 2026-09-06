# No bounded-size repair of the even-polarity core at unbounded degree

Node: construction-side test of A-REG, using the A.1 polarity existence jaw.
Date: 2026-09-06. Status: uniform prose theorem; no Lean claim.

Let F be a finite field of characteristic two, q=|F|. The even-polarity
core has vertex set `F²\{0}` and adjacency `omega(u,v)=1`, where omega
is the alternating determinant form. It is q-regular and C4-free.
The affine coordinate identification and the sharper k=1 argument are
recorded in `POLARITY_TOP_BAND_K1_SURGERY_OBSTRUCTION.md`.

Consider a repair which deletes a set K of k old vertices, removes an
arbitrary set R of edges between surviving old vertices, and adds k+1
new vertices. Edges among new vertices and between old and new vertices
are arbitrary. No new edges between surviving old vertices are added.

**Theorem.** If k>=1 and the repaired graph is q-regular and C4-free,
then

```text
q <= 3k² + 5k.                                       (T)
```

For k=0 no such repair exists. Thus no fixed number of deleted vertices
can repair this source graph to order q² for unbounded q. This is not an
exclusion of arbitrary graphs at order q² or repairs whose deleted set
grows with q. A further bound for inserted old-old edges appears below.
The local overlap improvement is due to Sol1's independent review.

## Degree and overlap budgets

Put r=k+1. For a surviving old vertex v, write d_K(v) for its number of
neighbors in K, d_R(v) for its removed survivor edges, and s_v for its
number of new neighbors. Regularity gives

```text
s_v = d_K(v)+d_R(v),             0 <= s_v <= r.         (1)
```

Let e_K count old edges inside K and e_J edges inside the new gadget.
Counting the new-old edges in two ways gives

```text
rq-2e_J = kq-2e_K+2|R|,
|R| = q/2+e_K-e_J.
```

Consequently

```text
q/2-k(k+1)/2 <= |R| <= q/2+k(k-1)/2.                  (2)
```

Every pair of new vertices has at most one common old neighbor. Hence

```text
sum_v binom(s_v,2) <= binom(r,2).                     (3)
```

Let P be the surviving old vertices adjacent to some vertex of K, and
let E={v:s_v>=2}. Then `|E|<=binom(r,2)`. Every R-incident vertex in P
belongs to E by (1). Call surviving old vertices outside P external.

## A selector containing an external vertex has few root neighbors

Let A_i be the old-neighbor set of new vertex i, so `|A_i|>=q-k`.
Suppose y is external and belongs to A_i. Fix x in K and put
`L_x=N_core(x)`.

For n in `A_i intersect L_x`, the old pair y,n must have no common
neighbor left in the repaired graph, since both attach to i.

There is at most one n in L_x linearly dependent with y: the line F*y
meets the affine line `omega(x,n)=1` in at most one point. Every other
n has a unique core common neighbor z with y. It cannot belong to K,
because y is external. Thus either yz or nz must be in R.

There are exactly s_y removed neighbors z of y, by (1). Each such z is a
survivor, hence z!=x, and `|L_x intersect N_core(z)|<=1` by core
C4-freeness. These account for at most s_y possible n. To bound the
remaining n, use the **local** overlap budget at gadget vertex i:

```text
sum_(v in A_i) (s_v-1) <= k.
```

Each of the other k new vertices shares at most one old neighbor with i.
The vertex y already consumes s_y-1 of this budget. If nz is removed,
n is an R-incident vertex of P and has s_n>=2. Since y is external,
these n are distinct from y, and there are at most k-s_y+1 of them.
Counting the union of possibilities therefore gives

```text
|A_i intersect L_x| <= 1+s_y+(k-s_y+1) = k+2.
```

Since P is contained in the union of the k sets L_x,

```text
|A_i\P| >= q-k-k(k+2).                               (4)
```

If two selectors contain external vertices, (4) counts at least
`2(q-k-k(k+2))` external new-old incidences. By (1), the total number of
these incidences is `sum_external d_R(v)<=2|R|`. Using (2),

```text
2(q-k-k(k+2)) <= q+k(k-1),
q <= k²+k+2k(k+2) = 3k²+5k.                          (5)
```

Thus, if (T) fails, at most one new vertex has external old neighbors.

## A single external selector cannot support the removed edges

Assume q exceeds the right side of (T). An R-incident external vertex
has `d_R(v)=s_v` by (1). Since only one new vertex can have external
neighbors, it follows that d_R(v)=1 and all such vertices belong to the
same selector.

Suppose uv is an R-edge with both endpoints external. The core contains
the triangle through `z=u+v`: z is nonzero, distinct from u,v, and
adjacent to both. It cannot be deleted, since z in K would make u,v
members of P. Neither uz nor vz can be in R, because u and v each have
R-degree one, already used by uv. Their shared new neighbor and z then
give a C4. Therefore every R-edge has at least one endpoint in P.

But the total R-degree on P is bounded using (3):

```text
|R| <= sum_(v in P) d_R(v)
    <= sum_(v in E) (s_v-1)
    <= sum_(v in E) binom(s_v,2)
    <= k(k+1)/2.
```

Here d_K(v)>=1 on P justifies d_R(v)<=s_v-1. The lower bound in (2)
now gives `q<=2k(k+1)`. For k>=1 this is strictly smaller than
`3k²+5k`, a contradiction. This proves (T).

For k=0, (1) forces R to be a matching of q/2 edges, all endpoints
attached to the sole new vertex. Each matching edge's core triangle
survives on its other two edges, immediately producing a C4.

## Allowing inserted edges between surviving old vertices

Sol3's complementary path argument treats this additional operation.
Suppose ell>0 old-old nonedges are inserted, besides the deletions and
new gadget above. Then any q-regular C4-free repair satisfies

```text
q <= 2ell+k²+3k+2.                                  (I)
```

Choose an inserted nonedge uv of the original core. For each a in N(u),
there is a unique common neighbor b of a,v, unless a is proportional
to v. The intersection `N(u) intersect F*v` has one point when
omega(u,v)!=0 and none otherwise. Thus there are q-1 or q paths
`u-a-b-v` in the core. All are simple: uv is a nonedge, excluding a=v
and b=u, and adjacency excludes a=b.

These paths are edge-disjoint. Distinct paths have distinct a and
distinct b by C4-freeness. A shared undirected middle edge in opposite
orientations would put two distinct vertices in N(u) intersect N(v),
which is impossible. End edges cannot coincide with middle edges because
all interiors exclude u,v. Each vertex occurs internally at most once
as a and at most once as b.

Deleting k vertices destroys at most 2k of these paths. Each remaining
path, together with the inserted uv, would create a C4, and each removed
old edge destroys at most one path. Therefore `|R|>=q-1-2k`.
The degree identity now becomes

```text
|R|=q/2+e_K-e_J+ell <= q/2+k(k-1)/2+ell.
```

Combining proves (I). This argument does not apply the earlier selector
equation (1) after old-old insertions; it uses the amended total budget.

Consequently, for fixed k and ell, neither case can scale to unbounded q:
ell=0 is covered by (T) (or the k=0 triangle argument), and ell>0 by (I).
In particular, a family with bounded inserted old-old edges would need
the number of deleted vertices to grow at least on the order of sqrt(q).
No claim excludes repairs whose edit counts grow with q.

## Verification and limit of the result

The proof uses only the displayed degree counts, C4 overlap bound, and
the core's elementary two-dimensional geometry. The k=1 predecessor
also checks the core triangle identity on all 2,040 edges at q=16; the
uniform proof does not depend on that finite check. The polynomial
identities and comparisons in (5) were checked with exact arithmetic.

No classification of large selectors beyond (4) is assumed. Both bounds
allow shared selectors and arbitrary edges within the new gadget.
They show necessary growth of the repair size, not existence or
nonexistence of repairs above the bounds. The general A-REG gap remains.

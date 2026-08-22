# Defect cut variance and maximal edge connectivity

Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.

Status: q-generic hand proof, independently audited in squad review #16.
This is structural progress, not a terminal contradiction.  The companion
script exhausts every shore of the banked q=4 fixed-free control.

## Setup

Let `A` be a symmetric loopless q-regular 0/1 matrix on `n=q^2` vertices,
with every two distinct rows having inner product at most one.  Let `D` be
the second-order defect graph, so

```text
L_D = (q-1)I - D = A^2 - J.
```

For `S` a vertex set, write `s=|S|`,
`b_v=|N_A(v) intersect S|`, and `delta_D(S)` for its D-edge boundary.

## Exact cut-variance identity

Center the indicator of `S`:

```text
x = 1_S - (s/q^2) 1.
```

Then `x` is perpendicular to `1`, and regularity gives

```text
A x = b - (s/q) 1.
```

Consequently

```text
|delta_D(S)|
  = x^T L_D x
  = x^T (A^2-J) x
  = ||A x||^2
  = sum_v (b_v-s/q)^2.                       (1)
```

Write `s=qa+r`, with `0 <= r < q`, and put `c_v=b_v-a`.  Since
`sum_v b_v=qs`, one has `sum_v c_v=qr`.  Among `q^2` integers with this
sum, the square sum is minimized by `qr` ones and zeros elsewhere.  Equation
(1) therefore gives

```text
|delta_D(S)| >= r(q-r).                       (2)
```

When `r=0`, equation (1) is an integer square sum with zero coordinate sum,
so every such cut is even.

## Maximal edge connectivity

Assume `D` is connected.  Suppose a nontrivial cut has size
`delta <= q-2`.  Inequality (2) forces `r=0`.  Hence

```text
y = A 1_S - a 1
```

is a nonzero integer vector satisfying

```text
sum_v y_v = 0,       ||y||^2 = delta.
```

Let `m=|supp(y)|`; then `2 <= m <= delta`.  Count incidences from
`supp(y)` into A-neighborhoods.  There are `mq` incidences.  If `k_v` is
the number of support vertices adjacent to `v`, C4-freeness gives

```text
sum_v choose(k_v,2) <= choose(m,2).
```

For `k_v >= 2`, one has `k_v <= 2 choose(k_v,2)`.  Therefore at least

```text
mq - 2 choose(m,2) = m(q-m+1)                (3)
```

vertices have exactly one A-neighbor in `supp(y)`.  At each such vertex
`Ay` is nonzero, so (3) is a lower bound for `|supp(Ay)|`.

On the other hand,

```text
Ay = A^2 x = L_D 1_S,
```

which is supported only at endpoints of the `delta` cut edges.  Thus

```text
m(q-m+1) <= 2 delta.                          (4)
```

The left side is concave in `m`.  On `2 <= m <= delta <= q-2`, its two
endpoint values satisfy

```text
2(q-1) > 2 delta,
delta(q-delta+1) >= 3 delta > 2 delta,
```

contradicting (4).  Every nonzero D-cut therefore has size at least `q-1`.
Since `D` is `(q-1)`-regular, a singleton shore realizes a cut of size
`q-1`, and hence

```text
lambda(D) = q-1.
```

## Immediate residue

- A minimum cut has shore size congruent to `1` or `-1` modulo `q`.
- A nontrivial q-divisible shore has an even cut of size at least `q`.
- `D` is bridgeless and odd-regular, hence has a perfect matching by
  Petersen's 1-factor theorem; deleting it leaves an even `(q-2)`-regular
  graph with a 2-factor decomposition.
- If `F=D\T` is disconnected, every union of F-components has an all-T
  boundary of size at least `q` (and at least `2q-4` when its even size is
  not divisible by `q`).

These consequences are new constraints on a connected defect graph, but
they do not yet exclude one.  Lean promotion should wait for a consumer, in
accord with goal #24's math-before-certificates rule.

## Equality case and a second cut

Suppose a nontrivial minimum cut has size `q-1`.  After replacing its shore
by its complement if necessary, write `|S|=qa+1`.  Equality in the integer
variance bound gives a q-set `R` such that

```text
A 1_S = a 1 + 1_R.                            (5)
```

Put `d_u=|N_D(u)\S|` for `u in S`.  Comparing the singleton minimum cut
with the cut of `S\{u}` shows

```text
d_u <= (q-1)/2                                (6)
```

for every `u in S`.  Applying `A` to (5) gives

```text
A 1_R - 1 = L_D 1_S.
```

Since its left side has entries at least `-1`, every outside vertex has at
most one cut edge.  Thus the outside endpoints of the cut are `q-1`
distinct vertices: an endpoint has no A-neighbor in `R`, every other outside
vertex has one, and a vertex `u in S` has `1+d_u`.  If
`c_v=|N_A(v) intersect R|`, C4-freeness and direct squaring give

```text
sum_v choose(c_v,2) = ((q-1) + sum_{u in S} d_u^2)/2,
|delta_D(R)|        =  (q-1) + sum_{u in S} d_u^2.       (7)
```

If `R=N_A(v)` for some vertex `v`, then comparison with
`A 1_R-1=L_D 1_{v}` shows that `1_S-1_{v}` lies in the kernel of `L_D`.
Connectedness would make `S` a singleton or its complement.  Hence excluding
a nontrivial minimum cut reduces to recognizing `R` as an A-neighborhood.

An exact SAT audit at `q=4` found no counterexample to this recognition
statement in any of the five normalized cases `|S intersect R|=0,...,4`,
even without imposing connectedness of `D`.  This is finite external
evidence only.  Equations (6)--(7) do not force recognition for general q:
they bound the common-neighbor collision count but do not force its maximum
`choose(q,2)`.  Super-edge-connectivity is therefore not claimed.

### Punctured parallel classes from every minimum cut

The one-sided matching boundary has a general resolvable-design form.  Let

```text
Z = {z outside S : deg_A(z,R)=0}.
```

These are exactly the `q-1` outside endpoints of the minimum cut.  Write
`s_z` for the unique D-neighbor of `z` in `S`.  Since `N_A(z)` is disjoint
from `R`, equation (5) says every `w in N_A(z)` has exactly a A-neighbors
in `S`.  The q sets

```text
N_A(w) intersect S,       w in N_A(z),
```

are pairwise disjoint: a common point of two would give those two vertices
the distinct common A-neighbors `z` and that point.  Their total size is
`qa`, and the D relation says their union is precisely `S\{s_z}`.  Thus
every endpoint gives a parallel class of q a-blocks on the once-punctured
shore.  The omitted point `u in S` occurs in exactly `d_u` of the `q-1`
classes.

This statement is valid for every nontrivial minimum cut, independently of
the later triangle/near-bipartite dichotomy.  Aggregate cross-class pair
counts have constant-factor slack (and no pair content when `a=1`), so the
remaining issue is compatibility of the block labels with their own point
locations.

That location constraint has a compact Boolean-factorization form.  Put
`C=V\R`, let `X=A[Z,C]`, let `Y=A[C,S]`, and let `M` be the matrix with
`M_(z,s)=1` exactly when `s=s_z`.  Then

```text
X Y = J - M.                                      (5c)
```

Rows of `X` have weight q, rows of `Y` have weight a, and distinct rows in
either matrix meet in at most one position.  If t is the number of distinct
inside cut endpoints, reduction modulo two gives

```text
rank_F2(J+M) = t,
rank_F2(X), rank_F2(Y) >= t.                       (5d)
```

Indeed, the distinct rows `1+e_u` of `J+M` are independent because
`t<|S|`.  Endpoints with the same omitted point have identical rows in
`XY`, so their signed A-neighborhood differences lie in the kernel of
`Y^T`.  Since `t<=q-1` while both ambient matrix dimensions are much larger,
(5c)--(5d) do not improve the already closed binary-rank route.  They record
exactly where a future nonlinear point-location argument must enter.

Symmetry supplies one further universal parity.  Taking the quadratic form
of (5) against `1_S` gives

```text
2 e_A(S) = a|S| + |R intersect S|.
```

Since q is even and `|S|=qa+1` is odd,

```text
|R intersect S| = a  (mod 2).                 (5a)
```

This forces some self-location when a is odd, but does not by itself
contradict looplessness.

### The smallest shore as an edge-labelled graph

When `a=1`, the shore has size `q+1`.  Its non-D graph `H` has exactly q
edges.  Each `r in R` has exactly two A-neighbors in `S`; those two points
form one H-edge, uniquely labelled by `r`.  C4-freeness makes the q labels
distinct, and looplessness says that a label lying in `S` is not an endpoint
of its own edge.  Conversely, at `s in S`,

```text
deg_H(s) = deg_A(s,R) = 1 + d_s.              (5b)
```

Thus H has no isolated vertices, and its edge labels meet the self-location
parity `|R intersect S|` odd.  This exact partial structure is locally
feasible: take `H` to be the path on `q+1` vertices, identify one
non-endpoint path vertex with the label of a nonincident edge, and take the
other q-1 labels outside `S`.  Hence the `a=1` edge-label constraints alone
do not exclude a minimum cut.

## A q-clique is an isolated defect component

There is also a sharp incidence consequence useful for the Baer-type route.
If `C` is a q-clique in `D`, then for distinct `c,c' in C` the neighborhoods
`N_A(c)` and `N_A(c')` are disjoint.  They are q pairwise disjoint q-sets,
so they partition all `q^2` vertices.

Now take `y` outside `C`.  C4-freeness gives

```text
|N_A(y) intersect N_A(c)| <= 1
```

for every `c in C`.  The q cells `N_A(c)` partition the q neighbors of `y`,
so equality holds for every cell.  Hence every pair `(y,c)` has exactly one
common A-neighbor and no such pair is a D-edge.  There are no D-edges from
`C` to its complement, and therefore

```text
C is a whole K_q component of D.              (8)
```

In particular, connected `D` on `q^2>q` vertices has clique number at most
`q-1`.  This explains the boundary of the affine polarity control, whose
defect graph is a union of `K_q` components.  It generalizes the earlier
special observation that a clique closed neighborhood `N_D[x]` isolates,
but by itself it does not rule out smaller odd cycles or prove the desired
absolute-point theorem.

## Incidence-bottleneck energy

The cut theorem substantially strengthens the previously known nonvanishing
bound for the incidence bottleneck

```text
E = AD - (J-A) = qA - A^3 + (q-1)J.
```

Because `A` and `D` commute, row `x` is exactly

```text
E_x = A 1_{N_D[x]} - 1.
```

The closed D-neighborhood `S=N_D[x]` has size q.  Equation (1), with
`a=1`, therefore identifies its cut energy exactly:

```text
||E_x||^2 = |delta_D(N_D[x])|.                (9)
```

When `D` is connected this is a nonzero q-divisible-shore cut.  It is even
and at least `q-1`, hence at least q.  Summing (9) over all vertices gives

```text
||E||_F^2 >= q^3.                             (10)
```

This improves the bare integral zero-sum estimate `||E||_F^2 >= 2q^2` by
a factor `q/2`.  In local graph language, if `h_x` is the number of missing
D-edges among the `q-1` vertices of `N_D(x)`, then

```text
|delta_D(N_D[x])| = 2 h_x,
h_x >= q/2.                                   (11)
```

Thus every vertex centers at least `q/2` D-wedges whose endpoints have a
unique common A-neighbor.  Globally, if `t(D)` is the number of D-triangles,

```text
||E||_F^2 = q^2 (q-1)(q-2) - 6 t(D),
t(D) <= q^2 (q^2-4q+2) / 6.                  (12)
```

The spectral multiplier of `E` still vanishes on the defect eigenvalue
`mu=-1`, so (10) does not alone close the designated-sector trace problem.
It is, however, a load-bearing consumer of maximal defect connectivity and
the strongest current uniform energy bound for that incidence operator.

### Equality in the closed-neighborhood bound

The equality case in (9) is rigid.  Suppose
`|delta_D(N_D[x])|=q`, and put `y=E_x`.  Then `y` is an integral zero-sum
vector with `||y||^2=q`.  If `m=|supp(y)|`, then `m<=q`.  Moreover

```text
A y = L_D 1_{N_D[x]},
```

so `Ay` is supported on at most `2q` cut endpoints.  The C4 support count
used in (3) gives

```text
m(q-m+1) <= 2q.
```

For `q>=8`, this leaves only `m in {2,q-1,q}`.  The middle value is
impossible: `q-1` nonzero integer squares already sum to at least `q-1`,
and the next possible increase is three, not one.  If `m=2`, zero sum gives
`y=(a,-a)` and `q=2a^2`.  This can occur arithmetically only when the binary
exponent of q is odd.  But then `a` is even (as `q>=8`), whereas

```text
y_x = E_xx = deg_T(x)-1
```

is odd and nonzero because every T-degree is even.  Thus `m=2` is also
impossible.  Necessarily `m=q`, all nonzero entries are `+1` or `-1`, and
zero sum gives exactly `q/2` of each.  In particular

```text
|delta_D(N_D[x])| = q
  implies deg_T(x) in {0,2}.                  (13)
```

Equivalently, the q-neighbor occupancy of the closed D-star has exactly
`q/2` empty and `q/2` double cells, with every other cell occupied once.
If this balanced simple-occupancy pattern fails, the even cut has size at
least `q+2`.  No contradiction to the balanced pattern is currently known.

The balanced pattern cannot occur at every vertex.  Define the nonnegative
integer excess

```text
e_x = (|delta_D(N_D[x])| - q) / 2.
```

The number `t_x` of D-triangles through `x` is

```text
t_x = choose(q-1,2) - q/2 - e_x.
```

Since `sum_x t_x` is three times the number of D-triangles, reduction modulo
three (and `3` does not divide binary q) gives

```text
sum_x e_x = q  (mod 3).                       (14)
```

In particular, some row has cut energy strictly greater than q.  More
quantitatively, (9) and (14) sharpen (10) to

```text
||E||_F^2 >= q^3 + 2,  if q = 1 (mod 3),
||E||_F^2 >= q^3 + 4,  if q = 2 (mod 3).      (15)
```

For `q=2^k`, these are respectively the even-k and odd-k cases.  This strict
global residue still does not control how much E-energy lies in certified
residual spectral sectors.

## A near-Mantel q-set from a nontrivial minimum cut

Return to the nontrivial minimum-cut equality case and its associated q-set
`R`.  The inside cut degrees satisfy

```text
sum_u d_u = q-1,        0 <= d_u <= (q-2)/2.
```

Equation (7) and `|delta_D(R)|=q(q-1)-2e_D(R)` give

```text
e_D(R) = ((q-1)^2 - sum_u d_u^2)/2.
```

The capped square sum is maximized by
`((q-2)/2,(q-2)/2,1)`, and therefore

```text
e_D(R) >= q^2/4 - 1.                            (16)
```

Thus a nontrivial minimum cut manufactures a q-vertex D-subgraph within one
edge of the Mantel bound.  For binary `q>=16`, if `D[R]` is triangle-free,
its form is completely determined.  A triangle-free nonbipartite graph on
`2m` vertices has at most `m^2-m+1` edges (apply the standard shortest-odd-
cycle proof), so a triangle-free graph with at least `m^2-1` edges is
bipartite.  Its two part sizes then differ by at most two.  Consequently the
only possibilities at the top two edge counts are

```text
K_(m,m),
K_(m,m) minus one edge,
K_(m-1,m+1),               where m=q/2.          (17)
```

The first alternative would require `sum d_u^2` equal to the maximum minus
two.  But after the maximizing partition above, the second-largest capped
partition is `(m-1,m-2,2)`, whose square sum is lower by `q-6>2` when
`q>=16`.  Hence `e_D(R)=m^2-1`, and equality in (16) forces

```text
(d_u : d_u>0) = (m-1,m-1,1).                  (18)
```

The corresponding common-A-neighbor block sizes on `R` are `(m,m,2)`.
They exhaust all non-D pairs of `R`, with no pair repeated by C4-freeness.
The two m-blocks in fact partition `R`.  They can intersect in at most one
point.  If they intersected once, the one point of `R` outside their union
would have only the size-two block as a possible non-D partner, hence would
have D-degree at least `q-2` inside `R`.  This is impossible in either
bipartite graph in (17), whose largest part has size `m+1<=q-3` for
`q>=16`.

This pair-block decomposition excludes `K_(m-1,m+1)`: its non-D graph is
`K_(m-1) disjoint-union K_(m+1)`, and two edge-disjoint m-cliques plus one
edge cannot cover the `K_(m+1)` component.  Therefore

```text
D[R] triangle-free
  implies D[R] = K_(q/2,q/2) minus one edge.   (19)
```

Moreover, the two q/2 common-neighbor blocks are its bipartition classes,
and the size-two block covers the unique missing cross edge.  The excluded
`q=8` square-sum gap is exactly two, so this argument deliberately makes no
order-64 endpoint claim.  In the remaining general case `D[R]` contains a
triangle.  That branch is quantitatively nontrivial: Theorem 1 of Erdos,
*On the number of triangles contained in certain graphs*, Canadian
Mathematical Bulletin 7 (1964), DOI `10.4153/CMB-1964-007-3`, says that an
n-vertex graph with `floor(n^2/4)-ell` edges and a triangle has at least
`floor(n/2)-ell-1` triangles.  If necessary, delete edges other than a fixed
triangle down to the `q^2/4-1` threshold and apply the theorem to obtain

```text
D[R] contains a triangle
  implies t(D[R]) >= q/2-2.                    (20)
```

Each such triangle is a triple of vertices with pairwise disjoint
A-neighborhoods.  The bound grows with q, but the triangles may form a book
around one D-edge; the resulting neighborhood packing still fits inside
`q^2` vertices.  Thus neither the near-bipartite branch nor (20) is yet
contradictory.

### Two-wing decomposition in the near-bipartite branch

The exact branch in (19) has a useful full-incidence form.  Write its parts
as `R=L disjoint-union M`, with `|L|=|M|=m=q/2`, and let `(a,b)` be the
unique missing cross D-edge.  The common-neighbor blocks of sizes `(m,m,2)`
have centers `alpha,beta,gamma` and are respectively

```text
N_A(alpha) intersect R = L,
N_A(beta)  intersect R = M,
N_A(gamma) intersect R = {a,b}.               (21)
```

Every other A-neighborhood meets at most one of `L,M`, and meets that part
at most once.  Indeed, two points in the same part already have their unique
common neighbor `alpha` or `beta`, while every cross pair is a D-edge except
`(a,b)`, whose unique common neighbor is `gamma`.

Consequently, if

```text
X_L = union_{l in L} N_A(l),
X_M = union_{r in M} N_A(r),
```

then the q-neighborhoods in either union share only their common pole and
are otherwise disjoint.  Hence

```text
|X_L| = |X_M| = 1 + m(q-1),
X_L intersect X_M = {gamma}.
```

The remaining set

```text
Z = V \ (X_L union X_M)
```

has exactly `q-1` vertices and is A-anticomplete to all of `R`.  More
finely, the `(q-1)`-sets `N_A(l)\{alpha}`, for `l in L`, are pairwise
disjoint cells; the analogous M-cells are pairwise disjoint, and the only
cross-cell intersection is `gamma` between the cells indexed by `a,b`.

This partition is aligned with the original minimum cut, not merely with
`R`.  The equation `A 1_R-1=L_D1_S` makes the zero-occupancy vertices
exactly the outside endpoints of that cut.  Hence

```text
Z is disjoint from S,
each z in Z has exactly one D-neighbor in S,
alpha,beta,gamma lie in S
  with cut degrees m-1,m-1,1.                 (22)
```

The general punctured parallel classes above specialize here to q-1 classes
whose omitted points have multiplicities

```text
(m-1,m-1,1) at (alpha,beta,gamma).             (23)
```

The three poles are also an explicit D-vertex separator for this branch.
Put `W={alpha,beta,gamma}`.  All D-edges of the original cut meet `W`, so
`D-W` separates `S\W` from `V\S`.  Degree counting gives

```text
|delta_D(S\W)| = 2(q-1-e_D(W)).                (24)
```

The shore `S\W` has residue `q-2` modulo q, and (2) therefore makes the
right side at least `2q-4`; hence `e_D(W)<=1`.  This is sharp from the
incidence description: `alpha,gamma` have common A-neighbor `a`, and
`beta,gamma` have common A-neighbor `b`, so neither pair is a D-edge.  Only
`alpha,beta` can be a D-edge.

If it is, (24) attains equality `2q-4`, and equality in the integer variance
bound says

```text
A 1_W = 1_R + 1_K,       |K|=2q,              (25)
```

where `K intersect R={a,b}`.  If `alpha,beta` is not a D-edge, its unique
common A-neighbor `c` lies outside `R`, the cut is `2q-2`, and the analogous
near-equality profile is

```text
A 1_W = 1_R + 1_K + 1_c,
|K|=2q-1, c in K, K intersect R={a,b}.         (26)
```

Equations (25)--(26) exactly restate the three pairwise pole intersections;
they do not exclude the separator.  Four-vertex-connectivity of D would
suffice to eliminate this triangle-free minimum-cut branch; the branch is
one explicit candidate obstruction beyond the three-vertex-connectivity
proved below.

This is the exact nonlinear filler problem left by the triangle-free
minimum-cut branch.  The available degree and pair-capacity counts fit
inside the two wings and `Z`; no repeated common neighbor or D-disconnection
follows from the cell sizes alone.

### The full residue-(q-2,q-1) three-separator frontier

The pole separator above belongs to a slightly larger variance family that
is useful to state explicitly.  Let `W` be a three-vertex separator for
which `D-W` has two components `X,Y` with

```text
|X| = q a + q-2,       |Y| = q b-1.
```

The two cut sizes sum to `3(q-1)-2e_D(W)`.  Their residue lower bounds are
`2q-4` and `q-1`, and all excesses are even.  Consequently exactly the
following three cases remain:

```text
e_D(W)=1:  (delta_D(X),delta_D(Y))=(2q-4,q-1),
e_D(W)=0:  (delta_D(X),delta_D(Y))=(2q-2,q-1),
e_D(W)=0:  (delta_D(X),delta_D(Y))=(2q-4,q+1). (B1)
```

The equality and near-equality degree profiles make the distinction more
concrete.  In the first two cases the `q-1` shore is a minimum cut, so for a
q-set `R`

```text
A 1_Y = b 1 - 1_R.
```

Complementing across `W`, equality for the `q-2` shore gives

```text
A 1_W = 1_R + 1_K,       |K|=2q,
```

whereas excess two gives one of the two mirror profiles

```text
A 1_W = 1_R + 1_K + 1_c,
|K|=2q-1, c in K,
A 1_W = 1_R + 1_K - 1_c,
|K|=2q+1, c in R, c notin K.
```

The first and the positive-sign excess profile are the ambient versions of
(25)--(26).  The negative-sign profile has `(A 1_W)_c=0` at a point
`c in R`, so it is excluded in the near-bipartite branch by (21), whose
three pole traces cover every point of `R`.  The same trace argument further
forces `K intersect R={a,b}` and locates the positive-sign spike in (26).

The third line of (B1) is genuinely dual.  Equality on `X` gives a `2q`-set
`K`.  If `t=A 1_Y-b 1`, then

```text
sum_v t_v=-q,       sum_v t_v^2=q+2,
```

so `sum_v t_v(t_v+1)=2`.  There are exactly two integer profile types:

```text
A 1_Y = b 1 - 1_R - 1_c,   |R|=q-1, c in R,
A 1_Y = b 1 - 1_R + 1_c,   |R|=q+1, c notin R.
```

Complementing gives, respectively,

```text
A 1_W = 1_K + 1_R + 1_c,
A 1_W = 1_K + 1_R - 1_c,   |K|=2q.           (B2)
```

In the second line nonnegativity forces `c in K`.

Unlike the first two cases, (B2) supplies no associated q-set to which the
minimum-cut Mantel bound applies.  Hence the two-wing pole analysis covers
all pattern-B profiles with a minimum `q-1` shore, but not this last dual
near-mincut escape.  Any general four-connectivity argument must either
exclude (B2) separately or recover a q-set from additional point-location
information.

There is nevertheless a sharp first location constraint in the dual case.
Since `e_D(W)=0`, every pair of vertices of `W` has exactly one common
`A`-neighbor.  Therefore

```text
sum_v binom((A 1_W)_v,2)=3.                  (B3)
```

For the omitted negative-sign excess profile with minimum `Y`, its forced
conditions `c in R`, `c notin K` make the value at `c` zero.  Substitution
in (B3) gives `|K intersect R|=3`.  In the near-bipartite specialization it
is already impossible because the pole traces have positive incidence at
every point of `R`.

For the negative-spike line of (B2), where `c in R`, substituting the
indicator profile into (B3) gives

```text
|K intersect R| + 1_(c in K) = 2.            (B4-)
```

For the positive-spike line, `c in K` and `c notin R`; the subtraction at
`c` makes `(A 1_W)_c=0`, while every point of `K intersect R` has value two.
Thus

```text
|K intersect R| = 3.                         (B4+)
```

The equality profile of the `q-2` shore also has a useful componentwise
form.  From

```text
A 1_X = (a+1)1 - 1_K
```

and `L_D=A^2-J`, one obtains

```text
L_D 1_X = 2 1 - A 1_K.                       (B5)
```

There are no `D`-edges from `X` to `Y`, so (B5) says

```text
deg_A(y,K)=2                    for every y in Y,
deg_A(x,K)=2-deg_D(x,W)         for every x in X,
deg_A(w,K)=2+deg_D(w,X)         for every w in W.  (B6)
```

In particular the whole large opposite component is a two-fold incidence
cover of `K`, while only two or three points of `K` can lie in the spike set
`R`.  These signed-intersection and two-cover conditions are absent from an
abstract cut-capacity model and are the appropriate next input for excluding
the dual escape.

In fact the negative-spike subtype is impossible.  Its centered profile
gives

```text
L_D 1_Y = 1 - A 1_R - A 1_c.
```

For `x in X` the left side is zero, while for `y in Y` it is the nonnegative
number `deg_D(y,W)`.  Since `c in R`, any `A`-edge from either `x` or `y` to
`c` contributes once through `A 1_R` and once again through `A 1_c`, making
the right side at most `-1`.  Thus `c` has no `A`-neighbor in `X union Y`.
All its `A`-neighbors would have to lie in the three-element set `W`,
contradicting `deg_A(c)=q` for `q>=4`.

Consequently the only dual pattern-B escape is the positive-spike profile

```text
A 1_Y = b 1 - 1_R + 1_c,
|R|=q+1, c notin R,
A 1_W = 1_K + 1_R - 1_c,
|K|=2q, c in K, |K intersect R|=3.            (B7)
```

In particular `(A 1_W)_c=0`: the exceptional point `c` is
`A`-anticomplete to the separator.  This reduces the previously two-pronged
dual filler problem to the single signed profile (B7).

The remaining profile has an exact three-wing core.  Put
`P=K intersect R`, so `|P|=3`.  For `w in W`, let

```text
m_w=deg_D(w,X),       n_w=deg_D(w,Y).
```

Since `D[W]` is empty, `m_w+n_w=q-1`.  Equations (B5) and the positive-spike
cut flow give

```text
deg_A(w,K)=2+m_w,     deg_A(w,R)=1+n_w.
```

Thus the two sets account for `q+2` incidences among only q neighbors of
`w`, so `deg_A(w,P)>=2`.  On the other hand every point of `P` has
`(A 1_W)_v=2` by (B7), whence

```text
sum_(w in W) deg_A(w,P)=6.
```

Therefore every `w` meets exactly two points of `P`, and every point of `P`
meets exactly two vertices of `W`.  The resulting bipartite incidence graph
is a six-cycle.  In particular the three points of `P` are the three
distinct pairwise common `A`-neighbors of the vertices of `W`; there are no
other intersections among the three separator neighborhoods.  Moreover

```text
N_A(w) subset K union R                       (B8)
```

for every `w in W`, with the two points of `P` counted in both sides.
More precisely, `K\(P union {c})` has size `2q-4` and every one of its
points has exactly one neighbor in `W`; these points split into three wings
of sizes `m_w`.  Likewise `R\P` has size `q-2`, every one of its points has
exactly one neighbor in `W`, and it splits into three wings of sizes
`n_w-1`.  Thus

```text
K\(P union {c}) = disjoint-union_(w in W) K_w,  |K_w|=m_w,
R\P             = disjoint-union_(w in W) R_w,  |R_w|=n_w-1. (B8')
```

Together with the six-cycle on `W union P`, this accounts for every point
of `N_A(W)` exactly.

There is also a first numerical restriction on the component location.
Because `(A 1_Y)_c=b+1`, `(A 1_W)_c=0`, and `a+b=q-1`, regularity gives
`deg_A(c,X)=a`.  For every `x in N_A(c) intersect X`, the positive-spike
flow equation on `X` gives `deg_A(x,R)=2`.  Distinct such incidences use
distinct pairs `(c,r)` by C4-freeness.  Hence

```text
2a <= |R|=q+1,
```

and, since q is even,

```text
a <= q/2.                                    (B9)
```

The componentwise flow equations also bound individual attachments.  From
(B6),

```text
deg_D(x,W) <= 2                         for x in X.
```

For `y in Y`, the positive-spike equation reads

```text
deg_D(y,W)=1-deg_A(y,R)+1_(y in N_A(c)),
```

and hence

```text
deg_D(y,W) <= 1+1_(y in N_A(c)).              (B10)
```

Thus only the `b+1=q-a` neighbors of `c` in `Y` can attach to two separator
vertices.

At the endpoint `a=0`, the first bound is sharp everywhere.  Indeed
`|X|=q-2` and the cut has `2q-4=2|X|` edges, so every `x in X` has exactly
two neighbors in `W`.  Its remaining `q-3` defect neighbors exhaust the
other vertices of `X`, giving

```text
D[X] = K_(q-2).                                (B11)
```

The `A`-neighborhoods of this clique are pairwise disjoint and have union
size `q(q-2)`; (B6) says that their complement is exactly the `2q`-set `K`.
Accordingly the smallest surviving parameter has been reduced to a rigid
near-maximal defect clique with a two-edge attachment at every vertex.

There is an exact matching inside this endpoint.  For `w in W`, let `X_w`
be the vertices of `X` whose unique missing `D`-attachment is `w`.  Since
every `x in X` attaches to the other two separator vertices,

```text
|X_w|=(q-2)-m_w=n_w-1=|R_w|.                 (B12)
```

The pair `(x,w)` is a `D`-nonedge and therefore has a unique common
`A`-neighbor.  It cannot lie in `K`, because `K` is `A`-anticomplete to
`X`; among the neighbors of `w`, (B8') then forces it to lie in `R_w`.
Distinct vertices of the defect clique `X` have disjoint `A`-neighborhoods,
so these common neighbors are distinct.  Cardinality in (B12) upgrades the
map to a bijection

```text
X_w  <-->  R_w.                               (B13)
```

Thus each of the three missing-attachment color classes is paired exactly
with its opposite R-wing.  In particular every `x in X` has exactly one
`A`-neighbor in `N_A(W)`, namely its matched point in an R-wing.  Its other
`q-1` neighbors lie outside `N_A(W)`, and these outside parts are disjoint as
`x` varies because `X` is a defect clique.  Now

```text
|V\N_A(W)| = q^2-(3q-3)=q^2-3q+3,
(q-2)(q-1)=q^2-3q+2.
```

The exceptional point `c` lies outside `N_A(W)` and belongs to `K`, hence
is `A`-anticomplete to `X`.  It is therefore the unique unoccupied point:

```text
V\(N_A(W) union {c})
  = disjoint-union_(x in X) (N_A(x)\N_A(W)),
|(N_A(x)\N_A(W))|=q-1.                       (B14)
```

So the endpoint branch is an exact punctured parallel class rooted at the
near-maximal defect clique.

Finally, symmetry of `A` gives a location balance that is invisible in the
unsigned wing sizes.  Count the `A`-edges between `X` and `Y` from the two
sides, using

```text
A 1_Y=(b 1)-1_R+1_c,
A 1_X=(a+1)1-1_K.
```

Writing `k_Y=|K intersect Y|`, `r_X=|R intersect X|`, and
`c_X=1_(c in X)`, one obtains

```text
b|X|-r_X+c_X=(a+1)|Y|-k_Y,
k_Y-r_X+c_X=2b-a-1=2q-3a-3.                 (B15)
```

Since `|K|=2q`, this is equivalently

```text
|K intersect (X union W)|=3a+3-r_X+c_X.      (B16)
```

There are also uniform location parities.  On `X`,

```text
deg_A(x,X)=a+1-1_(x in K).
```

Because `|X|=q(a+1)-2` is even, the handshake lemma gives

```text
|K intersect X| = 0 mod 2.                   (B16a)
```

On `Y`, the analogous degree sum is
`b|Y|-|R intersect Y|+1_(c in Y)`.  Here `|Y|=qb-1` is odd and
`b=q-1-a` has parity `a+1`, so

```text
|R intersect Y| + 1_(c in Y) = a+1 mod 2.    (B16b)
```

These hold for the full positive-spike profile, not only at `a=0`.

At the endpoint `a=0`, at most four points of `K` can lie in `X union W`,
and necessarily `r_X<=3+c_X`.  Since `c in K`, at most three of those
points are different from `c`; equality four requires `c in X` and
`r_X=0`.  Thus almost the whole two-fold cover `K`
is located in the opposite component `Y`; any realization of the punctured
parallel class must also satisfy this strong self-location constraint.

The exceptional point produces a second exact matching at this endpoint.
Here `b=q-1`, so `(A 1_Y)_c=q`; all q neighbors of `c` lie in `Y`.  By
(B6), every `y in Y` has exactly two neighbors in `K`.  For
`y in N_A(c)`, one is `c in K`, leaving a unique other point
`phi(y) in K\{c}`.  If two distinct neighbors of `c` had the same image,
they would form a 4-cycle with `c` and that image.  Hence

```text
phi : N_A(c) --> K\{c}
```

is injective and its image `Q` has size q.  Equivalently, the q paths

```text
c -- y -- phi(y),       y in N_A(c),          (B17)
```

match `N_A(c)` to a q-subset of `K\{c}`.  Combining this with (B16), at
least `q-4` points of `Q` lie in `Y`.  Thus the endpoint contains two
simultaneous exact matchings: the three `X_w <--> R_w` wing matchings and
this exceptional-point matching into the overwhelmingly Y-located set K.

This matching exhausts all common-neighbor incidences between `c` and
`K\{c}`.  Indeed every common neighbor lies in `N_A(c) subset Y`, and each
such point has only the two K-neighbors `c` and `phi(y)`.  Hence the q points
of `Q` are exactly the K-points that are D-nonneighbors of `c`.  The other
`q-1` points exhaust its defect degree:

```text
N_D(c)=K\({c} union Q).                       (B17')
```

In particular `c` cannot lie in `X` for binary `q>=8`.  If it did, the
defect clique (B11) would give

```text
X\{c} subset N_D(c) subset K,
```

so `|K intersect (X union W)|>=q-3` from those vertices, and the two
separator attachments of `c` are also in `N_D(c) subset K`, raising the
lower bound to `q-1`; including `c in K intersect X` raises it to q.  This
contradicts the upper bound four from (B16).
Thus at the endpoint

```text
c in Y union W.                               (B17'')
```

The two surviving locations have sharply bounded attachments.  If
`c in Y`, then (B10), with no loop at `c`, gives

```text
deg_D(c,W) <= 1.                              (B17Y)
```

If `c in W`, write `m_c=deg_D(c,X)`.  The set in (B17') contains `c` itself
and all `m_c` X-neighbors of `c`, while (B16) puts at most `3-r_X` K-points
outside `Y`.  Therefore `1+m_c<=3-r_X`.  Minimality of the separator gives
`m_c>=1`, so

```text
m_c in {1,2},
deg_D(c,Y)=q-1-m_c in {q-2,q-3},
m_c=2 implies r_X=0.                          (B17W)
```

Thus a separator-located exceptional point has an extremely lopsided pair
of wings, while a Y-located one has at most one boundary edge.

Parity makes the W-location exact.  As below, the handshake lemma in
`A[X]` makes `k_X=|K intersect X|` even.  All `m_c` defect neighbors of `c`
in `X` belong to `K` by (B17'), so `k_X>=m_c`; also `c in K intersect W`.
If `m_c=2`, (B17W) gives `r_X=0`, while (B16) says
`k_X+k_W=3`; hence `(k_X,k_W)=(2,1)`.  If `m_c=1` and `r_X=1`, the same
equation would give `k_X+k_W=2`, impossible because even `k_X>=2` and
`k_W>=1`.  Therefore this case has `r_X=0` as well and again
`(k_X,k_W)=(2,1)`.  In both cases

```text
R intersect X = empty,
|K intersect X|=2,
K intersect W={c}.                            (B17W')
```

In particular the whole set `R` is located in `Y union W` in this branch.

Since `deg_A(x,X)=1-1_(x in K)`, the induced graph `A[X]` is consequently
a perfect matching on `q-4` vertices together with exactly two isolated
vertices, namely `K intersect X`.  When `m_c=2` both isolates are the
X-neighbors of `c` in D; when `m_c=1`, one is that D-neighbor and the other
lies in `Q`.

The two isolates are also matched exactly to the other separator vertices
in `A`.  Since `R intersect X` is empty, (B7) read on `X` gives

```text
deg_A(x,W)=1_(x in K).
```

Thus only the two points of `K intersect X` meet `W`, once each.  Conversely
the profile `A 1_X=1-1_K` read on `W` gives no X-neighbor at
`c in K intersect W` and exactly one at each point of `W\{c}`, because
`K intersect W={c}`.  Therefore these two A-edges form a bijection

```text
K intersect X  <-->  W\{c}.                  (B17W'')
```

Consequently `A[X union W]` consists of the perfect matching on the
`q-4` nonisolated X-points, this two-edge cross matching, the isolated
vertex `c`, and possibly the single edge between the other two vertices of
`W`.  Here isolation of `c` inside `W` uses the signed value
`(A 1_W)_c=0` from (B7), not merely its membership in `K`.

The R-location is then exact up to that last possible edge.  Since
`P=K intersect R`, `K intersect W={c}`, and `c notin R`, while
`R intersect X` is empty, all three points of `P` lie in `Y`.  On `W`, the
profile (B7) reads

```text
deg_A(w,W)=1_(w in R)       for w in W\{c},
deg_A(c,W)=0.
```

Only the edge between the two points of `W\{c}` can occur, so

```text
R intersect W = empty       if A[W] is empty,
R intersect W = W\{c}       if A[W] has that edge.          (B17W''')
```

In particular `R\(P union W)` lies entirely in `Y`; the three pair-centers
`P` themselves lie there as well.

The wing indexed by `c` has no W-located exception: a point of
`R intersect W`, when present, has its unique W-neighbor at the other point
of `W\{c}`, since `c` has no A-neighbor in W.  Hence `R_c subset Y`.
For `r in R_c`, the Y-profile gives `deg_A(r,Y)=q-2`, while (B13) supplies
its unique matched point `x in X_c` and the wing definition supplies its
unique W-neighbor `c`.  These are therefore its only two A-neighbors outside
Y.  Equivalently,

```text
X_c <--> R_c
```

is precisely the unique-common-neighbor bijection for the D-nonadjacent
pairs `(c,x)`, `x in X_c`.  More generally, for any `r in R_w intersect Y`,
its only outside-Y neighbors are `w` and its matched point in `X_w`.
Each `p in P` likewise has exactly its two incident W-vertices outside Y
and no X-neighbor (because `P subset K`).                 (B17W'''')

The Y-location also carries a near-complete transversal.  If `c in Y`,
then every `x in X` is a D-nonneighbor of `c`, because `X,Y` are different
components of `D-W`.  Let `psi(x)` be their unique common A-neighbor.
Distinct `x,x' in X` have disjoint A-neighborhoods by (B11), so the centers
are distinct.  Hence

```text
psi : X --> N_A(c)
```

is injective, with image size `q-2`; exactly two of the q neighbors of `c`
are not used as centers for X.  Moreover, for the matching `phi` in (B17),

```text
x in K  iff  phi(psi(x))=x.                  (B17Y')
```

Indeed `psi(x)` is adjacent to `c`; its only other K-neighbor is
`phi(psi(x))`, so it equals `x` precisely when `x in K`.  Thus the small
set `K intersect X` is exactly the fixed-point locus where the exceptional
matching lands back on the clique point whose cell contains its center.

This transversal is actually onto the non-K part of `N_A(c)`.  Since
`c in Y`, (B6) gives `deg_A(c,K)=2`.  The two neighbors of `c` not used by
`psi` are A-anticomplete to `X` (otherwise they would be the unique center
of `c` with that X-point), and at `a=0` the complement of
`union_(x in X) N_A(x)` is exactly `K`.  Hence they are precisely the two
K-neighbors of `c`, and

```text
psi : X  <-->  N_A(c)\K                      (B17Y'')
```

is a bijection.  Put `theta=phi o psi`.  For every `x`, the point `psi(x)`
is adjacent to `c,x,theta(x)`; when these are distinct it is the unique
common A-neighbor of each pair.  If `theta(x)` also lies in `X`, the defect clique forces
`theta(x)=x`; conversely this equality is equivalent to `x in K` by
(B17Y').  Therefore

```text
theta(X) intersect X = K intersect X,
theta fixes exactly K intersect X.            (B17Y''')
```

The two holes of the injection `theta:X-->Q` are the `phi`-images of the
two points in `N_A(c) intersect K`.

The fixed-point locus has even size.  At `a=0`, the profile on `X` reads

```text
deg_A(x,X)=1-1_(x in K).
```

The handshake lemma and even order `|X|=q-2` therefore give
`|K intersect X|=0 mod 2`.  In the present `c in Y` branch, (B16) gives
`|K intersect X|<=3`.  Combining this with (B17Y''') yields

```text
|Fix(theta)|=|K intersect X| in {0,2}.        (B17Y'''')
```

Thus neither one nor three of the clique cells can be fixed by the
exceptional-point transversal.

The matching in fact closes for every `a`.  The point `c` has `a` neighbors
in `X` and `q-a` in `Y`.  Each Y-neighbor has exactly two K-neighbors by
(B6), one of which is `c`, so it supplies one other K-target.  For
`x in N_A(c) intersect X`, (B6) says

```text
deg_A(x,K)=2-deg_D(x,W).
```

Since `c in K` is already one such neighbor, `deg_D(x,W)` is zero or one;
the point `x` supplies a second K-target exactly in the zero case.  Let h
be the number of these zero-attachment X-neighbors.  All targets are
distinct by C4-freeness, and every common neighbor of `c` with a point of
`K\{c}` arises this way.  Thus exactly `q-a+h` points of `K\{c}` are
D-nonneighbors of `c`, leaving

```text
(2q-1)-(q-a+h)=q+a-h-1
```

D-neighbors of `c` already inside K.  This cannot exceed its total defect
degree `q-1`; hence `h>=a`.  Since `h<=a`, equality holds.  Therefore every
point of `N_A(c) intersect X` has zero W-attachments, all q neighbors of
`c` supply a distinct second K-target, and

```text
phi : N_A(c) --> Q subset K\{c},   |Q|=q,
N_D(c)=K\({c} union Q)                       (B18)
```

for every `a`, not only at the endpoint.  Finally (B16) gives

```text
|K intersect (X union W)| <= 3a+4,
```

so at least `max(0,q-3a-4)` targets of Q lie in `Y`.  This upgrades the
former partial Y-matching to an exact global matching and makes the
exceptional neighborhood completely attachment-free on its X side.

It also excludes the X-location through the lower third of the range.  If
`c in X`, then component separation puts all `q-1` defect neighbors of `c`
in `X union W`.  By (B18) they lie in K, and `c` itself is another point of
`K intersect (X union W)`.  Comparing with (B16) gives

```text
q <= |K intersect (X union W)| <= 3a+4,
a >= ceil((q-4)/3).                           (B19)
```

Thus `c notin X` whenever `3a+4<q`; the endpoint exclusion (B17'') is the
first case of this uniform location bound.

The Y-location has a complementary lower bound.  If `c in Y`, then (B10)
gives `n_c=deg_D(c,W)<=1`, and there are no D-edges from `c` to `X`.
Equation (B18) therefore puts `c` and the `q-1-n_c` internal-Y defect
neighbors of `c` in `K intersect Y`, so

```text
|K intersect Y| >= q-n_c.
```

Substitution in (B15), where `c_X=0`, yields

```text
|R intersect X| >= 3a-q+3-n_c >= 3a-q+2.     (B20)
```

If `c` has no W-attachment the first lower bound improves by one.  Thus at
large a the Y-location forces a correspondingly large part of R to sit in
the opposite component X.

Finally suppose `c in W`, and write `m_c=deg_D(c,X)`.  Minimality of the
separator gives `m_c>=1`.  The point `c` and its `m_c` X-neighbors in D all
belong to `K intersect (X union W)` by (B18), while (B16), now with
`c_X=0`, gives

```text
1 <= m_c <= 3a+2-|R intersect X|.             (B21)
```

Thus the exceptional separator vertex has only O(a) attachments into the
q-2 residue component; the endpoint `a=0` specializes to the exact
`m_c in {1,2}` classification in (B17W).

The first non-endpoint slice has a useful intrinsic form.  At `a=1`, the
X-profile says

```text
deg_A(x,X)=2-1_(x in K).
```

Thus `A[X]` has maximum degree two, with degree-one vertices exactly
`K intersect X`.  By (B16a) their number is even, so

```text
A[X] is a disjoint union of cycles and |K intersect X|/2 paths,
and the path endpoints are exactly K intersect X.         (B22)
```

This path-cycle decomposition is the `a=1` analogue of the matching plus
two isolates obtained at the endpoint, and is the next location-sensitive
object to couple to the W-attachment fibers.

For binary `q>=8`, (B19) excludes `c in X` on this slice because
`3a+4=7<q`.  If instead `c in W`, then `c in K intersect W` and minimality
gives at least one X-neighbor in D.  By (B18) those X-neighbors lie in
`K intersect X`, whose size is even.  Equation (B16) becomes

```text
|K intersect X|+|K intersect W|=6-|R intersect X|.
```

Since `|K intersect W|>=1`, the only possibilities are

```text
|K intersect X| in {2,4},
|R intersect X| <= 3,
1 <= deg_D(c,X) <= |K intersect X| <= 4.       (B23)
```

Thus the separator-located `a=1` branch has only two possible numbers of
path endpoints and at most four X-attachments at the exceptional pole.

There is also a parity coupling between those paths and the c-attachment
fiber.  Put

```text
M_c={x in X : cx is not an edge of D}.
```

Then `X\M_c=N_D(c) intersect X` has size `m_c` and lies in K by (B18),
while the endpoints in `K intersect M_c` lie in Q.  Hence the path endpoints
split exactly as

```text
|K intersect (X\M_c)|=m_c,
|K intersect M_c|=|K intersect X|-m_c.        (B24)
```

Sum the degrees of `A[X]` over `M_c`.  Since the degrees are two except at
the K-endpoints, the parity of the A-cut from `M_c` to `X\M_c` is

```text
e_A(M_c,X\M_c) = |K intersect M_c| = m_c mod 2,
```

using even `|K intersect X|`.  Finally `N_A(c) intersect X` is a singleton
at `a=1`; call it `u`.  The uniform conclusion after (B18) puts `u in M_c`.
If `u` had an A-neighbor in `X\M_c`, it would be a common A-neighbor of c
and a D-neighbor of c, impossible.  Thus all A[X]-neighbors of `u` remain
inside `M_c`.  This is the first edge-level constraint linking the
path-cycle decomposition to a separator attachment fiber.

The whole separator complement is in fact routed through the three wings;
this part holds for every `a`, not only on the first non-endpoint slice.
For `x in X`, put `t_x=deg_D(x,W)`.  The componentwise equations (B6) and
the two-walk identity give

```text
deg_A(x,K)=2-t_x.
```

Indeed, the number of two-edge walks from `x` to `W` is `3-t_x`: each of
the `3-t_x` non-D pairs `(x,w)` has exactly one common A-neighbor, and the
`t_x` D-pairs have none.  On the other hand (B7), summed over the neighbors
of `x`, says that the same number is

```text
sum_(z in N_A(x)) deg_A(z,W)
  = deg_A(x,K)+deg_A(x,R)-1_(x in N_A(c))
  = 3-t_x.                                      (B25)
```

In particular (B25) recovers

```text
deg_A(x,R)=1+1_(x in N_A(c)).
```

More importantly, it is an exact color-preserving routing rule: for
each missing `D`-attachment `xw`, its unique common neighbor lies in the
`K/R` wing incident with `w`, and these are all the `K/R`-neighbors of
`x`, except for `c` itself when `x in N_A(c)`.

This is particularly sharp when `t_x=2`.  Such a point cannot be the
unique vertex `u=N_A(c) intersect X`, because (B18) gives `t_u=0`; it has
no K-neighbor by (B6), exactly one R-neighbor, and (B25) forces that point
to lie in the unique wing `R_w` indexed by the missing attachment `w`.
Thus every twice-attached X-point is assigned canonically to the opposite
R-wing.  More generally the one- and zero-attachment X-points route their
two and three missing colors, respectively, through the corresponding
wing incidences (a point of `P` simultaneously carries its two incident
colors).  This extends the endpoint bijections (B13) to a fiberwise routing
law on the first non-endpoint slice.

The attachment multiplicities are consequently unbalanced by exactly two.
Let

```text
N_i={x in X : deg_D(x,W)=i},   n_i=|N_i|   (i=0,1,2).
```

Here `|X|=2q-2` and the X-side of the defect cut has size `2q-4`, so

```text
n_0+n_1+n_2=2q-2,
n_1+2n_2=2q-4,
n_0=n_2+2.                                  (B26)
```

Thus there are always at least two attachment-free X-points (one of them
is `u`), and the attachment-free class exceeds the twice-attached class by
exactly two.  Equivalently, the K-degrees in (B25) partition all `2q`
points of K into fibers of sizes `2,1,0` over `N_0,N_1,N_2`: indeed
`A 1_X=2 1-1_K` says independently that every point of K has exactly one
X-neighbor.  This couples the wing routing to a global exact cover, rather
than merely bounding the number of each local attachment type.

The routing law also resolves each separator color into an exact mixture of
singletons and pairs.  Fix `w in W` and let

```text
S_w={x in X : xw is not an edge of D}.
```

At `a=1`, every point of K has exactly one X-neighbor.  Every point of
`R\P` has exactly two X-neighbors, because `A 1_X=2 1-1_K`, while each
point of `P=K intersect R` has exactly one.  Consequently the centers in
the w-wing route the set `S_w` as follows:

```text
K_w:                     m_w singleton fibers,
R_w:                 n_w-1 disjoint two-point fibers,
{p in P : p adjacent w}:     two singleton fibers.        (B27)
```

These fibers are disjoint: an X-point in two fibers for the same color
would give the non-D pair `(x,w)` two common A-neighbors.  They are also
exhaustive by (B25).  Numerically,

```text
|S_w|=|X|-m_w=2q-2-m_w
     =m_w+2(n_w-1)+2,
```

where `m_w+n_w=q-1`.  Hence each `R_w` is canonically a matching of
two-element subsets of the missing-w class, while `K_w` and the two
incident P-points account for all remaining singleton routes.  In
particular the three wing colors impose simultaneous partial matchings on
the same path-cycle vertex set `X`; any surviving realization must make
these colored matchings compatible with `A[X]` and with the endpoint split
in (B24).

Their uncolored union already has an exact normal form.  The three points
of P have three distinct X-neighbors.  Indeed any two points of P share
one of their two W-neighbors in the six-cycle (B8); if they also shared an
X-neighbor, that X-point and the shared W-point would have two common
A-neighbors.  Let `U_P subset X` be this three-point recipient set.

Similarly, no unordered pair of X-points can be a two-fiber of two
different points of `R\P`, since those would be two common A-neighbors of
the pair.  Thus the `R_w` fibers in (B27), over all three colors, form a
simple edge-disjoint union `M_R` with `q-2` edges.  By (B25), every
`x != u` has exactly one R-neighbor, whereas `u` has two; a point is
incident with an edge of `M_R` once for each of those R-neighbors outside
P.  Also `u` can receive at most one P-point by the preceding paragraph.
Consequently exactly one of the following holds:

```text
u in U_P:      M_R is a matching with exactly two uncovered X-points;
u notin U_P:   M_R is a matching together with one length-two path
               whose middle vertex is u, and has three uncovered points.
                                                               (B28)
```

In the second line the two R-neighbors of `u` lie in different wings:
two fibers of the same color would give `(u,w)` two common neighbors.
Thus (B28) is also properly three-colored by the separator wings.  This
near-perfect matching is forced on the same vertex set on which `A[X]`
is the path-cycle graph (B22), giving a compact two-factor-style object for
the remaining `a=1` compatibility problem.

There is a first direct compatibility condition between these two graphs.
If `xy` is an edge of `M_R`, its R-center is already a common A-neighbor of
`x` and `y`.  Therefore `x` and `y` cannot have a common neighbor in X as
well.  Equivalently,

```text
xy in M_R  implies  N_A(x) intersect N_A(y) intersect X = empty. (B29)
```

In the path-cycle decomposition (B22), no R-fiber may join the two ends of
an A-path of length two (including a two-step arc of an A-cycle); in
particular it cannot be an edge of a triangular A[X]-component.  An
R-fiber may still be an edge of a longer path or cycle, producing a triangle
with its R-center, or join vertices with no common A[X]-neighbor.  Thus the
next consumer must distinguish these two allowed types; raw matching
parity alone cannot close the branch.

For the separator-located pole, this near-perfect matching is overwhelmingly
one-colored.  Suppose `c in W` and retain `m_c=deg_D(c,X)`.  Then the set
`M_c` from (B24) is exactly the missing-c color class `S_c`.  Since
`n_c=q-1-m_c`, (B27) specializes to

```text
M_c = (m_c singleton K_c fibers)
      disjoint-union (q-2-m_c two-point R_c fibers)
      disjoint-union (two incident-P singleton fibers).     (B30)
```

The two P-recipients in this display lie in `M_c` directly: their centers
are adjacent to c.  The other two wing matchings contain only

```text
sum_(w in W\{c}) |R_w|
  = (q-2)-|R_c| = m_c <= 4
```

edges in total, using (B23).  Thus all but at most four edges of the global
normal form (B28) have color c, and the c-colored part is a matching on
`M_c` leaving exactly `m_c+2` singleton-routed points there.  In the
second case of (B28), if u is the middle of the unique length-two path,
at least one of its two incident edges belongs to this bounded non-c
exception, because a single color is itself a matching.  The remaining
separator-located compatibility problem is therefore a bounded color
perturbation of one large c-wing matching, even though q is unrestricted.

The alternative location `c in Y` has a parallel but even cleaner normal
form.  Every `x in X` is a D-nonneighbor of c, so its unique common
A-neighbor with c lies in `N_A(c)`.  Conversely every X-neighbor of a point
of `N_A(c)` supplies such a route.  The resulting fibers are disjoint and
exhaust X.  Now c has exactly one X-neighbor, namely u, no W-neighbor by
(B7), and its other `q-1` neighbors lie in Y.  Moreover

```text
deg_A(z,X)=2-1_(z in K),
|N_A(c) intersect K|=deg_A(c,K)=2.
```

Thus the q centers in `N_A(c)` partition X into two singleton fibers and
`q-2` two-point fibers.  The latter form a matching `M_c^Y` with `q-2`
edges and exactly two uncovered X-points.  The special center u determines
its precise interaction with the path-cycle graph:

```text
u in K:      u is one of the two singleton centers, and every edge of
             M_c^Y has no common A-neighbor in X;
u notin K:   N_A(u) intersect X is the unique edge of M_c^Y whose ends
             have a common A-neighbor in X; all other edges have none.
                                                               (B31)
```

Indeed every center other than u lies in Y, so a common X-neighbor of the
ends of one of its fibers would be a second common A-neighbor.  If `u notin
K`, its X-degree is two and its fiber is exactly the two-step A[X]-arc
through u; C4-freeness excludes any other X-center for those ends.  If
`u in K`, its X-degree is one and it supplies a singleton instead.  Hence
the Y-located branch is an almost-perfect matching avoiding every A[X]
two-step arc, with the sole possible exception forced and identified by u.

So the sole dual escape consists of three rigid wings around `W`, an
exceptional point outside all three wings, and a `q-2` residue component no
larger than the halfway parameter.

## Three-vertex-connectivity

The Mantel bound (16) closes the sole two-separator escape left by maximal
edge-connectivity.  First, `D` has no articulation vertex: if deleting `w`
leaves at least two components, their nonzero cuts are all incident with
`w`, so their cut sizes sum to `q-1`, while each is at least `q-1`.

Now suppose `W={x,y}` separates `D`.  The component cuts sum to at most
`2(q-1)`.  Hence there are exactly two components `S_1,S_2`, both cuts have
size `q-1`, and `xy` is not a D-edge.  For binary `q>=8`, the minimum-cut
residue and

```text
|S_1|+|S_2| = q^2-2
```

force `|S_i|=q a_i-1`, with `a_1+a_2=q`.  Equality in (1) gives q-element
low sets `Z_i` such that

```text
A 1_(S_i) = a_i 1 - 1_(Z_i).
```

Adding the two equations and using `S_1 disjoint-union S_2=V\W` yields

```text
1_(Z_1)+1_(Z_2) = 1_(N_A(x))+1_(N_A(y)).      (27)
```

Since `xy` is not a D-edge, its two A-neighborhoods meet in a unique point
`c`.  Equation (27) therefore says that `Z_1,Z_2` also meet in `c` and
partition the two punctured neighborhoods.  For either i, write

```text
Z_i = {c} disjoint-union P_i disjoint-union Q_i,
P_i subset N_A(x)\N_A(y),
Q_i subset N_A(y)\N_A(x).
```

Both `{c} union P_i` and `{c} union Q_i` are D-cocliques, because their
pairs share A-neighbor x or y.  Thus, with `p=|P_i|`,

```text
e_D(Z_i) <= p(q-1-p)
           <= floor((q-1)^2/4)
            = q^2/4-q/2.                      (28)
```

On the other hand, orienting the complementary minimum cut `V\S_i`, whose
size is 1 modulo q, makes `Z_i` its associated q-set.  Bound (16) gives

```text
e_D(Z_i) >= q^2/4-1,                           (29)
```

contradicting (28) for `q>=8`.  Consequently

```text
D connected implies vertexConnectivity(D) >= 3.      (30)
```

This is stronger than maximal edge-connectivity alone and is the first
place where the near-Mantel q-set bound eliminates a global separator
configuration rather than merely classifying it.

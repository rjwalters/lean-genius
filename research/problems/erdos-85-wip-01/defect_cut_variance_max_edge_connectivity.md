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

whereas excess two gives

```text
A 1_W = 1_R + 1_K + 1_c,
|K|=2q-1, c in K.
```

These are precisely the ambient versions of (25)--(26); the extra
near-bipartite incidence argument is what further forces
`K intersect R={a,b}` and locates `c` there.

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

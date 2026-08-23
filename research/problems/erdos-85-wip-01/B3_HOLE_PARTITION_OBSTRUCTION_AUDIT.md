# B.3 exceptional-hole partition obstruction audit

## Scope

This note records the current boundary of the `q = 9` three-high second-profile
residual/core obstruction.  It is not a nonexistence proof.  The SAT results
below are external exploratory evidence; no UNSAT certificate is claimed.

Let `Q` be the `47 x 24` incidence matrix of the ordinary `B0` centers with
the unmarked `B1` core, let `K` be the cubic core adjacency matrix, and let
`A` be the residual adjacency matrix on the 47 centers.  An exceptional
triple center `h` has residual degree six and exactly three triple-center
neighbors.  The already-proved trace-zero law and the `B0` Gram law imply
that the six `Q`-blocks at those neighbors are pairwise disjoint and avoid
`supp(Q_h K)`.  Their sizes are three triples and three pairs, so equality in
the 24-point capacity bound requires

```text
U1 \ supp(Q_h K)
  = (three disjoint rainbow triples) disjoint-union
    (three disjoint marked-support pairs).
```

Colorwise, the pairs must consist of one of each missing-color type, using
two points of each color.  The triples must then give a three-edge matching
on the remaining `3 x 3 x 3` points.

## Exact computational frontier

`q9_b0_residual_defect_sat.py --audit-hole-partitions-seeds N` counts these
local partitions in fixed outer witnesses.  In ten sampled witnesses per
branch, every witness had at least one exceptional hole with count zero.
Branch 4 also produced a valid outer witness with a count-one hole, so a
theorem excluding every hole separately is false.

The seed-free mode keeps the unrestricted outer `Q,K` design and only the
residual edges incident to exceptional holes.  It omits all other residual
rows and defect semantics:

```text
python3 q9_b0_residual_defect_sat.py \
  --branch 3 --hole-partition-only --kissat --timeout-seconds 180
```

This produced `p cnf 138975 837650` and `UNKNOWN`.  Requiring only one of the
two branch-3 holes via `--hole-partition-at-least 1` produced
`p cnf 138976 837618` and was also `UNKNOWN` after 180 seconds.  Thus neither
the coupled conjecture nor a branch-3 per-hole strengthening is established.

## Reductions that do not close

1. **Capacity alone.**  For a row `t`, disjointness gives
   `3 n3(t) + 2 n2(t) <= 24 - |supp(Q_t K)|`.  This is just the degree bound
   on ordinary rows.  At a hole it is equality and yields the partition
   above, but no contradiction.
2. **Parallel-class role counts.**  They admit an abstract partition: take
   three diagonal triples on indices `3,4,5` and the pairs
   `(c0:6,c1:6)`, `(c0:7,c2:6)`, `(c1:7,c2:7)` outside a `3+3+3` support.
   Hence the Latin/parallel-class layer alone is insufficient.
3. **Binary row space.**  Exact partition implies
   `(A Q)_h = 1 + (Q K)_h` over `F2`.  The aggregate hole targets lie in the
   eligible block-row span in sampled witnesses, so parity gives no terminal.
4. **Scalar pair-cover contractions.**  The exact outer cover is
   `K^2 + Q^T Q + D = C + 8 I`, where the 47 rows of `Q` already include
   both the 26 triple centers and the 21 marked-pair centers, `D` is the core
   defect graph, and `C` is the complete tripartite color graph.
   Substituting the partition equation and taking row sums or inner products
   recovers existing column laws or tautologies.
5. **Per-hole Hall or determinant vanishing.**  False in branch 4: one valid
   outer witness has a full local transversal.  Its partition parity is one,
   so even the coupled sum of the corresponding determinants need not vanish.
6. **Forced puncture-type transport.**  False in sampled compatible holes.
   Triple-neighbor role patterns vary, and a compatible partition need not
   contain another exceptional hole.

## Remaining conjecture

The only surviving statement from this mechanism is location-sensitive:

> In every branch-3 or branch-4 outer design satisfying the exact zero-slack
> pair cover, not all exceptional holes admit the complement partition above.

Equivalently, the high-degree product of the local `3 x 3` matching-existence
indicators is zero.  None of the capacity, parity, determinant-sum, role-count,
or scalar matrix identities above implies this.  Progress requires a new
entrywise coupling among different holes or a certified solution of the
seed-free query; repeating fixed-outer residual SAT does not address the
uniform statement.

## Rectangular collision parity

There is a parameter-free parity invariant which survives the failed scalar
contractions above.  It was identified by transferring the collision-table
argument from the regular component lane.  Let `Q` be any zero-one matrix,
let `K` be any symmetric loopless zero-one matrix, and put

```text
R = Q K Q^T.
```

If `S_x` is the support of row `x` of `Q`, then

```text
R_xx = 2 |E_K(S_x)|.                                           (1)
```

Since `R` is symmetric, every off-diagonal summand in the ordered collision
count occurs twice.  On the diagonal,
`binom(2e,2) = e(2e-1) = e (mod 2)`.  Therefore

```text
sum_(x,y) binom(R_xy,2)
  = sum_x |E_K(S_x)|                         (mod 2).           (2)
```

No entry bound on `R` is needed for (2).  If the application separately
forces `R_xy <= 2`, its left side is exactly the parity of the ordered cells
with two routes.

For disjoint vertex blocks `T,U` in a C4-free graph, take `Q` to be the
`T x U` adjacency block and `K` the adjacency matrix on `U`.  Then the right
side of (2) counts triangles having one vertex in `T` and two in `U`.
Moreover, if `x,y in T` are adjacent, the two cross fibers are anticomplete
by `c4Free_internalEdge_crossBlock_fibers_anticomplete`, so

```text
A_T(x,y)=1  implies  R_xy=0.                                  (3)
```

Thus (2)--(3) give a joint parity invariant of precisely the residual
adjacency and the zero-support graph of `Q K Q^T`; unlike the earlier trace
zero, it sees double routes.  In the B.3 specialization, its right side is
the parity of the `B0-B1-B1` triangles with the B1 vertices in the unmarked
core.

This does not yet close the hole-partition conjecture.  The remaining
consumer must determine that triangle parity (or force the parity of the
double-route cells) from the colored row ledger.  Connectivity of `D0-x`
does not by itself enter (2); its prospective role is to prevent the
collision support from splitting into independently parity-balanced pieces.

### Core-edge contraction

The exact pair-cover identity makes the missing parity more concrete.  In
the B.3 notation,

```text
K^2 + Q^T Q + D = C + 8 I,
```

The graph `K` has twelve same-color root-triangle matching edges and 24
cross-color edges;
only the latter are edges of the complete tripartite color graph `C`.
Contracting this identity over those 24 unordered cross-color `K`-edges gives

```text
sum_{uv in E(K)} (Q^T Q)_uv
  = 24 - 3 t(K) - |E(K) intersect E(D)|,                       (4)
```

where every edge set in (4) is implicitly restricted to the cross-color
sector.  Indeed, the `K^2` contraction is `3 t(K)`: a K-triangle is rainbow
(two same-color vertices would share both their high root and the third
triangle vertex), and contributes one common neighbor on each of its three
edges.  The left side of (4) is exactly the number of `B0-B1-B1` triangles
counted on the right side of (2).  Thus its parity is

```text
t(K) + |E(K) intersect E(D)|  (mod 2).                         (5)
```

This is the three-way common-neighbor partition of the cubic-core edges:
completion inside the unmarked core, completion through one of the 47
ordinary `B0` rows (including a marked-pair row), or no completion (a defect
edge).  Consequently the first missing input can be stated sharply: the
existing colored ledger must couple the two terms in (5).  Their uncolored
sum merely recovers the 24-edge partition and supplies no contradiction by
itself.

### Pointwise sharpening and parity probe

There is one exact pointwise sharpening.  The graph induced on the
neighborhood of any vertex in a C4-free graph has maximum degree at most
one: two incident local edges would make their two outer endpoints share
both the root and the middle vertex.  Every B.3 row support has size two or
three, so

```text
|E_K(S_x)| is either zero or one.                               (6)
```

Consequently the right side of (2) is literally the parity of the number of
ordinary B0 rows carrying a B0--U1--U1 triangle, not merely a weighted edge
count.

The mandatory abstract-satisfiability probe rules out an outer-ledger-only
parity theorem.  Using `make_outer_seed` from
`q9_b0_residual_defect_sat.py`, three independently seeded valid outer
designs in each branch gave total internal-row K-edge counts

```text
branch 3: 11, 14, 18  (parities 1,0,0),
branch 4: 12, 15, 17  (parities 0,1,1).
```

Thus both parities occur in both branches before the residual graph and
defect semantics are imposed.  This is a failure certificate for the claim
that the colored `Q,K` row ledger alone fixes (2); it is not evidence that an
actual graph can realize either parity.  Any terminal consumer must use the
residual adjacency, defect connectivity, or an equally strong coupling.

### The unmasked local label sum is tautological

The most direct attempt to bring the residual graph into (6) still loses its
adjacency information.  Over `F2`, let

```text
q(s) = |E_K(supp(s))|,
b(s,t) = s K t^T.
```

Then `q(s+t)=q(s)+q(t)+b(s,t)`.  At an exact exceptional hole `h`, the
partition equation is

```text
sum_{u in N_A(h)} Q_u = 1 + Q_h K.
```

Polarizing therefore expresses the sum of the row labels `q(Q_u)`, plus all
cross-block terms `b(Q_u,Q_v)`, as `q(1+Q_hK)`.  But the neighbor blocks
partition `W = U1 \ supp(Q_hK)`, so the entire left side is simply
`|E_K(W)|`.  Cubic handshaking gives

```text
|E_K(W)| = q(supp(Q_hK)) + |supp(Q_hK)|  (mod 2),
```

which is exactly the polarized right side.  Hence the unmasked neighbor-label
sum is another form of cubic handshaking.  A non-tautological consumer must
retain a mask on the cross-block terms, for example one supplied by residual
adjacency or defect reciprocity.

### Incidence-masked three-way partition

There is a pointwise identity that retains both masks.  For an ordinary B0
row `t`, put `S_t = N_G(t) intersect U1` and `l_t=|E_K(S_t)|`.  Restrict the
mixed three-way resolution to the incidence cells `b in S_t`.  Such a cell
is resolved in exactly one of three ways:

1. by a core common neighbor in `U1`;
2. by a residual B0 common neighbor;
3. by the defect relation, equivalently the original edge `tb` is
   triangle-free.

Because the graph induced on `S_t` is a matching, the first class has size
exactly `2 l_t`.  If `r_t` and `d_t` denote the sizes of the second and third
classes, respectively, then

```text
|S_t| = 2 l_t + r_t + d_t.                                  (7)
```

Every unmarked B1 column has five B0 neighbors, so
`sum_t |S_t| = 24*5 = 120`.  Writing `L=sum_t l_t`, `R=sum_t r_t`, and
`Z=sum_t d_t`, summing (7) gives

```text
2 L = 120 - R - Z.                                           (8)
```

Thus the collision parity is the half-parity of the combined
residual-resolved and triangle-free incidence mass.  Unlike the unmasked
polarization, (7)--(8) preserve exactly the residual/defect distinction
needed by a prospective connectivity consumer.  They do not yet determine
that half-parity; a mod-four constraint on `R+Z` is still required.

The residual term has an exact graphical normalization.  Every triangle
with two ordinary B0 vertices and one vertex of `U1` contributes its two
B0--U1 incidence cells to `R`, and uniqueness of a common neighbor gives
the converse.  If `T_R` is the number of these triangles, then

```text
R = 2 T_R,
120 = 2 L + 2 T_R + Z,
L = T_R + Z/2  (mod 2).                                      (9)
```

In particular `Z` is even.  Equation (9) identifies the remaining consumer
as a joint parity law for residual B0--B0--U1 triangles and half the number
of triangle-free B0--U1 incidence edges.

The colorwise version retains more information.  For a high-root color `i`,
the eight vertices of `U1_i` have five ordinary B0 neighbors each, giving a
40-edge incidence cut.  Let `L_i` count the endpoints of row-internal
K-edges that lie in color `i`, let `T_R,i` count residual triangles whose
U1 vertex has color `i`, and let `Z_i` count triangle-free incidence edges
into `U1_i`.  Then

```text
40 = L_i + 2 T_R,i + Z_i,
L_i = Z_i  (mod 2).                                           (10)
```

Here `sum_i L_i=2L`, because every internal K-edge is cross-color.  If `m_i`
instead counts the triangle-carrying rows whose internal edge misses color
`i`, then `m_i=L-L_i`, hence

```text
m_i = L + Z_i  (mod 2).                                      (11)
```

Thus a colored defect-cut parity would recover the parity distribution of
the missing colors, even though summing (10) over all three colors returns
only the already-known evenness of `Z`.
### Defect-degree connectivity probe

A second probe tests how much of defect connectivity is already enough.
For each fixed outer design, allow a B0--U1 defect cell exactly when its core
common-center count is zero.  Prescribe the proved row degrees
`3 - markedDefects(t)` (zero on exceptional holes) and the proved column
degrees `5 - specialDefects(b)`.  This is an exact bipartite b-matching, so it
was solved by max flow rather than SAT.  Four seeds per branch all attained
the full demand:

```text
branch 3: flow 114 / 114; connected positive core of order 69;
branch 4: flow 108 / 108; connected positive core of order 66 or 67.
```

Both triangle parities occurred among the successful connected cores in
each branch.  Thus the outer ledger plus the B0--U1 defect degree sequence
and connectivity of its positive bipartite core still do not determine (5).
This remains a necessary-condition probe: it does not construct the missing
B0--B0 defect edges or a residual graph and therefore is not a model of the
full `D0-x` theorem.  It does isolate the missing input more sharply as
residual/common-center reciprocity (or comparably strong B0--B0 structure),
not connectivity imposed only on the defect degree ledger.

### Marked-support neighborhood partitions

The marked-row reciprocity that is absent from the max-flow probe has an
exact support-local form.  Let `P_g` be one of the three seven-row groups
adjacent to a fixed marked B1 vertex, and put

```text
M_g = {t in ordinary B0 : N_A(t) intersect P_g is empty}.
```

Every row `u` in `P_g` has residual degree six: among its nine original
neighbors it has the marked B1 vertex, two unmarked B1 vertices, and six B0
vertices.  All six B0 vertices lie among the 47 ordinary rows.  Indeed, an
edge from `u` to a vertex `y` of the exceptional set `U` would close the
4-cycle `x-z-u-y-x`, where `z` is the marked partner.  The marked B1 vertex
has exactly five B0 defect neighbors, all again among the 47 ordinary rows;
the vertices of `U` share `x` with it.  Some of those five defects can lie
inside `P_g`: adjacency does not exclude a triangle-free edge from the
second-order defect graph, and the proved internal-defect theorem in fact
makes their number inside `P_g` odd.  Hence `|M_g|=5` and

```text
sum_t |N_A(t) intersect P_g|
  = sum_{u in P_g} deg_A(u) = 7*6 = 42.
```

Each of the other 42 rows has at least one neighbor in `P_g`, so equality
forces exactly one.  Equivalently,

```text
{N_A(u) : u in P_g}
```

is a family of seven disjoint six-point sets which partitions the 42-point
complement of `M_g`.  Disjointness also follows directly from C4-freeness:
two rows of `P_g` already share the marked B1 vertex and therefore cannot
share a residual B0 neighbor.  Thus the full marked reciprocity produces
three parallel seven-fiber partitions, each with five holes.  This is a
strictly stronger placement constraint than prescribing only the row and
column degrees of the B0--U1 defect matrix.

There is already an exact reciprocity law among the three partitions.  Put

```text
c_gh = |M_g intersect P_h|.
```

For `g != h`, the residual edges between `P_g` and `P_h` form a matching.
Viewed from `P_h`, they cover exactly the `7-c_gh` rows which do not miss
`P_g`; viewed from `P_g`, the same edges cover exactly `7-c_hg` rows.
Therefore

```text
c_gh = c_hg.                                                 (12m)
```

On the diagonal, the induced graph on `P_g` matches precisely the rows
outside `M_g`, so `7-c_gg` is even and every `c_gg` is odd.  Hence the
three-by-three marked-miss matrix has symmetric off-diagonal entries and
odd diagonal.  This refines the earlier scalar parity laws: summing all
nine cells gives an odd pair-row marked-defect mass because the off-diagonal
entries occur twice, and subtracting it from the total marked-defect mass
`3*5=15` leaves the even triple-row mass.  Thus those two parities are the
aggregate shadow of the stronger symmetric transport law (12m).

The scalar miss-matrix abstraction is still highly nonrigid.  Enumerating
the nonnegative symmetric integer matrices with diagonal in `{1,3,5}` and
every row sum at most five gives 213 labeled matrices, or 59 orbits under
simultaneous permutation of the three marked groups.  The unused mass
`sum_g (5-sum_h c_gh)`, which is the marked-defect mass on triple rows,
attains every even value from zero through twelve.  Thus (12m) retains real
transport information, but its integer margins alone do not strengthen the
two aggregate parities; the locations of the matched rows must be used.

The first pairwise count between these partitions is nevertheless exhausted.
For `g != h`, every row outside `M_g union M_h` selects one fiber from each
partition, so

```text
sum_{u in P_g, v in P_h} |N_A(u) intersect N_A(v)|
  = 47 - |M_g union M_h| = 37 + |M_g intersect M_h|.         (12p)
```

Every summand is at most one, and it is zero when the two corresponding
outer blocks already share a U1 point.  The two marked matchings share a
color and cover seven of its eight points each, so they create six or seven
such forced-zero cells among the 49 pairs.  The resulting capacity is 43 or
42, while the right side of (12p) is at most 42.  Thus the unrefined pairwise
intersection count gives only the tautological bound
`|M_g intersect M_h| <= 5` (or weaker).  Any gain must couple all three
partitions, retain the locations of their forced-zero cells, or use the
ordinary U1 fibers below; pairwise mass alone is not the terminal.

### Residual fiber-matching form

Residual reciprocity packages the term `T_R` columnwise.  For `b in U1`,
let

```text
F_b = {t in ordinary B0 : Q_tb=1}.
```

Every `F_b` has five vertices.  Since it lies in the neighborhood of `b`,
the residual graph induced on `F_b` has maximum degree at most one and is
therefore a matching.  Its edges are in bijection with the residual
B0--B0--`b` triangles.  Consequently

```text
T_R = sum_{b in U1} |E(A[F_b])|,                              (12)
```

with each summand in `{0,1,2}`.  In particular, the parity of `T_R` is the
parity of the number of U1 columns whose five-point residual fiber contains
exactly one matching edge.  This is the first formulation in the chain that
uses symmetry of the residual B0 adjacency itself; the max-flow defect probe
does not model these fiber matchings.

### Two-color fiber-packing localization

The nonlinear join localizes much more sharply than the full 24-column
model suggests.  Fix an outer `Q,K` design and retain only:

1. the exact residual row degrees (five on regular triple rows and six on
   the exceptional holes and all pair rows);
2. the two trace-zero directions on an allowed residual edge `uv`, namely
   `S_v intersect (S_u K)=empty` and `S_u intersect (S_v K)=empty`;
3. the fiber cap `|N_A(t) intersect F_b| <= 1`, but only for the sixteen
   points `b` in any chosen two of the three high-root colors.

Even after relaxing every residual edge variable to the interval `[0,1]`,
this system is infeasible for every color pair on four independently
generated outer seeds in each branch.  All 24 branch/seed/color-pair LPs
return infeasible.  By contrast, keeping the caps for only one eight-point
color class is satisfiable in the corresponding binary model, as is every
tested four-fiber closed neighborhood in `K`.  Exact degrees plus the
trace-zero support and all three marked-support partitions are also
satisfiable on the eight seeds when the U1 fiber caps are omitted.

Thus the sampled obstruction is not marked-row reciprocity and does not
require all three colors.  It is already a **two-color fiber-packing
inequality**, and LP infeasibility guarantees a weighted linear (Farkas)
certificate for each sampled design.  The remaining proof target is to make
that inequality uniform in the outer design.  Rowwise transversal capacity
alone is not uniform: it kills a few sampled color pairs directly, while in
most instances every row separately has enough eligible neighbors and only
global residual reciprocity fails.  The reproducible relaxation is
`q9_two_color_residual_lp.py`; its output is evidence for the uniform lemma,
not a universal certificate.

Dual extraction also gives a useful negative boundary.  A canonical
minimum-cap-relaxation LP produces positive separating duals, but their
extreme rays vary strongly with the outer witness.  Three restricted dual
families give separation exactly zero on every tested instance: one common
cap price per row; additive row-plus-fiber prices; and eighteen invariant
prices indexed by row type, selected fiber color, and incidence versus
nonincidence (after deleting trace-inactive cells).  Hence the observed
Farkas certificate does not collapse to fixed row-type, color, or local
incidence weights.  It sees the detailed two-color eligibility graph.  A
uniform proof must therefore construct a Hall/min-cut potential from `Q,K`
or prove directly that the corresponding fractional exact-degree polytope
is empty; another scalar weighted-row ledger cannot recover this signal.

Greedy irreducible-subsystem probes show why such a potential cannot be
attached to one fixed row set.  Depending on the outer witness and selected
color pair, an infeasible degree-row core can be a single locally deficient
row, one complete five-row fiber `F_b`, a six-row set `F_b union {u}` with
`b in S_u K` (so `u` is trace-anticomplete to `F_b`), or a larger coupled
multi-fiber set.  In other instances every individual row and every single
fiber is fractionally feasible although the complete system is not.  These
cores depend on deletion order and are diagnostic rather than certificates,
but they locate the plausible uniform statement: a local-transversal versus
coupled-multi-fiber deficiency dichotomy, not the existence of one bad fiber
of a predetermined kind.

The local half of that dichotomy has a standard exact form.  Fix a row `t`
and two selected colors.  Replace every trace-eligible candidate neighbor
`u` by the selected-color labels in `S_u`.  A triple row, or a pair row
missing the unselected color, carries one label in each selected color and
therefore gives an edge of an `8`-by-`8` bipartite graph.  A pair row missing
one selected color carries a single label; attach its other endpoint to a
private dummy vertex on the opposite shore.  Linearity of the outer design
prevents duplicate two-label edges, and the marked pair supports are
matchings, so the construction faithfully records candidate rows.

Choosing residual neighbors of `t` subject to all sixteen fiber caps is now
exactly choosing a matching in this augmented bipartite graph.  In
particular, the one-row LP relaxation is integral, and

```text
the degree demand at t is locally feasible
iff nu(twoColorCandidateGraph(t)) >= d_t,                    (12f)
```

where `d_t` is five or six.  Failure of (12f) has an ordinary Hall-set
certificate.  This explains the single-row irreducible cores above without
any numerical duality.  When (12f) holds at every row, the remaining horn is
genuinely simultaneous: locally chosen matchings must be coupled by
`A_uv=A_vu` and by the five-row fiber constraints.  The sampled designs show
that this simultaneous horn can fail even though every graph in (12f) has a
large enough matching.

Kőnig's cover criterion can be written without private dummy vertices.  Let
`L` be a subset of the sixteen real selected labels which meets every
two-label candidate support, and let `s_t(L)` be the number of singleton
candidates at row `t` whose unique label is outside `L`.  Once `L` is fixed,
exactly those `s_t(L)` private dummies must be added to cover the singleton
candidate edges.  Therefore

```text
nu(candidateGraph(t))
  = min_{L hits every two-label candidate} (|L|+s_t(L)),
so nu(candidateGraph(t)) < d_t iff some such L has
|L| + s_t(L) <= d_t-1.                                     (12fa)
```

Equivalently, local feasibility says `|L|+s_t(L)>=d_t` for every real-label
cover of the two-label candidates.  This is an exact label-only Hall
inequality derived from `Q,K`, and is the clean hypothesis to negate in the
simultaneous price branch.

There is an exact weighted extension which removes the local matching oracle
from (12h).  Assume the row is locally feasible, give candidate `u` weight
`w_u`, and let `D_t` and `S_t` be its two-label and singleton candidates.
The dual of the cardinality-`d_t` bipartite matching LP has a free cardinality
price `z` and nonnegative vertex prices.  Every singleton dummy is private,
so its price can be minimized explicitly.  The result is

```text
max_{matching M, |M|=d_t} sum_{u in M} w_u
 = min_{z real, y_b>=0}
     [d_t z + sum_{b in C} y_b
      + sum_{u in S_t} max(0, w_u-z-y_{b(u)})],             (12fb)

subject to z+y_a+y_b >= w_u for every u in D_t
with selected labels {a,b}.
```

Thus all private dummies and all matching choices can be eliminated in favor
of sixteen real-label prices and hinge terms.  Substituting the Farkas-curl
edge weights (12n) into (12fb) turns the global condition
`sum_t max_{P_t} W_t<0` into a purely scalar nested price inequality.  This
is the natural analytic form for proving the Hall-or-price conjecture: (12fa)
handles failure of the cardinality face, and (12fb) handles every locally
feasible row.

The free cardinality price can also be eliminated.  For fixed `y`, put

```text
L_t(y) = max_{u in D_t, labels {a,b}} (w_u-y_a-y_b),
rho_u(y) = w_u-y_{b(u)}  for u in S_t,
```

and let `theta_(d_t+1)(y)` be the `(d_t+1)`-st largest singleton residual,
with value minus infinity if there are fewer than `d_t+1` singletons.  The
`z`-dependent part of (12fb) is convex piecewise linear, with slope `d_t`
minus the number of residuals above `z`, subject to `z>=L_t(y)`.  Hence one
minimizer is

```text
z_t(y) = max(L_t(y), theta_(d_t+1)(y)).                    (12fc)
```

If both entries are minus infinity (no two-label candidates and exactly
`d_t` singleton candidates in the locally feasible case), any real `z`
below all singleton residuals is minimizing.

Substitution in (12fb) leaves a minimization over only the sixteen
nonnegative real-label prices.  In particular, both the unweighted Hall
branch and the weighted simultaneous branch now live on the same label
space; their difference is a cardinality threshold versus a convex hinge
objective.

All prices may be made exact integers.  The directed feasibility system has
rational coefficients, so strict Farkas separation admits rational
`alpha,mu`; scaling gives integral `alpha,mu,W` while preserving `mu>=0` and
the strict sign.  For integral candidate weights, the bipartite matching
system is totally dual integral, hence the local dual in (12fb) has integral
`z` and real-label prices `y`; eliminating private dummies and then `z` via
(12fc) preserves integrality.  Consequently every fractional B.3
obstruction has a finite integer nested-price certificate.  This matters for
formalization: a prospective checker needs only integer inequalities, not LP
tolerances or imported solver duals.

The experiment now contains such an independent integer checker.  After a
floating separator is found, it rounds every price at a requested scale and
recomputes each row support function by integer dynamic programming on the
sixteen-bit occupied-label mask and the exact chosen cardinality.  Singleton
private dummies need no state bit, since each occurs in only its own edge.
This check uses neither the floating master LP objective nor its binary MILP
matching oracle.  At scale `10000`, all six individually fitted seed-zero
branch/color instances pass, with exact total support values

```text
branch 3: -44635, -67985, -39396,
branch 4: -53670, -202275, -45792.
```

Thus the sampled strict inequalities have genuine finite integer witnesses,
not numerical-tolerance artifacts.  Conversely, fitting one common
uncompressed Farkas table to all six cases reaches the zero potential and
the exact checker returns six zero totals.  This is useful negative scope:
the evidence supports design-adaptive prices derived from `(Q,K)`, not one
universal coefficient table shared by unrelated outer designs.

In the four-seed run the local branch is extremely sharp.  There are nine
failed row/color-pair instances.  Every matching number is exactly one below
demand.  Eight are demand-six rows with a minimum vertex cover of size five;
the remaining regular triple row has demand five and cover size four.  Five
of the eight size-five covers consist of five selected U1 labels; the other
three observed demand-six covers consist of four selected labels and one
private dummy (the demand-five cover uses four labels).  Thus the sampled
local obstruction is not a diffuse Hall deficit: a set of `d_t-1` cap
vertices covers every eligible candidate edge.  Negating this concrete
cover pattern is the likely local input to the monotone-price branch.

The simultaneous horn also has an exact directed form which removes matrix
symmetry from the list of mysteries.  A feasible symmetric fractional `A`
exists if and only if there is a nonnegative directed matrix `X`, on the
same symmetric allowed support, such that

```text
rowSum(X)=d,   colSum(X)=d,
sum_{u in F_b} X_tu <= 1,   sum_{u in F_b} X_ut <= 1          (12g)
```

for every row `t` and every selected fiber `b`.  The forward implication is
`X=A`.  Conversely, set `A=(X+X^T)/2`.  Its row sum is the average of the
corresponding row and column sums of `X`, and each fiber cap is the average
of the outgoing and incoming caps in (12g); all other conditions are
preserved.  Thus the remaining obstruction is precisely balanced
transportation between the locally feasible candidate matchings, not an
extra parity of symmetric matrices.  Equation (12g) is the natural interface
for a submodular-flow or transportation min--max theorem.

In fact (12g) has a canonical separation theorem.  Let `P_t` be the compact
local candidate-matching polytope at row `t`, including the equality that
its total mass is `d_t`, and let

```text
P = product_t P_t.
```

Transpose is a linear involution `T` on directed matrices.  Equation (12g)
is feasible exactly when `P intersect T(P)` is nonempty.  If these two
compact convex polytopes are disjoint, strong separation supplies a linear
functional `L` with

```text
sup_{X in P} L(X) < inf_{X in P} L(TX).
```

Then `W=L-L after T` is antisymmetric and `W(X)<0` for every `X in P`.
Conversely, any antisymmetric functional of one strict sign on `P` forbids
the intersection: if `X,TX in P`, then `W(TX)=-W(X)` has the opposite sign.
Consequently

```text
P intersect T(P) is empty
iff there is W with W^T=-W and max_{X in P} W(X)<0.           (12h)
```

The optimization in (12h) decomposes over rows.  For fixed `W`, its value is
the sum of 47 independent maximum-weight degree-`d_t` matchings in the
augmented bipartite graphs from (12f).  Thus (12h) compresses the
design-dependent Farkas rays into the correct canonical object: an
**antisymmetric matching potential**.  The uniform outer-design theorem can
now be stated precisely as constructing `W(Q,K)` for which the sum of these
local matching optima is strictly negative.

The arbitrary skew matrix in (12h) can be replaced, without loss, by a
canonical row--fiber Farkas curl.  Assume first that every `P_t` is nonempty.
Regard `P` as already enforcing row degrees and outgoing fiber caps.  If the
remaining column-degree equalities and incoming caps are infeasible, strong
Farkas separation gives free prices `alpha_u` for the column equalities and
nonnegative prices `mu_ub` for the incoming caps such that

```text
F(X) = sum_u alpha_u(colSum_u(X)-d_u)
     + sum_{u,b} mu_ub(incomingCap_ub(X)-1) > 0             (12m)
```

for every `X in P`.  But `F(TX)<=0` on `P`, because transpose turns those
terms into the row equalities and outgoing caps already imposed in `P`.
Consequently `W=F after T-F` is strictly negative on `P`, with ordered-edge
coefficient

```text
W_tu = alpha_t-alpha_u
     + sum_{b in S_u intersect C} mu_tb
     - sum_{b in S_t intersect C} mu_ub.                   (12n)
```

Conversely, any strict certificate of the form (12n) is an antisymmetric
certificate in (12h).  Thus (12n) is a complete normal form: the obstruction
is a curl of row-specific prices on the sixteen selected fibers, plus an
ordinary degree-gradient term.  Its optimization over `P` still splits
into the 47 local weighted matchings.  The uniform theorem need not invent
an arbitrary weight for every ordered row pair; it must construct the
nonnegative incoming-cap prices `mu` from `Q,K`.

As a diagnostic, allowing signed row--fiber prices and setting `alpha=0`
already separates all six seed-zero instances.  The normalized optima are

```text
branch 3: -5.11710981, -9.45805385, -5.14649276,
branch 4: -5.48336072, -23.1950319, -5.18894009.
```

Mode `--features row-fiber-curl` reproduces this restricted fit.  The signed
fit is evidence that the cap curl, rather than the degree gradient, carries
the sampled signal; the exact completeness statement remains (12m)--(12n),
where Farkas requires `mu>=0` and may use `alpha`.

Imposing exactly those signs and including `alpha` also succeeds
numerically, as completeness predicts.  Mode `--features farkas-curl` gives

```text
branch 3: -4.46896933, -6.80267476, -3.94440060,
branch 4: -5.37158807, -20.2324231, -4.58449430.
```

These are direct nonnegative-cap-price certificates of (12m), not fits in a
larger unsigned feature class.  They verify the sign convention and leave a
sharper uniform target: derive `mu>=0` and `alpha` from the mixed flag counts
in (12k)--(12l).

The nonnegative prices can be made local and color-symmetric on every
seed-zero instance.  Relative to an unordered selected color pair, merge the
five row types into four roles:

```text
regular triple; exceptional hole;
pair missing either selected color; pair missing the unselected color.
```

For a root row `t` and selected fiber `b`, let `r_tb` be the four-vector of
these role counts in `E_t intersect F_b`.  There are nonnegative prices of
the form

```text
mu_tb = f(role(t), n(t), c(t), r_tb),
alpha_t = g(role(t), n(t), c(t)),                            (12o)
```

with no dependence on the identity or selected color of `b`, nor on whether
`b in S_t`, which strictly separate all six instances.  Their normalized
optima are

```text
branch 3: -0.964341984, -2.40773483, -1.01006714,
branch 4: -2.21949614,  -11.7358523, -1.45558145.
```

This is the first exact-price ansatz invariant under swapping the selected
colors.  Coarser controls locate its necessary information: retaining only
the load `|E_t intersect F_b|` separates three of six; replacing the four
roles by merely residual demand five versus six separates only two;
and deleting `n(t),c(t)` from the root price separates only one.  Thus the
prospective lemma must combine the root mixed-triangle flag with the marked
role census inside each eligible fiber.  Mode `--features
fiber-role-farkas` reproduces (12o); the neighboring feature modes record
the controls.

The four-role symmetry is close to, but not uniformly stable across, a wider
sample.  In a four-seed-per-branch run, seven of the 24 instances have a
direct local Hall obstruction.  Of the remaining seventeen, the four-role
prices separate sixteen.  Retaining the two oriented roles "pair missing
the first selected color" and "pair missing the second selected color" gives
five roles and separates all seventeen, still without using the identity,
color, or root-incidence of `b`.  Thus the robust sampled dichotomy is

```text
local Hall failure, or
mu_tb = f(orientedRole(t),n(t),c(t), orientedRoleCensus(E_t intersect F_b)).
                                                                    (12p)
```

Mode `--features fiber-type-bare-farkas --seeds 4 --individual` reproduces
the 7/17 split.  The random-seed numbers label solver samples rather than
canonical outer witnesses, so comparisons of one named seed across separate
processes are not treated as witness identities.  Equation (12p) is sampled
evidence and a precise seed-free flag-price conjecture, not yet a proof for
every admissible outer design.

The fitted cap prices have a strong but nonterminal monotonicity pattern.
For the first witness, among 935 pairs of fiber censuses comparable
coordinatewise at a fixed root signature, one maximum-margin solution is
nondecreasing on 760 pairs (with 76 equalities).  Imposing exact
coordinatewise monotonicity on the five-role prices still separates all six
seed-zero instances.  On the wider four-seed run it separates fifteen of the
seventeen simultaneous instances; two branch-3 instances require the
unconstrained five-role table.  Hence a monotone shadow-price lemma is a
credible main case but not the complete sampled theorem: a uniform argument
needs either an exceptional branch or a weaker partial order on the role
censuses.  Mode `--features fiber-type-monotone-farkas` enforces these order
constraints inside the master LP.

Crucially, those two failures are not exceptions at the level of an outer
design.  They belong to the same branch-3 witness, whose third color pair
already has a direct local Hall obstruction.  Grouping the four-seed run by
its eight outer witnesses gives the clean dichotomy

```text
5/8 witnesses: some color pair has a local Hall failure;
3/8 witnesses: no local Hall failure, and monotone prices separate all
               three color pairs.                               (12q)
```

Thus every sampled outer witness is excluded after choosing a favorable
color pair by **local Hall or monotone flag prices**, with no residual sampled
case.  This is the sharp seed-free conjecture suggested by the computation:
prove that every admissible `Q,K` has either a local Hall-deficient candidate
graph (12f), or a color pair admitting coordinatewise-monotone prices of the
form (12p).  The exact color coupling (12l) is the natural mechanism for that
choice.

The two monotonicity exceptions identify a sharper three-color implication.
They occur in the same branch-3 outer witness, for pairs `(0,1)` and `(1,2)`;
the complementary pair `(0,2)` has a local Hall failure at exceptional row
25.  Its demand is six and its minimum cover has size five (either five real
labels, or four real labels plus one private singleton dummy).  Thus the only
sampled failure pattern has the form

```text
no monotone separator for {a,b} and {b,c}
  ==> a local Hall cover for the complementary pair {a,c}. (12qa)
```

Equation (12qa), with arbitrary distinct colors `a,b,c`, is a more focused
uniform target than constructing prices for every pair.  In the transport
dual below, its contrapositive says that local feasibility for `{a,c}`
prevents simultaneous balanced monotone transports for the two pairs
containing `b`.  The pair collision identity (12l) is exactly additive in
the two one-color load energies, so it is the natural scalar interface for
this complementary-pair implication.

A synchronization-free strengthening emerges by retaining that scalar in
the root signature.  Let

```text
c_all(t) = sum over all 24 U1 labels b of binom(ell_b(t),2)
         = (c_01(t)+c_02(t)+c_12(t))/2
         = c_ij(t) + c_k(t)  for {i,j,k}={0,1,2}.          (12qb)
```

This is selected-pair independent and is computed directly from `(Q,K)`.
Refine the monotone prices in (12p) by allowing `f,g` also to depend on
`c_all(t)`.  In the same four-seed run this refinement separates sixteen of
the seventeen locally feasible instances.  It repairs one of the two former
exceptions but not the other:

```text
branch 3, exceptional witness:
pair (0,1): 0,   pair (1,2): -0.4491999820.
```

Rounding at scale `100000` and applying the independent integer checker
gives exact total `-44861` for the repaired pair.  Thus the gain is genuine,
not a floating tolerance, but omitted collision alone is not a complete
sampled theorem.  Mode `--features fiber-type-total-monotone-farkas`
reproduces the corrected 16/17 result.

Since `c_pair` was already present, this refinement is equivalently just the
collision energy `c_k` in the **omitted** color.  In the exceptional witness
it splits six formerly aliased root signatures for each failed pair,
involving only fourteen roots for `(0,1)` and thirteen for `(1,2)`.  Thus the
old monotone failure is partly localized to omitted-color concentration, but
the surviving `(0,1)` case proves that concentration is not the only missing
flag.  A proof should still work directly with the color-symmetric triple
`(c_0,c_1,c_2)`, while retaining one further incidence/orientation datum for
the last case.

The omitted-color dependence may be given the expected collision sign.
Impose, at fixed `(role,n,c_pair,r_tb)`,

```text
c_all <= c'_all  ==>  mu(role,n,c_pair,c'_all,r_tb)
                       <= mu(role,n,c_pair,c_all,r_tb).     (12qe)
```

Thus a more concentrated omitted color receives a weakly smaller incoming
cap price, while the previous coordinatewise monotonicity in the fiber role
census is retained.  This signed cone also separates sixteen of seventeen:
the `(0,1)` exception remains at zero, while `(1,2)` has objective
`-0.3463128592` and exact scale-`100000` total `-34559`.
Mode `--features fiber-type-collision-monotone-farkas` enforces this signed
order.  The sign is the useful structural gain: it makes the omitted-color
coordinate a genuine collision/concentration charge in the repaired case,
but it does not remove the final need for another flag.

This axis-qualified cone also has an exact transport alternative.  At fixed
base signature `(role,n,c_pair)`, put a directed order edge

```text
(c,r) <= (c,r')   when r<=r',
(c,r) <= (c',r)   when c>=c',                              (12qf)
```

and take the transitive closure **on the flags which actually occur**.  The
first edge is fiber-census isotonicity and the second is collision
antitonicity (12qe); importantly, (12qf) does not insert a diagonal edge when
the intermediate flag is absent.  Repeating the separation and finite
Strassen argument of (12ra)--(12rc), failure of the signed price branch is
equivalent to fractional exact-cardinality row matchings such that

1. the endpoint census balances separately for every full alpha signature
   `(role,n,c_pair,c_all)`; and
2. within each base signature, incoming flag mass transports to source flag
   mass only along the realizable order (12qf).

This is the precise primal object exhibited by the one surviving sampled
case.  It retains exact three-color collision layers through the alpha
equations, but allows role mass to move between layers only through a fiber
census that occurs on both sides.  The remaining task is to identify the
smallest genuine `(Q,K)` flag that destroys this transport without reverting
to row or fiber identities.

That final flag can be isolated experimentally.  Retain the single bit

```text
iota_tb = 1[b in S_t]                                      (12qg)
```

in the cap-price signature, in addition to
`(role,n,c_pair,c_all,r_tb)`.  This is root--fiber incidence already present
in `Q`; it names neither the root nor the fiber and is invariant under
swapping the two selected colors.  The last `(0,1)` exception then separates
with objective `-0.08409488672` and exact scale-`100000` total `-8347`.
Consequently the four-seed result returns to 17/17 locally feasible
instances, now with the correctly scoped feature class.  Mode
`--features fiber-type-total-incidence-monotone-farkas` reproduces it.

For comparison, retaining selected-color position instead of `iota_tb` also
repairs the last case (objective `-0.1523749388`), but (12qg) is the smaller
and more symmetric datum.  The sharp sampled Hall-or-price target is
therefore: either the label-only Hall cover (12fa), or nonnegative prices
isotone in the oriented role census at fixed
`(role,n,c_pair,c_all,iota)`.  Relative to the original four-role ansatz,
the only added information is omitted-color collision and whether the priced
fiber is one of the root's own support fibers.

The incidence refinement has fixed margins.  Exactly `g(t)` of the sixteen
selected columns have `iota_tb=1`, where `g(t)` is two for regular triples,
holes, and pairs missing the unselected color, and one for pairs missing a
selected color.  For each oriented role `j`, put

```text
o_tj = sum_{b in S_t intersect C} r_tb,j.                  (12qh)
```

The outer block system is linear, so an eligible candidate block meets
`S_t intersect C` in at most one label.  Hence `o_tj` is exactly the number
of role-`j` eligible candidates sharing a selected support label with the
root; the external-column margin is the corresponding total in (12r) minus
`o_tj`.  Thus (12qg) merely exposes an own-versus-external partition of the
already fixed role margins.  This is also the native orientation of (12n):
the negative cap term is summed precisely over the root's own selected
fibers.  A prospective proof should therefore couple the two column classes
through (12qh), rather than treat `iota` as an arbitrary binary feature.

The reviewed separation alternative becomes especially sharp for this
incidence mode.  Its flag poset compares role censuses only at fixed full
root signature `sigma=(role,n,c_pair,c_all)` and fixed `iota`.  Hence failure
of the incidence-price branch is equivalent to fractional local matchings
with alpha balance at every `sigma` and, separately for each `(sigma,iota)`,
an equal-mass monotone transport

```text
incoming role-census columns  -->  source role-census columns,
supported only on r_in <= r_out.                            (12qi)
```

To see equal mass, sum all cap coordinates as in (12rb): alpha balance
weighted by `g` makes the global mass zero.  Every `(sigma,iota)` component
and its complement are upper sets of the disconnected flag poset, so their
two nonnegative dual inequalities force the component mass itself to zero.
Finite Strassen then gives (12qi).  Thus the final sampled conjecture has a
fully combinatorial negation: signature-balanced fractional row matchings
whose own columns and external columns each admit a census-increasing
transport.  The fixed own/external role margins (12qh) are the natural
candidate invariant for ruling this out uniformly.

The split can be read transition by transition.  Put

```text
delta_tu = |S_t intersect S_u intersect C| in {0,1}.       (12qj)
```

For a chosen directed candidate `t->u`, every shared selected label appears
once in the positive `(t,b)` cap sum and once in the negative `(u,b)` cap
sum, both with `iota=1`.  Target-only labels give `g(u)-delta_tu` positive
external flags, while source-only labels give `g(t)-delta_tu` negative
external flags.  Consequently

```text
own cap mass of t->u:       +delta_tu - delta_tu = 0,
external cap mass of t->u:  g(u)-g(t).                     (12qk)
```

Thus own-fiber mass cancels before any global argument, and external mass
cancels after alpha signature balance.  Moreover (12qi), tested against the
increasing coordinate `r_j`, gives for every `(sigma,iota)` and role `j`

```text
sum of source-side r_j over selected flags in (sigma,iota)
  >=
sum of incoming-side r_j over selected flags in (sigma,iota). (12ql)
```

Equations (12qj)--(12ql) turn the residual price problem into a directed
role-flow inequality.  The own system is supported exactly on selected
candidate transitions whose two blocks share a selected label; the external
system carries the complementary label incidences.  Since a row matching
uses each selected label at most once, at most `g(t)` of its chosen
transitions can enter the own system.  This is the direct bridge between the
transport alternative and the label-only Hall cover (12fa).

Equivalently, let `G_t^ext` be the row candidate graph after deleting every
candidate whose selected support meets `S_t intersect C`.  Splitting any
matching into own-touching and external candidates gives

```text
nu(G_t) <= g(t) + nu(G_t^ext).                             (12qm)
```

Therefore local feasibility forces

```text
nu(G_t^ext) >= d_t-g(t),                                  (12qn)
```

namely thresholds three on a regular row, four on a hole or a pair missing
the unselected color, and five on a pair missing a selected color.  If
(12qn) fails, (12qm) is already the local Hall branch.  The simultaneous
price argument may hence assume these smaller external matchings exist at
every row; those are precisely the transitions carrying the nontrivial
external transport in (12qk)--(12ql).

The bound (12qn) is only a necessary first layer.  In the four-seed run none
of the nine Hall-deficient row/pair cases violates it: every external graph
has matching number at least `d_t-g(t)`.  The observed deficit is the coupling
cost of adding an own-touching candidate, whose other selected label may
delete an external option.

That coupling has an exact bounded formula.  Let `G_t^own` contain the
candidates touching `S_t intersect C`.  For a matching `O` in this graph,
let `L(O)` be all selected labels occupied by its candidates, and delete from
`G_t^ext` every candidate meeting `L(O)`.  Every full matching splits
uniquely into such an `O` and a residual external matching, so

```text
nu(G_t) = max_{O matching in G_t^own}
            (|O| + nu(G_t^ext minus L(O))),   with |O|<=g(t)<=2. (12qo)
```

Thus local Hall failure is equivalent to the finitely many inequalities
`|O|+nu(G_t^ext minus L(O))<=d_t-1` for own matchings of size zero, one, or
two.  Formula (12qo) is the sharp local companion to the incidence-split
transport: the same own candidate that contributes the paired `iota=1` curl
also removes one or two labels from the external matching system.  A uniform
Hall-or-price proof can charge this bounded deletion loss against the
own-versus-external role-flow inequalities (12ql).

Normalize the bounded loss by putting

```text
m_t = nu(G_t^ext),
lambda_t(O) = m_t - nu(G_t^ext minus L(O)).
```

An own candidate contains at most one non-own selected label, so deleting the
labels of `O` lowers matching number by at most `|O|`.  Hence

```text
0 <= lambda_t(O) <= |O| <= 2,
nu(G_t) = m_t + max_O (|O|-lambda_t(O)).                  (12qq)
```

Local feasibility is exactly the gain inequality

```text
max_O (|O|-lambda_t(O)) >= d_t-m_t.                       (12qr)
```

The nine sampled Hall failures have a uniform profile.  Six have
`m_t=d_t-1` and best net own gain zero; three have `m_t=d_t-2` and best net
gain one.  Thus in every case the right side of (12qr) exceeds the best gain
by exactly one, matching the observed deficiency-one cover.  The two ways to
lose are now explicit: too few compatible own candidates, or an own
candidate whose external label is essential and therefore has deletion loss
one.  Both are root--fiber collision statements visible to `iota` and the
role census.

For `|O|=1` the loss has a standard matching interpretation.  If the own
candidate is a selected-label singleton, it deletes no external label and
has `lambda=0`, hence net gain one.  If its support is `{a,b}` with `a` a
root-own label and `b` external, then

```text
lambda({u})=1  iff every maximum matching of G_t^ext uses label b. (12qs)
```

Indeed, a maximum matching avoiding `b` survives its deletion, while one in
the deleted graph is precisely a maximum matching of the original graph
which avoids `b`.  Call such a `b` **external-essential**.  Thus a two-label
own candidate contributes net gain zero exactly when its second label is
external-essential; otherwise it contributes one.  For two compatible own
candidates, (12qq) is the corresponding two-label essential-set test.  This
reduces the local side of the conjecture to at most two root-own fibers and
the essentiality of their attached external labels—a small vertex-cover
condition via Kőnig, rather than an arbitrary matching interaction.

The sampled rows split into two transparent archetypes under (12qs).

- In the six cases with `m_t=d_t-1`, no positive-gain own choice exists.
  Three rows have no own-touching candidate at all; in the other three,
  every two-label own candidate has an external-essential second label.
- In the three cases with `m_t=d_t-2`, positive-gain own candidates exist,
  but the largest compatible positive-gain family has size one.  In one case
  a singleton-own candidate and a nonessential two-label candidate both use
  the same root-own label, so they cannot be selected together.

Thus the deficiency-one phenomenon is exactly either **essential-label
blocking** or **competition for one of the two root-own labels**.  These are
the two local configurations a uniform transport argument must charge; no
higher-order matching pathology occurs in the sample.

At zeroth order, the own transport is an Eulerian flow statement.  Let
`x_tu` be the fractional multiplicity with which candidate `u` is selected
in row `t`.  Equal own mass in (12qi) says, for every full signature `sigma`,

```text
sum_{sig(t)=sigma,u} x_tu delta_tu
  = sum_{sig(u)=sigma,t} x_tu delta_tu.                    (12qp)
```

Thus the own-touching selections form a directed fractional flow on the
selected-label block-intersection graph, balanced after quotienting roots by
`(role,n,c_pair,c_all)`.  The inequalities (12ql) refine this conservation
by every role coordinate of the shared fiber.  Formula (12qo) simultaneously
says that each such flow edge spends one of at most two root-own labels and
deletes its other label(s) from the external matching.  This Eulerian-flow
plus bounded-deletion formulation is a compact graph-theoretic statement of
the remaining uniform obstruction.

There is an exact alternating-cycle lift of (12qp).  Clear denominators in
the fractional row matchings and in the own-fiber Strassen transports.  For
each selected own-touching transition `t->u` through its unique shared label
`b`, draw a horizontal arc

```text
positive source flag (t,b)  -->  negative incoming flag (u,b).
```

For each unit of the transport (12qi), draw a vertical handoff from that
incoming flag to a source flag `(t',b')` with the same full signature and
`r_ub <= r_t'b'` coordinatewise.  The transport marginals say that every
flag-type vertex has equal indegree and outdegree.  Therefore this finite
directed multigraph decomposes into alternating closed cycles

```text
source --shared-label transition--> incoming
       --monotone signature handoff--> source -- ... .       (12qt)
```

This is the state-cycle normal form of a failed incidence-price separator.
Horizontal arcs lie in the edge-disjoint selected-label fibers of the linear
block system; vertical arcs preserve `(role,n,c_pair,c_all,iota=1)` and can
only increase the role census.  Each horizontal arc also carries the bounded
external deletion cost in (12qq).  Hence the remaining uniform theorem can
be stated without LP language: every alternating cycle system (12qt) must
incur enough essential-label deletion to trigger the Hall inequalities
(12qr), or else some monotone handoff inequality is strict and supplies the
price separator.

Low-degree analytic prices do not yet close this cycle system.  Three
restricted incidence-price classes were tested on the two original
monotonicity exceptions:

```text
mu = beta_0 + sum_j beta_j r_j, beta>=0:
  objectives 0, 0;
add arbitrary nonnegative univariate thresholds 1[r_j>=k]:
  objectives 0, 0;
add all nonnegative quadratic monomials r_j r_k:
  objectives 0, -0.5709038026.
```

The corresponding modes are `fiber-type-total-incidence-linear-farkas`,
`...-threshold-farkas`, and `...-quadratic-farkas`.  Thus first moments and
separable nonlinear role thresholds are insufficient, while a positive
quadratic collision charge repairs one case but not the final `(0,1)` case.
The surviving price requires a genuinely joint nonlinear upper set of the
five-role census, or a signed interaction whose total evaluation remains
monotone on the realizable flags.  This rules out the simplest scalar
root-incidence collision potential and locates the needed invariant at the
interaction between role coordinates.

The upper-set decomposition is not sparse either.  Take one fitted arbitrary
isotone incidence table for the last `(0,1)` case and threshold its cap
values; every superlevel set is an upper set of the realized census poset.
For 25 levels spanning all nonzero values, refitting free alpha plus a single
nonnegative upper-set coefficient always gives objective zero.  Refitting
every pair among 13 coarse superlevels also gives zero.  Therefore the final
certificate is not one or two exceptional census predicates hidden inside a
dense table: it requires a genuinely multi-threshold combination (or a new
structural identity which couples those thresholds before separation).

The alternating-cycle lift supplies such a joint threshold canonically.
Index one cycle of (12qt) so its horizontal arcs are

```text
(t_i,b_i) --> (u_i,b_i),
```

and the following vertical handoff goes from the incoming flag at `u_i` to
the next source flag at `t_(i+1)`.  Let `a_i=role(t_i)`.  Signature
preservation on the handoff gives `role(u_i)=a_(i+1)`.  Since `u_i` is an
eligible member of `F_{b_i}`, the source census satisfies

```text
r_{t_i b_i, a_(i+1)} >= 1.
```

Likewise the previous incoming census contains its horizontal predecessor
`t_(i-1)`, of role `a_(i-1)`, and the vertical handoff is coordinatewise
nondecreasing.  Therefore every source flag on the cycle obeys

```text
r_{t_i b_i, a_(i-1)} >= 1,
r_{t_i b_i, a_(i+1)} >= 1.                                (12qu)
```

When the adjacent roles differ, (12qu) forces a genuinely joint two-role
occupancy in one root-own fiber.  Thus the nonlinear interaction is not an
opaque artifact of the fitted table: it records the predecessor/successor
role pair of an alternating flag cycle.  A uniform proof may now classify
cyclic role words against the five-row fiber cap and charge every role turn
to a mixed-role collision in `c_pair` or `c_all`.

This charge has a direct capacity bound.  In the original fractional row
matching, all candidates using one selected label `b` are mutually
exclusive, so the total horizontal flow leaving any source flag `(t,b)` is
at most one.  Let `Turn` be the total cycle-flow mass at indices with
`a_(i-1) != a_(i+1)`.  At such an index (12qu) supplies two occupants of
distinct roles in `E_t intersect F_b`, hence one mixed-role collision.
Therefore

```text
Turn <= sum_t sum_{b in S_t intersect C}
          sum_{j<k} r_tb,j r_tb,k
     <= sum_t sum_{b in S_t intersect C} binom(ell_b(t),2). (12qv)
```

The right side is the root-own portion of the collision energy, paid once
per actual flag rather than once per cycle occurrence.  If `Turn=0`, then
`a_(i-1)=a_(i+1)` everywhere, so the cyclic role word has period two.  In
particular an odd-horizontal cycle with no charged collision is
role-constant.  Thus every odd nonconstant role cycle consumes positive
root-own mixed collision, exactly paralleling the once-paid collision budget
in the simultaneous port-switch lane.

Same-role multiplicity sharpens the uncharged branch.  At a no-turn index
write `a=a_(i-1)=a_(i+1)`.  If `r_{t_i b_i,a}>=2`, the source flag contains
a same-role occupant pair and can instead be charged to
`binom(r_{t_i b_i,a},2)`.  The same per-flag flow bound applies.  Combining
mixed- and same-role pairs, all cycle mass except indices satisfying

```text
a_(i-1)=a_(i+1)=a  and  r_{t_i b_i,a}=1                 (12qw)
```

is bounded by the full root-own collision energy
`sum_{t,b in S_t intersect C} binom(ell_b(t),2)`.
Consequently an entirely uncharged odd-horizontal cycle is role-constant and
every used own fiber has exactly one eligible occupant of that role.  This
is the collision-free residual normal form: the horizontal same-role
transition is the unique same-role option visible in its source census, and
all other eligible occupants in that fiber (if any) have different roles.

Define the **flat handoff graph** directly from this residual.  Its vertices
are the eighty root-own selected flags `(t,b)`.  Draw a directed edge
`(t,b)->(t',b')` when

1. `t` has exactly one eligible same-role occupant `u` in `F_b`;
2. the horizontal transition `t->u` is allowed; and
3. `(u,b)` can hand off monotonically to `(t',b')`, i.e. the two roots have
   the same full signature, `t'` also has exactly one same-role occupant in
   `F_b'`, and `r_ub<=r_t'b'` coordinatewise.

An uncharged cycle (12qw) is exactly a directed closed walk in this graph.
The first 24 four-seed pair/design instances had only 6--22 arcs, recurrent
strongly connected components of order two, four, or six, and no odd
directed closed walk.  This originally suggested

```text
FLAT-HANDOFF BIPARTITENESS (RETRACTED):
the flat handoff graph of every admissible (Q,K) has no odd directed cycle.
                                                               (12qx)
```

This is **false**, even after imposing local Hall feasibility.  In a branch-3
outer witness generated at seed 8 with selected colors `(1,2)`, roots 6 and
19 share selected label 22 and are reciprocal unique same-role occupants.
Both root signatures are

```text
(role,n,c_pair,c_all) = (triple,13,14,19),
```

and both fiber-role censuses are exactly
`{triple:1,pair-low:1,pair-other:1}`.  Thus horizontal transition
`(6,22)->(19,22)` hands back monotonically to `(6,22)` with equality: the
flat handoff graph has a directed self-loop.  Every one of the 47 local
candidate graphs in this instance passes Hall.  The witness is reproduced by
running `--seeds 9 --audit-flat-signatures`; the audit reports
`forest=False` for the offending quotient.

The earlier observed bipartition was not an affine parity of the obvious state data:
parallel class of the root and its unique neighbor, selected-label color,
and all binary digits of `(n,c_pair,c_all)` give an inconsistent `F_2`
edge-sign system across the 283 recurrent sampled arcs.  The counterexample
now shows that even the full realizable census/eligibility relation is
insufficient.  Any valid terminal must restore information discarded in
passing from (12qt), most naturally whether the horizontal edge is actually
used by the balanced fractional row matchings and its external
essential-label deletion cost in (12qq)--(12qr).

There is a smaller sufficient graph which explains the sampled parity.
Define the **flat signature graph** with vertex set the full signatures
`(role,n,c_pair,c_all)` which occur on flat flags.  Join signatures `sigma`
and `tau` when some shared-label pair `(t,b),(u,b)` is reciprocal and flat:
`t,u` have the same role, each is the other's unique same-role eligible
occupant in `F_b`, and their signatures are `sigma,tau`.  Every horizontal
step of an **uncharged closed** flat handoff walk crosses one such signature
edge.  Indeed, flatness at the source makes `u` its unique same-role
occupant; flatness at the incoming flag is forced by the same-role collision
charge, and since `t` is an occupant there, incoming uniqueness makes the
pair reciprocal.  The vertical step stays at the incoming signature.

In the first 24 sampled instances this undirected simple signature graph was
a forest, with no equal-signature reciprocal pair.
It has between three and sixteen nonisolated vertices and between two and
nine edges; in every case `|E|=|V|-number_of_components`.  Therefore every
closed projected walk has even length, which proved (12qx) for each of those
instances without inspecting the detailed handoff arcs.  This led to the
now-retracted terminal

```text
FLAT-SIGNATURE FOREST (RETRACTED):
there is no equal-signature reciprocal flat pair, and the simple quotient
of reciprocal unique-same-role shared-label pairs is a forest on full root
signatures.                                                     (12qy)
```

Multiple actual flat pairs which realize the same pair of distinct
signatures are harmless: they become one edge in the simple quotient, and
traversing between its endpoints still changes sides.  A loop is not
harmless, since it is already an odd closed projected walk; this is why its
exclusion is explicit in (12qy).  The weaker exact requirement would merely
be that the signature multigraph have no loop or odd cycle.  Seed 8 violates
even that requirement.

The economy of (12qy)—depending only on the outer eligibility graph and four
scalar root flags—was precisely its defect: it discarded the matching-flow
and deletion data which distinguish the seed-8 self-loop from an actual
global Farkas obstruction.

One role family is already excluded uniformly.  Two pair centers have the
same role exactly when their two-point blocks omit the same U1 color, hence
belong to the same marked-support group.  The blocks inside each such group
are point-disjoint (the marked-support matching constraint), so two
same-role pair centers cannot share the selected label required by a flat
edge.  Thus every edge of the flat signature graph lies in the triple-center
or hole roles.  The original 24-sample audit happened to realize only
regular-triple edges, but hole-role exclusion is **false** under the outer
axioms.  Adding the seed-free requirement that two hole blocks intersect and
have no cross-core edge is SAT in both branches; the resulting witnesses
contain reciprocal flat hole pairs.  Nevertheless all six two-color
quotients of the two targeted witnesses remain forests.  This is reproduced by
`--require-eligible-hole-pair --audit-flat-signatures`.  Only the pair-role
exclusion remains a valid uniform structural fact.  An expanded eight-seed
run in this adversarial mode
produced 48 further two-color quotients, 32 with an actual hole-role edge;
all 48 were forests (five to eighteen nonisolated signatures, at most ten
simple edges).  Seed 8 shows why that finite evidence cannot support a
uniform terminal.

The apparent connected-shape sharpening also fails.  The 24
original quotients and twelve separately regenerated hole-forced quotients
were audited by full component degree sequence.  Every component was a path,
except for one four-vertex claw with degrees `(1,1,1,3)`.  Thus the sharper
sampled statement is

```text
FLAT-SIGNATURE PATH-OR-CLAW (RETRACTED):
every nontrivial flat-signature component is a path or K_(1,3). (12qz)
```

Seed 7 already supplies a `K_(1,4)` component, and seed 8 supplies the loop
above.  Hence neither bounded branching nor an empty degree-two core follows
from the outer axioms.  The component-shape output remains a useful
regression diagnostic, but (12qy)--(12qz) are not proof targets.

The seed-8 loop identifies exactly which information was lost.  Both
orientations of the reciprocal pair can occur in a cardinality-five local
matching (forcing the indicated candidate still permits packing six).  For
row 6, using candidate 19 deletes its other selected label 8 from an external
matching and lowers the external rank from six to five.  That orientation
pays one unit of deletion.  For row 19, using candidate 6 deletes label 14,
but the external rank remains five; this reverse orientation has zero
deletion cost and therefore cannot be dismissed by (12qq) alone.

It is nevertheless not a zero incidence-price transition.  Candidate 6 in
row 19 consumes selected labels `{14,22}`, whereas the incoming own support
of row 19 is `{8,22}`.  The shared-label states cancel exactly:

```text
r_(19,22) = r_(6,22) = (1,0,1,0,1),
```

but the two secondary fiber states are

```text
r_(19,14) = (2,0,0,0,1),
r_(6,8)   = (2,0,0,1,0).                                (12ra)
```

Thus the flat graph retained the shared own flag and discarded the
nonshared-label bundle which a candidate consumes.  For an exact replacement,
attach to every transition `t->u` the signed multisets

```text
B^+(t,u) = {(signature(t), iota_tb, r_tb) : b in S_u intersect C},
B^-(t,u) = {(signature(u), iota_ub, r_ub) : b in S_t intersect C}.
                                                               (12rb)
```

The incidence part of its Farkas vector is precisely the feature-count
difference `B^+(t,u)-B^-(t,u)` (with the chosen monotone feature expansion),
while alpha records the root-signature boundary.  Any genuine failed
separator must balance these **whole bundles** across its fractional local
matchings.  The corrected structural target is therefore a hypergraph-flow
classification for balanced bundle boundaries (12rb), coupled to the
external deletion loss—not bipartiteness of the one-shared-flag projection.
The seed-8 self-loop is broken immediately by the pair-high/pair-other census
swap in (12ra).

The atomic version of this correction survives a wider falsification sweep.
The mode `--audit-bundle-boundaries` constructs the two exact tagged
multisets in (12rb) for every same-role own-touching transition and reports
literal equality, without floating optimization.  Across 20 seeds in both
branches and all three selected color pairs—120 quotients and 2,304 tested
transitions, including locally Hall-failing instances—there is no zero
bundle boundary.  This suggests the first local lemma

```text
BUNDLE ATOMIC SEPARATION:
for every same-role own-touching transition t->u,
(signature(t),B^+(t,u)) != (signature(u),B^-(t,u)).       (12rc)
```

Unlike the retracted flat terminals, (12rc) sees every label consumed by the
candidate and is not refuted by the seed-8 loop.  It only rules out a
one-transition obstruction: several nonzero bundle boundaries may still
balance in a fractional matching flow.  Hence the global problem remains a
signed hypergraph-circulation theorem, not a graph-cycle theorem.

The bundle boundary has one exact involutive character.  Candidate
eligibility is symmetric, and route reversal `T:(t,u)->(u,t)` exchanges the
two signed multisets definitionally:

```text
B^+(u,t)=B^-(t,u),  B^-(u,t)=B^+(t,u),
Delta(u,t)=-Delta(t,u),                               (12rd)
```

where `Delta` includes both the bundle feature-count difference and the
alpha root-signature boundary.  Consequently any transition flow whose
occurrence weights satisfy `x_tu=x_ut` cancels exactly.  Formal availability
of the reverse arc does **not** imply that equality—the fractional row
matchings choose oriented occurrences independently—so (12rd) locates the
remaining issue as flow reversibility.  Unlike the simultaneous owner-run
lane, B3 currently has no second canonical orientation involution: swapping
the two selected colors only permutes bundle states.  Thus the entire B3
boundary is route-odd, and an equivariant closing lemma must construct an
equal-weight occurrence pairing rather than merely reverse the formal arc.

There is no sampled two-atom escape from this characterization.  The exact
mode `--audit-bundle-pairs` hashes the full signed `Delta(t,u)` and searches
for `Delta(v,w)=-Delta(t,u)`, excluding the definitional reverse
`(v,w)=(u,t)`.  Across eight seeds in both branches and all color pairs it
tested 952 transitions and found no non-reversal opposite pair.  This
suggests

```text
BUNDLE TWO-ATOM RIGIDITY:
Delta(t,u)+Delta(v,w)=0 implies (v,w)=(u,t).              (12re)
```

Together, (12rc) and (12re) say that every balanced occurrence measure of
support at most two is the trivial symmetric pair and cancels by (12rd).
They do not exclude a three-or-more-transition circuit; finding or excluding
such circuits is the next exact hypergraph question.

The first such case is also absent in the same eight-seed sample.  A
meet-in-the-middle `--audit-bundle-triples` search allows repeated atoms and
checks the literal integer equation

```text
Delta(t_1,u_1)+Delta(t_2,u_2)+Delta(t_3,u_3)=0.          (12rf)
```

Among the 952 transitions it finds no zero triple.  Hence every sampled
nontrivial bundle circulation needs at least four transition occurrences.
This is still empirical: (12rf) is a finite-support diagnostic, not yet a
uniform lower bound or a substitute for the matching-flow constraints.

In fact the sampled support bound is unlimited.  Choose one orientation of
each unordered same-role own transition and form the integer matrix whose
columns are its `Delta(t,u)`.  The mode `--audit-bundle-rank` computes its
rank exactly over the rationals (and checks that every formal reverse arc is
present).  On the same eight-seed family, all 476 unoriented columns are
independent.  This suggests the stronger terminal

```text
BUNDLE ROUTE-PAIRING RIGIDITY:
the columns Delta(t,u), indexed by unordered same-role own transitions,
are linearly independent.                                      (12rg)
```

Indeed write a directed occurrence measure as weights `x_tu>=0`.  By
(12rd), its total boundary is

```text
sum_{{t,u}} (x_tu-x_ut) Delta(t,u).
```

Under (12rg), bundle balance forces `x_tu=x_ut` for every pair.  Thus all
small-support results (12rc), (12re), and (12rf) become corollaries, and the
arbitrary-support obstruction reduces exactly to symmetric route pairs.
This does not finish the Hall argument: a symmetric pair can still carry
matching mass, so its two external deletion losses must be coupled next.
The key gain is that no higher hypergraph circuit remains once (12rg) is
proved.

The most optimistic deletion coupling is false.  The exact mode
`--audit-bundle-deletion` computes both external matching ranks before and
after deleting a transition partner's nonshared selected labels, and also
checks whether each oriented candidate can be forced into a required-size
local matching.  In the 476-pair run the bidirectional loss table was

```text
(lambda_tu,lambda_ut): (1,1) 225, (0,1) 96,
                       (1,0)  94, (0,0) 61.
```

Sixty of the 61 zero-zero pairs can be forced into degree-`d` matchings in
both orientations (the remaining pair fails in one orientation).  Thus
neither positive paired deletion nor local occurrence infeasibility closes
the T-symmetric sector.  Let `Z` be the graph of zero-zero unordered route
pairs.  The corrected post-rank terminal is

```text
ZERO-LOSS SYMMETRIC FLOW EXCLUSION:
no balanced family of fractional degree-d row matchings can place positive
symmetric occurrence mass on Z after the charged transitions are removed.
                                                               (12ri)
```

Statement (12ri) must use simultaneous row capacities or the remaining
outer routing equations: every edge of `Z` is locally viable in isolation.
This is the B3 analogue of the transpose-even diagonal sector in the
simultaneous owner-run lane.

The zero-loss graph is itself extremely sparse.  In the eight-seed audit its
61 edges form 53 isolated `K_2` components and four three-vertex paths; the
maximum degree is two and there is no cycle.  The deletion audit now prints
these exact component degree sequences.  This suggests

```text
ZERO-LOSS PATH FOREST:
every component of Z is K_2 or P_3.                           (12rj)
```

Under (12rj), (12ri) reduces componentwise to one symmetric route weight on
an isolated pair, or two weights meeting at the middle root of a three-root
path.  The local feasibility checks show these components cannot be deleted
one edge at a time; the remaining simultaneous equation must constrain the
completion mass at their endpoint and middle rows.

A separate pair-level simultaneous LP cannot improve this.  For a `K_2`
edge, once both orientations occur in some local degree-`d` matching, the two
row matching polytopes are a Cartesian product, so the two occurrences can
be mixed independently with equal positive weight.  At the middle row of a
`P_3`, if each incident candidate is individually feasible, convexly mixing
their witnessing matchings gives arbitrarily small positive marginal to
both.  Therefore only a global normalization or conservation identity can
force one of these weights to vanish.  This rules out another local-capacity
detour and identifies (12ri) with the conservation obligation in the shared
tagged-bundle reversal lemma.

Most sampled instances die before global conservation is invoked.  The mode
`--audit-zero-loss-restriction` deletes every own-touching candidate outside
`Z`, retains all external candidates, and recomputes the exact local matching
capacity at every row.  In the eight-seed run, 45 of 48 quotients then have
at least one row below demand.  The three restricted-Hall survivors were

```text
(branch,seed,colors,|E(Z)|) = (3,7,(1,2),0),
                              (4,5,(0,1),1),
                              (4,5,(0,2),0).             (12rk)
```

Therefore the zero-charge sector has a sharp empirical dichotomy: a direct
restricted Hall failure, or one of a tiny set of external-completion designs
where the full bundle conservation equations must supply the contradiction.
The survivor with `|E(Z)|=1` is the only sampled case which actually carries
a symmetric zero-loss own route; the other two survive using external
candidates alone.  A uniform proof should first derive the restricted Hall
alternative and then classify its equality case, rather than apply the full
global ledger to all rows indiscriminately.

All three equality cases are killed by the full normalized bundle ledger.
The mode `--audit-full-bundle-primal` introduces one marginal for every row
candidate, imposes row sum `d_t`, every selected-label capacity at most one,
and equality of every alpha and tagged bundle coordinate.  HiGHS reports the
system infeasible for each survivor in (12rk), as it does for the other
sampled quotients.  Consequently the sampled two-stage terminal is complete:

```text
restricted Hall failure, or
normalized full-bundle primal infeasibility.                    (12rl)
```

This last check is a floating LP status, not an exact certificate or a
uniform proof.  Its value is localization: only the three restricted-Hall
equality patterns need an analytic conservation argument.  Producing a
small dual supported on their private bundle rows is the next proof-facing
experiment.

The first equality pattern already has such a dual.  The mode
`--audit-full-bundle-dual` minimizes the `L_1` norm of a Farkas alternative,
then rounds and rechecks every integer column inequality and the scalar
contradiction exactly.  For `(3,7,(1,2))` it finds 35 unit coefficients:

```text
negative row demands:  3, 8, 17, 25                         (sum 21);
positive capacities:   (3:{13,14,23}),
                       (8:{13,14,19,23}),
                       (17:{17,19,20,23}),
                       (25:{12,13,14}),
                       (26,32,33,38,44,45): label 11       (sum 20);
negative bundle rows:  11 external tagged states.          (12rm)
```

The eleven states have signatures/censuses

```text
(0,11,10,16):(1,0,0,0,0), (0,13,12,18):(0,0,0,1,1),
(0,15,22,32):(0,0,0,0,1), (0,16,22,33):(1,0,0,1,0),
(2,20,34,48):(2,1,0,0,1), (2,21,29,48):(1,1,0,0,0),
(3,20,31,50):(2,0,0,0,0), (3,20,36,50):(3,0,0,0,1),
(3,21,38,59):(2,0,0,0,0), (4,19,28,45):(1,1,0,0,1),
(4,19,33,51):(2,0,0,0,0),
```

all with `iota=0` and coefficient `-1`.  Bundle conservation transports the
four rows' total demand 21 into the listed twenty unit capacity slots, giving
the exact scalar `-21+20=-1`; the verified column coefficients are
nonnegative.  Thus the branch-3 survivor is an integer capacity-transfer
contradiction, not a numerical artifact.  The two branch-4 survivors produce
dense fractional `L_1` duals (613 and 620 nonzeros), so naive rounding does
not expose their structure.

A direct integer Farkas search does.  The mode `--audit-integer-bundle-dual`
allows the negative scalar to choose its natural integral scale, then rechecks
the rounded certificate against every original column.  On the same three
survivors it returns respectively

```text
branch 3, colors (1,2): 35 nonzeros, coefficients in {-1,1};
branch 4, colors (0,1): 53 nonzeros, coefficients in {-2,-1,1,2};
branch 4, colors (0,2): 51 nonzeros, coefficients in {-2,-1,1,2}.   (12rn)
```

All three have a strictly negative integer scalar and nonnegative coefficient
on every candidate column.  The branch-4 ledgers use six negative demand rows,
13 and 11 signed external bundle rows, and 34 positive capacity rows.  Thus
their weighted demand/capacity totals are respectively `47>46` and `36>35`.
Every feature multiplier is an `iota=0` external tagged-bundle equality; no
alpha equality is used.  Hence all three ledgers have the same analytic form:
signed bundle conservation transports an integer combination of row demands
into a collection of label slots whose capacity is smaller by exactly one.
Thus every survivor of the restricted exact Hall audit has a modest exact
integral certificate.  This is still a finite sampled statement: the
remaining proof task is to recognize these signed bundle transfers uniformly,
not to regard the three solver outputs themselves as the branch-3/4 theorem.

The reusable analytic statement exposed by these ledgers is elementary.  Let
`Delta_f(t,u)` be the external bundle boundary of candidate `u` at row `t`,
and let `S(t,u)` be its selected-label support.  If integers `a_t,m_f` and
nonnegative integers `c_tb` obey

```text
a_t + sum_f m_f Delta_f(t,u) + sum_{b in S(t,u)} c_tb >= 0
                                                        for every (t,u),
sum_t a_t d_t + sum_{t,b} c_tb < 0,                    (12ro)
```

then no normalized bundle-conserving matching flow exists.  Indeed, multiply
the first line by its nonnegative candidate marginal and sum.  Row
normalization replaces the first term by `sum a_t d_t`, bundle conservation
kills the second, and the unit label capacities bound the last term above by
`sum c_tb`, contradicting the second line.  Thus the remaining uniform B.3
task has a precise combinatorial form: construct the `(12ro)` weights from
the restricted-Hall equality patterns without solving an instance-specific
MILP.

For the certificates in `(12rn)`, `(12ro)` has an equivalent and more local
form.  Since every used feature has `iota=0`, define `p_t(b)` to be its integer
multiplier for the state `(sigma_t,0,census_t(b))` when `b` is external to
root `t`, and zero when `b` belongs to `t`.  Then the bundle contribution of
a candidate route `t -> u` is exactly

```text
 sum_{b in B_u cap selected} p_t(b)
-sum_{b in B_t cap selected} p_u(b).                         (12rp)
```

Thus the sampled certificates use no mysterious global coordinate: they are
integer external-label potentials, supplemented by nonnegative prices on the
row-label capacity slots.  Bundle conservation is precisely cancellation of
the two transport sums in `(12rp)`.  A uniform equality-case proof may
therefore be sought as a potential assignment on the finite root/census state
graph, with the one-unit deficit supplied by the selected demand rows.

The potential cannot be compressed to the obvious additive statistics.  The
diagnostic mode `--audit-linear-bundle-dual` restricts

```text
p_t(b) = beta_0 + sum_{j=1}^4 beta_j sigma_t(j)
                  + sum_{r=0}^4 gamma_r census_t(b,r)          (12rq)
```

on external labels, while still allowing arbitrary demand-row weights and
arbitrary nonnegative capacity prices.  HiGHS finds this restricted dual
system infeasible for all three survivors.  This is another sampled floating
no-go, not an exact impossibility theorem, but it rules out the most tempting
uniform ansatz: the state potential must distinguish joint signature/census
patterns nonlinearly (or be constructed by a combinatorial propagation rule)
rather than by a single additive score.

The sparse integer ledgers in the original eight-seed run nevertheless have a
simple label-level skeleton.
The integer audit now computes the minimum selected-label hitting sets of the
negative demand roots' own supports.  They are unique:

```text
branch 3, demand roots {3,8,17,25}:       pivot {11};
branch 4, demand roots {5,6,8,13,20,25}: pivots {6,13};
branch 4, demand roots {6,7,11,14,18,22}: pivots {22,23}.      (12rr)
```

Every positive capacity outside a demand root is priced at a pivot label,
except the single slot `(root 27,label 7)` in the last pattern.  That exception
is a one-step relay: label 7 is the nonpivot member of demand root 14's own
support `{7,22}`.  Thus those three equality certificates are respectively a
one-pivot star, a two-pivot network, and a two-pivot network with one secondary
relay.  This suggested a substantially smaller classification target than
arbitrary joint state potentials, but the exact three-item taxonomy is
run-local.

A fresh twenty-seed run with `PYTHONHASHSEED=0` is the required correction.
The outer Z3 model enumeration is not canonical across differently hashed
processes; the script now warns unless that deterministic setting is present.
The widened run had only two
restricted-Hall survivors, the old `(3,7,(1,2))` pattern and a new branch-3
pattern `(3,12,(0,1))`.  The latter has a much smaller exact certificate:
13 nonzeros, two unit demand rows, two signed external bundle states, and nine
unit capacities, again with scalar `-1`.  Its unique pivot is label 2.

This new pattern **refutes** the equality asserted in the former `(12rs)`.
Pivot 2 occurs at roots `{2,10,18,35,42}`; roots `{2,10,18}` are on the B0
side, but only `{2,10}` carry negative demand weight.  The surviving sampled
statement is the strict localization

```text
every negative demand root is a triple/hole root whose own support meets
the certificate's pivot set; equality need not hold.          (12rs*)
```

The profile audit now reports both this inclusion and whether equality happens
in a particular certificate.  The pivot/relay language survives, but the
demand subset must itself be part of the propagated state, not inferred from
pivot incidence alone.

The coefficient-two demand weights in the branch-4 ledgers are the cost of
this canonical small skeleton, not an absolute necessity.  Constraining the
original run's pivot-incident demand set to unit weights makes both branch-4
integer duals
infeasible.  If arbitrary unit-weight demand rows are allowed instead, exact
certificates reappear, but grow from 53/51 to 96/100 nonzeros, require three
or four pivot labels, and include pair-side demand roots.  The compact
two-pivot B0-only ledgers are therefore the better uniform target even though
they require one extra transport layer on some roots.

The compact ledgers are much closer to identities than their size suggests.
The integer audit now evaluates the left side of `(12ro)` on every candidate
column and lists every positive-slack exception.  The exact distributions are

```text
branch 3: 766 of 770 columns tight; 4 have slack 1;
branch 4, first pattern: 744 of 752 tight; 6 have slack 1, 2 slack 2;
branch 4, second pattern:742 of 752 tight; 10 have slack 1.     (12rt)
```

Thus 2252 of the 2274 candidate inequalities are equalities.  The audit
prints the remaining 22 ordered routes explicitly.  This changes the likely
proof architecture: construct an exact joint-state transport identity on the
pivot/relay network, then verify nonnegativity on a bounded exceptional-route
alphabet.  Trying to guess dozens of unrelated capacity prices obscures this
near-equality structure.

The new 13-term survivor strengthens rather than weakens `(12rt)`: 773 of its
778 columns are tight and the other five have slack one.  All five exceptional
sources are pivot-incidence roots.  Hence the robust observation is not the
original numbered-root list but the flat-connection phenomenon itself.

The original 22 exceptions are localized as well.  Every exceptional source
root has
an own support meeting the pivot set, except branch 4's single source root 46,
whose support is the relay label `{7}` from `(12rr)`.  Thus no route starting
outside the pivot/relay incidence neighborhood has positive slack.  The
exceptional alphabet is not merely small numerically: it lives on the same
canonical labeled neighborhood that determines the demand rows.

There is a useful connection form of the same calculation.  Put
`q_t(b)=p_t(b)+c_tb`, where `c_tb` is the nonnegative capacity price.  Then
every candidate route obeys the exact integer equation

```text
a_t + sum_{b in B_u cap selected} q_t(b)
    - sum_{b in B_t cap selected} p_u(b) = epsilon(t,u),       (12ru)
```

with `epsilon=0` on the tight columns and positive only on the exceptional
routes listed by the audit.  Thus the certificate is a flat root-to-port
transport connection away from a localized curvature set for the `iota=0`
ledgers above.  The scalar
contradiction is its one-unit capacity defect after summing the flat transport
against a normalized matching flow.  This is also the closest B.3 dictionary
to the simultaneous-routing lane's connection/holonomy language: `p` is the
incoming labeled potential, `q` the capacity-corrected outgoing potential,
and `epsilon` the localized curvature.  This `p,q` form is not asserted for
certificates using alpha or `iota=1` states.

The proposed pivot-flat generalization did not survive its next required
test.  A deterministic 32-seed run found eleven restricted-Hall survivors.
Seven obtained exact integer certificates within the 60-second per-instance
limit and four integer searches timed out.  Among the five new solved
branch-4 patterns, some certificates use alpha rows, some use `iota=1`
bundle states, some put demand on pair-side roots, and their capacity support
is not controlled by a two-label pivot set.  Therefore the following former
conjecture is **REFUTED**:

```text
PIVOT-FLAT CERTIFICATE CONJECTURE.                           (12rv, false)
```

What survives in the L1-solved models is the full-state flatness, not the
pivot support.  Every one of the seven solved certificates has scalar `-1`,
coefficients of absolute value at most two, and between two and ten
positive-slack candidate columns; all other columns satisfy the corresponding
full `(12ro)` expression with equality.

A separate bounded-feasibility mode then tested whether coefficient bound two
itself was uniform.  It is not: the branch-3 survivor `(3,21,(1,2))` is
infeasible under that bound, while four other searches time out.  Moreover,
arbitrary bound-two certificates found for the easy instances are dense and
can have dozens of positive-slack columns.  Thus small coefficients and
near-flatness are distinct objectives.  The honest replacement target is

```text
FULL-STATE SPARSE-CURVATURE CERTIFICATE:
every restricted-Hall survivor has a scalar -1 integral (12ro) certificate
whose positive-curvature support is a bounded, locally classifiable route
alphabet, allowing alpha and both iota states.                (12rv*)
```

The unresolved L1 searches mean `(12rv*)` remains conjectural.  They are the
next computational targets; no pivot or coefficient-two restriction should
be imposed on their duals.

The first unresolved model is already a hard counterprofile to this strategy.
For deterministic survivor `(3,21,(1,2))`, HiGHS reports the integer dual
infeasible under coefficient bounds 2, 3, 4, and 5.  A 300-second unrestricted
integer L1 search finds no incumbent.  The continuous L1 optimum exists, but
has 607 nonzero rows; among its 772 candidate columns, 688 are tight and 84
have positive slack (maximum about `3.277`).  Record this as

```text
HARD FULL-STATE COUNTERPROFILE:
the current normalized bundle ledger can be infeasible while its available
Farkas dual is dense, high-denominator, and broadly curved.              (12rw)
```

The bound-infeasibility and timeout statements are solver diagnostics, not
formal UNSAT certificates, and `(12rw)` does not rule out an undiscovered
sparse integral dual.  It does rule out promoting `(12rv*)` from a hope to a
uniform mechanism on present evidence.  Certificate-pattern mining has now
passed its useful stopping point: a proof must either derive an additional
design identity that eliminates this hard equality model before the full
ledger, or prove a structural integrality/certificate theorem not visible in
the sampled duals.

Primal ablation supplies exactly that additional identity and reverses the
misleading lesson of the dense dual.  The mode
`--audit-bundle-primal-ablation` separately retains alpha equalities, external
(`iota=0`) bundle equalities, and internal (`iota=1`) bundle equalities.  On
**all eleven** restricted-Hall survivors in the deterministic 32-seed run it
reports the identical profile

```text
rows only: feasible;                 alpha only: feasible;
internal bundles only: feasible;     alpha + internal: feasible;
external bundles only: infeasible;   all bundles/full: infeasible. (12rx)
```

Thus the external bundle layer is the unique load-bearing conservation family
in this ablation: alpha and internal states are neither sufficient alone nor
together, while external states alone already give the contradiction.  The
607-row full-state dual in `(12rw)` is therefore a coordinate artifact of L1
optimization, not evidence that alpha/internal geometry is essential.

The corrected uniform target is consequently simpler and more robust than
both false conjectures `(12rv)` and `(12rv*)`:

```text
EXTERNAL-BUNDLE CAPACITY TRANSFER:
every restricted-Hall equality model is infeasible after imposing only the
iota=0 bundle conservation equations, row demands, and label capacities.
                                                               (12ry)
```

Statement `(12ry)` restores the local transport form `(12rp)` for every
sampled hard model, without any pivot restriction or small-certificate claim.
The proof problem is now to derive external-state capacity loss directly—by a
combinatorial transport or Hall argument—rather than to reconstruct whichever
dense Farkas basis an LP happens to choose.

The external state itself admits one final, uniform compression.  The mode
`--audit-external-coarsening` groups external bundle equations after dropping
or retaining chosen coordinates.  Write

```text
kappa_sel(t) = selected-label pair-collision count at root t,
kappa_all(t) = all-label pair-collision count at root t,
n_r(t,b)     = number of candidates of role r containing label b.
```

For all eleven deterministic survivors, conservation indexed only by

```text
(kappa_sel(t), kappa_all(t), n_0(t,b),...,n_4(t,b))            (12rz)
```

already makes the normalized primal infeasible.  Root type and candidate
count—the first two coordinates of the old signature—are unnecessary.
Moreover `(12rz)` is coordinatewise minimal on the hard survivor
`(3,21,(1,2))`: either collision scalar paired with the full census is
feasible, and deleting any one of the five census coordinates from the
collision-pair state is feasible.  Thus the controlling object is genuinely
joint in exactly seven scalar coordinates.  This sharpens `(12ry)` to a
concrete theorem interface: prove capacity loss for external labels classified
by the two collision inventories and their complete five-role neighborhood
census, with no endpoint-role or raw candidate-count decoration.

Concretely, for a seven-coordinate state `s` define the route boundary

```text
E_s(t,u) = #{b in B_u cap selected : b notin B_t and state_t(b)=s}
           -#{b in B_t cap selected : b notin B_u and state_u(b)=s}.
```

The only global equations required by `(12rz)` are

```text
sum_(t,u) x_(t,u) E_s(t,u) = 0                 for every state s. (12rza)
```

Together with `sum_u x_(t,u)=d_t`, nonnegativity, and the row-label capacities
`sum_{u:b in B_u}x_(t,u)<=1`, these equations are already infeasible in all
eleven models.  This is the proof-facing formulation: `(12rza)` says that a
fractional matching flow transports every collision-pair/role-census class
without net creation, while the capacity ledger says some class must lose a
unit.  No reference to alpha endpoints, internal labels, or an LP dual is
needed in the statement.

Two further diagnostics set the boundary of this compression.  Re-solving the
L1 dual after projecting to the seven-coordinate state does not generally
produce a short certificate.  The hard survivor `(3,21,(1,2))` has a floating
optimum with L1 norm about `2104.177`, 643 nonzero rows, and 110 positive
column slacks among 772 columns (maximum slack about `19.401`).  Even two of
the three survivors in the deterministic eight-seed prefix have 611 and 624
nonzero rows; only `(3,7,(1,2))` has a 35-row integral certificate.  Thus

```text
SEVEN-STATE DUAL CAUTION:
minimality of the primal state does not imply sparsity or integrality of its
Farkas dual.                                                    (12rzb)
```

This is a solver profile, not a lower bound on all certificates.  It confirms
that `(12rza)`, rather than the observed dual basis, remains the appropriate
proof interface.

A greedy deletion audit also fails to expose a small hidden transport circuit.
On the hard survivor, 300 of the 361 seven-state conservation equations remain
in a deletion-irreducible infeasible subsystem (the row equations and label
capacities are kept throughout):

```text
HARD SEVEN-STATE CORE PROFILE:
the greedy irreducible core retains 300/361 state classes.       (12rzc)
```

Irreducibility here is relative to that deletion order, so `(12rzc)` neither
proves minimum core size nor rules out a different compact nonlinear argument.
It does rule out treating the first greedy core as evidence for a bounded
finite circuit.  The next step must exploit an algebraic relation among the
seven statistics or a direct Hall/transport inequality across many state
classes at once.

The most direct low-moment algebraic ansatz also fails.  The mode
`--audit-polynomial-collision-census-dual` restricts every state multiplier to
one common polynomial of total degree at most two in
`(kappa_sel,kappa_all,n_0,...,n_4)`, while still allowing arbitrary demand-row
weights and nonnegative capacity prices.  On both branch-4 survivors in the
deterministic eight-seed prefix, HiGHS reports this quadratic dual infeasible
(and likewise reports the linear subcase infeasible):

```text
COMMON QUADRATIC STATE POTENTIAL does not certify the sampled branch-4
external-capacity obstructions.                                  (12rzd)
```

The branch-3 quadratic solve returned an indeterminate numerical status, so
no claim is made there.  Statement `(12rzd)` is a floating-model no-go, but
the two clean failures already refute a uniform proof based on one quadratic
moment score of the seven coordinates.  Higher-degree fitting is not a
meaningful next step without an independently derived algebraic identity.

Allowing nonlinear lookup tables coordinate by coordinate does not repair the
loss.  The mode `--audit-categorical-collision-census-dual` first permits

```text
p(s) = sum_j f_j(s_j)
```

with an arbitrary table `f_j` for every observed value of each of the seven
coordinates.  This additive categorical dual is infeasible on **all eleven**
deterministic survivors.  Adding every pair table,

```text
p(s) = sum_j f_j(s_j) + sum_(j<k) f_jk(s_j,s_k),
```

certifies six survivors, but is cleanly infeasible on branch-4 survivor
`(4,5,(1,2))`; four further pairwise solves, including hard survivor
`(3,21,(1,2))`, return an indeterminate HiGHS status.  Therefore

```text
PAIRWISE-CENSUS NO-GO:
neither separate coordinate tables nor all pairwise contingency tables give
a uniform external-capacity certificate.                         (12rze)
```

Only the clean infeasible instance is needed for the pairwise no-go; the four
indeterminate solves carry no mathematical claim.  Together `(12rzd-e)` show
that the live object is not a scalar moment or a collection of one- and
two-coordinate marginals.  A proof must retain a genuinely higher-order joint
private state, or derive a new identity that makes such joint information
redundant.  Blindly adding third-order tables would merely approach an
overparameterized encoding of the original arbitrary state potential and is
not a structural reduction.

A bounded third-order checkpoint identifies what the easier pairwise failure
was missing without pretending to solve the hard model.  Number the state
coordinates as

```text
0=kappa_sel, 1=kappa_all, 2=n_0, 3=n_1, 4=n_2, 5=n_3, 6=n_4.
```

On `(4,5,(1,2))`, adding just one arbitrary triple table atop all pairwise
tables succeeds for exactly the ten tested triples

```text
(kappa, n_0, n_r), r=1,2,3,4, for either collision scalar kappa;
(kappa, n_2, n_4),            for either collision scalar kappa. (12rzf)
```

Thus the first genuine interaction is collision-conditioned coupling between
two role populations, not an unstructured cubic moment.  But `(12rzf)` is not
uniform: on hard survivor `(3,21,(1,2))` none of the 35 single-triple
augmentations produces a feasible dual after removing lookup-table gauge
dependencies.  Ten are reported cleanly infeasible and 25 remain numerically
indeterminate.  Accordingly no single-triple no-go is claimed for the hard
model, and no fixed triple is promoted as a theorem target.  The useful
conclusion is narrower: the easy branch-4 obstruction exposes a concrete
collision/two-role interaction, while the hard obstruction still requires a
richer joint private ledger.  This is the stopping point for categorical
feature escalation.

There is an exact occurrence-level realization of the interaction isolated in
`(12rzf)`.  For a selected label `c`, put
`N_c(t)=sum_r n_r(t,c)`.  By definition of selected collision count,

```text
kappa_sel(t)
 = sum_(c selected) binom(N_c(t),2)
 = sum_(c selected) [sum_r binom(n_r(t,c),2)
                     + sum_(r<s) n_r(t,c)n_s(t,c)].           (12rzg)
```

The identical formula gives `kappa_all(t)` after extending the role census to
all labels.  Thus a collision-conditioned two-role state can be expanded into
flags carrying

```text
(transported external label b,
 collision-witness label c,
 unordered pair of candidate roles r,s).
```

Equation `(12rzg)` is exact, not sampled.  It does **not** linearize an
arbitrary lookup table in `kappa`; rather, it identifies the occurrence space
on which a nonlinear/private proof must operate.  The next proof-facing target
is therefore a double-labelled flag transport: pair creation and destruction
of these `(b,c;r,s)` flags along `t -> u`, with row-label capacity charging the
transported `b`.  Such a ledger retains precisely the collision/two-role
coupling seen in `(12rzf)` and has a chance to compose with the squad's
resolved-label/private-activation ledgers; a scalar collision moment does not.

The double-label proposal has a sharp, symmetry-respecting capacity test.
For selected `c` and roles `r<=s`, let

```text
C_t(c;r,r) = binom(n_r(t,c),2),
C_t(c;r,s) = n_r(t,c)n_s(t,c)                 (r<s).
```

For an unordered selected-label pair `q={b,c}`, define the route boundary

```text
F_(q;r,s)(t,u)
 = sum_(b in (B_u cap selected) minus B_t)
       sum_(c selected : {b,c}=q) C_t(c;r,s)
 - sum_(b in (B_t cap selected) minus B_u)
       sum_(c selected : {b,c}=q) C_u(c;r,s).                 (12rzh)
```

Mode `--audit-double-label-flag-primal` imposes only row demands, row-label
capacities, and conservation

```text
sum_(t,u) x_(t,u) F_(q;r,s)(t,u) = 0
```

for every unordered `q` and role pair.  This primal is infeasible on **all
eleven** deterministic restricted-Hall survivors, including hard survivor
`(3,21,(1,2))`.  Ordering `(b,c)` is unnecessary: the ordered refinement is
also infeasible, but the unordered projection already suffices.  Conversely,
each of the following projections is feasible on all eleven:

```text
forget c;  forget b;  retain only 1[b=c];  retain only (r,s).
```

Record the sampled theorem interface as

```text
UNORDERED DOUBLE-LABEL FLAG CAPACITY TRANSFER:
conservation of ({b,c},r,s) collision flags is incompatible with the row
demands and private label capacities.                            (12rzi)
```

Conservation has no additional design hypothesis: swapping the route gives

```text
F_(q;r,s)(u,t) = -F_(q;r,s)(t,u),
```

definitionally.  Hence the actual symmetric residual adjacency, whose
occurrence weights satisfy `x_tu=x_ut`, cancels `(12rzh)` pairwise over
unordered routes exactly as in `(12rd)`.  The relaxed primal deliberately does
not impose edgewise symmetry; it retains only these flag consequences, so its
infeasibility is the stronger statement needed to exclude an actual symmetric
selection.

The mathematical gap is instead to prove the **capacity-transfer** assertion
`(12rzi)` uniformly, without relying on the sampled floating LP.  Both distinct
label identities are essential, while their order is not.  This is exactly
the occurrence-level shape expected of a two-label incidence handshake and is
substantially more proof-facing than the arbitrary seven-coordinate state
potential `(12rza)`.

The unordered flag matrix is close to, but not at, route-pairing rigidity.
Choose one orientation of every eligible unordered route and use the
`F_(q;r,s)` as its column.  A numerical rank audit on the eleven survivors
gives

```text
label             columns   rank   nullity
(3,7,12)             385      365      20
(3,12,01)            389      362      27
(3,21,12)            386      359      27
(4,1,01)             384      364      20
(4,1,12)             384      363      21
(4,3,01)             381      368      13
(4,4,02)             386      362      24
(4,5,12)             384      356      28
(4,10,01)            376      360      16
(4,15,01)            385      367      18
(4,15,02)            385      368      17.                     (12rzj)
```

In nine models every column lacks a flag row private to that column; in the
other two, only one column has one.  Thus neither private-row peeling nor full
column independence proves `(12rzi)`.  The surviving object is nevertheless
small relative to the roughly 380-route ambient space: a 13--28 dimensional
circulation kernel.  Since `(12rzj)` uses floating numerical rank it is only a
diagnostic, not an exact kernel theorem.  It refines the uniform target to:
classify the unordered two-label flag kernel structurally, then prove that no
nonnegative degree-normalized kernel point respects all private label
capacities.

The flag boundary has an exact tensor factorization.  Let `ell_t` be the
selected-label indicator of `B_t`, let `ell_(u-minus-t)` be the indicator of
`(B_u cap selected) minus B_t`, and let `P_t` be the collision-profile tensor
with coordinates `P_t(c;r,s)=C_t(c;r,s)`.  Before forgetting label order, put

```text
G(t,u) = ell_(u-minus-t) tensor P_t
         - ell_(t-minus-u) tensor P_u.                         (12rzk)
```

Then `F(t,u)` in `(12rzh)` is exactly the image of `G(t,u)` under
symmetrization of its two label slots, leaving the role-pair slot fixed.  This
makes `F(u,t)=-F(t,u)` immediate.  It also identifies the circulation kernel
as a symmetrized tensor-wedge kernel, rather than an arbitrary 700-row matrix
kernel.

The cheapest quotient explanation is absent: on all three deterministic
eight-seed survivors, no two unoriented route columns are equal, so none of
the 18--21 sampled null directions is a two-route exchange.  Combined with
the absence of private flag rows, this says a proof of `(12rzi)` must use a
genuine multi-route tensor relation.  A useful next algebraic target is to
classify the minimal-support relations among the symmetrized wedges `(12rzk)`
and show that every such relation has a positive private-capacity price.

The smallest relation is now explicit.  Suppose three mutually eligible roots
`L,H,O` have selected supports

```text
B_L cap selected = {a},
B_H cap selected = {b},
B_O cap selected = {a,b},                a != b.
```

Then `(12rzk)` gives, for every unordered label pair and role pair,

```text
F(L,H) = F(L,O) - F(H,O).                              (12rzl)
```

Indeed `L -> O` transports only `b`, so its flag tensor is
`sym(e_b tensor P_L)`; `H -> O` transports only `a`, giving
`sym(e_a tensor P_H)`; and `L -> H` is their difference.  The profile `P_O`
drops out completely.  Thus `(12rzl)` is an exact Boolean support-triangle
identity, not a sampled rank coincidence.

The two branch-4 survivors in the deterministic eight-seed prefix contain
respectively three and two independent support-triangle relations of this
form.  A pivoted fundamental basis exposes the three-route circuits on roots
`(31,33,40)` for colors `(0,1)` and `(29,42,35)` for colors `(0,2)`, with
roles respectively `pair-low`, `pair-high`, `pair-other`.  The branch-3
survivor has no support triangle, so these explain only a proper subspace of
the full kernel.  The capacity interaction is nevertheless concrete: at root
`L`, both candidates `H` and `O` spend label `b`; at root `H`, both candidates
`L` and `O` spend label `a`.  Hence the tensor kernel's smallest generator is
already aligned with the private slots that must price it.  The next uniform
statement should quotient these singleton-union triangles and classify the
residual kernel, rather than treating all null directions as opaque LP
artifacts.

The collision witness and its role pair can in fact be removed completely
from the sampled capacity obstruction.  For an oriented eligible route
`t -> u`, define the root--label half-atom boundary

```text
A(t,u)
 = sum_(b in (B_u cap selected) minus B_t) e_(t,b)
   - sum_(b in (B_t cap selected) minus B_u) e_(u,b).       (12rzm)
```

Definitionally `A(u,t)=-A(t,u)`.  Consequently every symmetric residual
selection conserves every `(root,label)` coordinate of `(12rzm)`, without a
collision expansion or any design hypothesis beyond route symmetry.  Mode
`--audit-half-atom-primal` retains only row demands, the original private
root--label capacity inequalities, and conservation of `(12rzm)`.  On all
eleven restricted-Hall survivors in the 32-seed corpus this smaller primal
is infeasible:

```text
(3,7,12): 452;  (3,12,01): 447; (3,21,12): 444;
(4,1,01): 453;  (4,1,12): 451;  (4,3,01): 453;
(4,4,02): 448;  (4,5,12): 444;  (4,10,01): 453;
(4,15,01): 449; (4,15,02): 451 half-atom coordinates.       (12rzn)
```

Every solve returns HiGHS `Infeasible`.  As elsewhere, the compact label
writes the branch, deterministic seed, and selected color pair.

On the three survivors in the separately recorded eight-seed rank run, the
half-atom column matrix has respectively ranks
`365,355,358`, exactly the ranks of the unordered double-label flag matrices;
their nullities are `20,21,18`.  This numerical rank equality is diagnostic,
not a proved row-space identity.  The infeasible primal `(12rzn)` is the
important reduction: the sampled terminal no longer needs the collision
identity `(12rzg)`, role populations, or a classification of the
symmetrized tensor-wedge kernel.  Its proof-facing target is now the direct
root--label handshake:

```text
HALF-ATOM CAPACITY TRANSFER:
no nonnegative degree-normalized route flow can simultaneously conserve
A(t,u) and respect every private root--label capacity.          (12rzo)
```

This is still a sampled abstract-satisfiability no-go, not a uniform theorem.
But it is stated entirely in the two objects already present in the original
matching relaxation: selected-label transport and the private capacity of a
root.  Any uniform proof of `(12rzo)` supersedes `(12rzi)`; the larger
double-label ledger remains useful only if the half-atom inequality itself
needs a collision-based derivation.

The exact dual has a clean uniform statement.  Let `alpha_t` and `phi_tb` be
rational prices, let `lambda_tb >= 0`, and suppose every eligible oriented
route satisfies

```text
alpha_t
 + sum_(b in (B_u cap selected) minus B_t) phi_tb
 - sum_(b in (B_t cap selected) minus B_u) phi_ub
 + sum_(b in B_u cap selected) lambda_tb >= 0.               (12rzp)
```

If in addition

```text
sum_t d_t alpha_t + sum_(t,b) lambda_tb < 0,                 (12rzq)
```

then `(12rzo)` follows immediately: multiply `(12rzp)` by the nonnegative
route weights and sum.  The `phi` terms vanish by half-atom conservation,
the `alpha` terms become the row demands, and the `lambda` terms are at most
their private capacities.  This is the easy, purely algebraic direction of
Farkas separation and is valid for arbitrary finite root and label sets; it
is the uniform **half-atom price lemma** needed by a future Lean interface.
The remaining mathematical problem is to construct prices satisfying
`(12rzp-q)` from the B.3 outer design identities rather than from a solved
finite instance.

Mode `--audit-half-atom-dual` now rationalizes the floating separators and
checks `(12rzp-q)` with exact `Fraction` arithmetic on every route column.
All eleven 32-seed survivors have exact certificates with contradiction
scalar `-1` and minimum route slack `0`.  Three are integral (supports of
sizes 30, 13, and 34); the other maximum denominators are respectively
`38,6,78,5787,206184,3778,16461,11811`.  Thus the sampled claim no longer
rests only on the HiGHS infeasibility status.  The large denominators and
dense supports in the hard branch-4 instances are also negative structural
evidence against guessing one universal small local cut: a proof should
derive the price function from a global design potential or prove the primal
impossible directly.

The price data have a reproducible invariant threshold.  Recall the root
signature

```text
sigma(t) = (type(t), n(t), kappa_selected(t), kappa_all(t))
```

and let `rho(t,b)` be the five-role census of candidates at root `t` carrying
label `b`.  Mode `--audit-half-atom-projections` forces `alpha`, `phi`, and
`lambda` to be constant on specified root/label classes before solving the
dual.  Across the eleven survivors the success counts are

```text
root class       label class                  successes
type             selected color                 0 / 11
sigma            selected color                 0 / 11
named root       selected color                 0 / 11
type             named label                    0 / 11
sigma,rho        selected color                 6 / 11
sigma            named label                   10 / 11
sigma,rho        named label                   11 / 11.       (12rzr)
```

Every successful final-row separator rationalizes and verifies exactly; its
maximum denominators on the eleven instances are
`5,1,145,6,73,5787,106899,106294,16461,4517,1`.  The decisive information
boundary is therefore not a named root.  It is the identity of the private
label together with that label's local role census at a root.  Conversely,
even giving every root its own price does not help after labels are collapsed
to their selected color.  Thus the sampled uniform target can be sharpened
from arbitrary prices to

```text
alpha_t = Alpha(sigma(t)),
phi_tb  = Phi(sigma(t), b, rho(t,b)),
lambda_tb = Lambda(sigma(t), b, rho(t,b)), Lambda >= 0.       (12rzs)
```

This is substantially smaller than a root-by-label lookup table and is
proof-facing: `sigma` consists of the canonical capacity/collision scalars,
while `rho` is the already-defined five-role fiber census.  Exact label
identity cannot yet be quotiented away, so any uniform construction must use
the selected-fiber partition or a labelwise handshake; a color-aggregate
moment is ruled out by `(12rzr)`.  As with the earlier experiments, this is a
finite-corpus information threshold, not proof that `(12rzs)` works for every
outer design.

The literal label in `(12rzs)` can be compressed further.  Define the
canonical global eligible-incidence mass of a selected label by

```text
L(b) = sum_t sum_(role r) rho_r(t,b).                       (12rzt)
```

Equivalently, `L(b)` is the number of oriented eligible root--candidate
incidences whose candidate block carries `b`.  It is invariant under every
renaming of roots or labels and is computed from the same local census used
in `(12rzs)`.  Forcing equal prices whenever `L(b)=L(b')`, while retaining
the local `rho(t,b)`, still gives an exact rational separator on **all
eleven** survivors.  The maximum denominators are
`1350,1,12,14354,6,906592,1007853,534119,661,1,1`; some label classes really
merge, so this is not merely a canonical renaming of sixteen singleton
fibers.

The local role census is indispensable in this projection class.  If
`rho(t,b)` is dropped, prices indexed by `(sigma(t),L(b))` fail on all eleven;
even replacing `sigma(t)` by the named root `t` still fails on all eleven.
Thus the sharper sampled interface is

```text
alpha_t = Alpha(sigma(t)),
phi_tb  = Phi(sigma(t), L(b), rho(t,b)),
lambda_tb = Lambda(sigma(t), L(b), rho(t,b)), Lambda >= 0.   (12rzu)
```

This supersedes the literal-label reading immediately after `(12rzs)`:
color aggregation is too coarse, but arbitrary label identity is not needed.
The two essential scales are a global scalar `L(b)` and the label's local
five-role geometry `rho(t,b)`.  A uniform proof can therefore target a
fiber-load potential and a local occupancy inequality, rather than a lookup
table on named labels.  The assertion remains a finite-corpus threshold, not
a construction of `Phi` and `Lambda` for every outer design.

The scalar `L(b)` is not a new global oracle.  Let `H` be the symmetric
eligibility graph on ordinary roots, let `n(u)=deg_H(u)`, and let
`F_b={u:b in B_u}` be the five-root fiber of label `b`.  Exchanging the two
finite sums gives the exact identity

```text
L(b)
 = sum_t |N_H(t) intersect F_b|
 = sum_(u in F_b) n(u).                                    (12rzv)
```

If `Q` is the ordinary-root by selected-label block-incidence matrix, this
is simply

```text
L = Q^T H 1.                                                (12rzw)
```

Thus `(12rzu)` depends only on the same candidate degree `n` already present
in `sigma`, aggregated over one canonical five-root fiber, plus the local
role vector `rho(t,b)`.  Mode `--audit-label-load-formula` verifies both
sides and reports the multiset of fiber loads; the implementation also
asserts `(12rzv)` whenever a load-projected dual is built.  A uniform price
construction can now be sought as a fiber-degree/occupancy inequality.  It
does not need arbitrary label names, a new collision tensor, or information
outside `H` and `Q`.

The magnitude of this scalar cannot be replaced by only a coarse load bit.
There are sixteen selected labels, so define the integral centered load

```text
C(b)=16L(b)-sum_(c selected)L(c).                           (12rzx)
```

The total in `(12rzx)` is itself fixed by the root degrees.  A root belongs
to two selected fibers in the triple, hole, and pair-other roles, and to one
selected fiber in the pair-low and pair-high roles.  Hence

```text
sum_b L(b)
 =sum_u g(u)n(u)
 =2sum_u n(u)-sum_(u of pair-low or pair-high type)n(u),    (12rzy)
```

where `g(u)` is that selected-fiber multiplicity.  Thus both the parity of
`L(b)` and the sign of `C(b)` are canonical consequences of the same
degree/fiber data, with no named-label information.

Nevertheless, after retaining the full local census `rho(t,b)`, projected
prices indexed by load parity succeed on only `7/11` corpus survivors;
prices indexed by `sign(C(b))` also succeed on only `7/11`; and their joint
index succeeds on only `8/11`.  Exact `L(b)` succeeds on all eleven as above.
Mode `--audit-half-atom-projections` includes all three coarse projections.
Therefore the observed interface needs more than above/below-average and
parity information: on three survivors even their combination loses a
separation that the exact fiber load restores.  This is again a sampled
no-go for those projection classes, not a universal minimality theorem.

There is strong numerical evidence that the required magnitude enters only
affinely.  Impose the still smaller ansatz

```text
phi_tb = Phi_0(sigma(t),rho(t,b))
         +L(b) Phi_1(sigma(t),rho(t,b)),
lambda_tb = Lambda_0(sigma(t),rho(t,b))
            +L(b) Lambda_1(sigma(t),rho(t,b)) >= 0,          (12rzz)
```

with `alpha_t=Alpha(sigma(t))`.  The nonnegativity in `(12rzz)` is imposed
on every realized root--label capacity price, rather than on the two affine
coefficients separately.  Mode `--audit-affine-load-dual` finds such a
separator on all eleven survivors, including the three on which centered
sign plus parity fails.  Thus the sampled next target is not an arbitrary
function of the exact load: it is a local census price with one constant
and one linear fiber-degree coefficient.

This restriction is nonvacuous on the hard survivors.  For example, the
branch-3 seed-21 survivor has `54` distinct `(sigma,rho)` classes that each
occur at three or more different values of `L`; arbitrary values on those
occurrences cannot in general be interpolated by one affine function.  The
audit reports this count as `nonlinear_test_classes` to distinguish genuine
linearity tests from classes supported at only one or two loads.

This affine result is currently numerical evidence, not yet an exact
certificate theorem.  The existing bounded-denominator rationalizer
verifies one of the eleven solver vertices exactly (independently reproduced
with maximum denominator `2`) but does not recover exact points for the other ten, whose degenerate
floating vertices produce near-ten-million denominators and fail the final
route-slack check.  Rational polyhedral feasibility suggests exact affine
prices should exist, but an exact basis reconstruction or a direct symbolic
construction is required before using `(12rzz)` as a proved corpus fact.

The coefficients need not be completely refit instance by instance on a
first cross-instance test.  Mode `--audit-common-affine-load-dual` forms one
joint LP in which the functions `Alpha,Phi_0,Phi_1,Lambda_0,Lambda_1` are
shared on every identical `(sigma,rho)` key and every survivor has its own
negative-price constraint.  On all four restricted-Hall survivors of a
13-seed run, one shared price succeeds.  The union has `165`
root-signature and `1716` local classes; `13` root classes and `84` local
classes genuinely occur in at least two instances, so the joint solve has
nontrivial cross-instance equalities.  The instance-overlap graph is
connected (reported component sizes `(4,)`), so this witness is not a
product of independent subcorpus prices.

This is only an initial common-potential witness.  The full eleven-survivor
joint LP exceeded the exploratory run window before returning a status, so
no all-corpus common-price claim is made.  The audit imposes a five-minute
HiGHS limit and reports shared-class counts, allowing progressively larger
subcorpora to locate the first incompatible pair or establish a universal
sampled affine potential.  It also decomposes disconnected instance-overlap
graphs automatically and reports their component sizes; this avoids solving
unrelated price systems together while exposing when a common witness is
genuinely coupled.

The sampled rank has a combinatorial certificate much simpler than a
determinant.  In all 476 columns, at least one nonzero tagged **bundle**
feature occurs in **no other unordered transition column** of that instance.
The rank audit now reports any column lacking such a private row and finds
none.  Hence the most concrete prospective lemma is

```text
PRIVATE BUNDLE FEATURE:
every unordered same-role own transition {t,u} has a tagged fiber-census
feature occurring in no other Delta(v,w).                       (12rh)
```

Peeling the coefficient of that private row proves (12rg) immediately.
This turns the rank conjecture into a uniqueness statement about a consumed
fiber state, without relying on alpha uniqueness.  In the sample, 336
columns also have a private alpha endpoint while 140 do not, but all 476
have a private bundle row.  The seed-8 loop
illustrates the latter case: its pair-high/pair-other secondary census swap
is exactly the private information lost by the flat projection.

The prospective proof has one sharply isolated alternative.  In 475 of the
476 sampled columns, a private bundle row has `iota=0`, so it is a nonshared
consumed secondary fiber.  The sole exception is a branch-4 regular-triple
pair with root signatures `(triple,10,9,13)` and `(triple,12,10,16)`; its
private row is instead the incoming shared-own state
`((triple,12,10,16), iota=1, (1,0,0,0,1))`.  The rank audit reports every
column lacking a private external row.  Thus a proof of (12rh) can target
secondary-fiber injectivity generically, with an explicit shared-own census
alternative rather than assuming the external version universally.

A simple parity sign on the horizontal part of (12qt) is also unavailable.
The sampled own-touching transition graphs contain many regular-to-regular
edges, so root role is not a bipartition.  More strongly, quotient the
horizontal graph by the full signature `(role,n,c_pair,c_all)`.  In every one
of the 24 four-seed pair/design instances this quotient graph is
nonbipartite (although none has a loop).  Hence no sign depending only on the
root signature can force even horizontal length in (12qt).  Any parity
refinement must resolve the individual own fiber or its external-essential
second label—exactly the information retained by `iota` and (12qs), rather
than another scalar root statistic.

External essentiality itself is not a plug-in global price.  Set
`mu_tb=1` when deleting external label `b` lowers `nu(G_t^ext)`, and zero
otherwise (root-own labels have value zero).  The exact integer matching
oracle gives positive global support sums on every locally feasible sampled
instance; on the two hardest pairs they are 66 and 58.  The complementary
`0/1` price is also positive (62 and 53).  Thus (12qs) identifies the local
deletion mechanism but does not by itself orient the Farkas curl.
Full-signature alpha potentials and genuinely joint role weights are still
required to turn essential-label blocking into a global contradiction.

The role flags in (12o)--(12p) are constrained occupancy tables, not
independent parameters.  Let `e_tj` be the number of eligible candidates of
role `j` at row `t`, and write `r_tb,j` for the corresponding coordinate of
`r_tb`.
Regular triples, holes, and pairs missing the unselected color carry two
selected labels, while a pair missing one selected color carries one.
Therefore

```text
sum_b r_tb,j = 2 e_tj  for j = regular, hole, pair-missing-unselected,
sum_b r_tb,j =   e_tj  for j = pair-missing-selected,
n(t) = sum_j e_tj,
c(t) = sum_b binom(sum_j r_tb,j,2).                         (12r)
```

Also `sum_j r_tb,j=ell_b(t)<=5`, because the whole fiber `F_b` has five
rows.  For the oriented five-role monotone cone, split the
`pair-missing-selected` coordinate into its two selected-color orientations;
each split coordinate separately has `sum_b r_tb,j=e_tj`.  Hence the
monotone-price conjecture is a finite sixteen-column, five-role occupancy
inequality with fixed linear margins and fixed convex energy.  This is a
more economical proof interface than arbitrary `Q,K` flags: a majorization
or compression argument on the columns of `r_t` could construct the
monotone prices, while (12fa) handles the low-cover boundary.

The all-color refinement (12qb) has equally rigid margins.  If `e_3(t)` is
the number of eligible regular-triple or hole candidates and `e_2(t)` the
number of eligible pair candidates, then its total 24-label load is

```text
M_all(t) = 3 e_3(t) + 2 e_2(t) = sum_(all b) ell_b(t).      (12qc)
```

Write `M_all=24a+r`, `0<=r<24`, and also `M_all=5h+s`,
`0<=s<5`.  Since every full fiber contains five rows, convexity gives the
sharp rootwise interval

```text
(24-r) binom(a,2) + r binom(a+1,2)
  <= c_all(t) <= 10h + binom(s,2).                          (12qd)
```

Thus adding `c_all` does not introduce arbitrary design data: it selects one
integer layer in a short interval determined by the same role margins.  A
uniform proof can split on equality/near-equality in (12qd), where the 24
fiber loads are respectively balanced or maximally concentrated, and use
the selected-pair refinement (12r) inside that layer.

There is an exact primal alternative to constructing those monotone prices.
Let `I` be the finite set of compressed root--fiber flags in (12p), ordered
at fixed root signature by coordinatewise inclusion of the role census.
Let `K` be the cone of nonnegative isotone tables on `I`.  For each choice of
one cardinality-`d_t` matching at every row, sum its (12n) feature vectors;
let `C` be the convex hull of all such sums.  The free `alpha` coordinates
and the cone `K` are precisely the allowed monotone price directions.
Finite-dimensional strong separation therefore gives

```text
no strict monotone flag-price separator
iff some v in C satisfies
    v_alpha(sigma)=0 for every root signature sigma, and
    sum_{i in U} v_mu(i) >= 0 for every upper set U of I.    (12ra)
```

Indeed, the first condition is forced by pairing with every free `alpha`.
Every nonnegative isotone function on a finite poset is a nonnegative linear
combination of indicators of upper sets (take its successive superlevel
sets), so the second line is exactly membership in the dual cone `K*`.
Conversely, if the compact polytope `C` misses this closed dual cone, strict
separation supplies an allowed monotone table whose maximum on `C` is
negative, which is the desired matching-support inequality.

The `alpha` equations in (12ra) say concretely that the fractional selected
candidate endpoints reproduce the fixed demand census of every root
signature.  The upper-set equations say that source fiber usage dominates
the corresponding incoming usage in role-census majorization order.  Thus a
counterexample to the price branch is not an opaque failed LP: it is a
fractional system of locally feasible matchings with exact signature balance
and finitely many flag-majorization inequalities.  Combining three such
systems for the three color pairs with the coupled occupancies (12l), (12r)
is a concrete route to the design-level Hall-or-price dichotomy (12q).

The majorization witness has zero, not merely nonnegative, total mass.  Put
`g(t)=|S_t intersect C|`.  This is determined by the root role: it is two
for a regular triple, hole, or pair missing the unselected color, and one for
a pair missing a selected color.  Summing all `mu` coordinates of a matching
feature vector gives

```text
sum_{chosen t->u} (g(u)-g(t)).                              (12rb)
```

The `alpha` balance equations in (12ra), weighted by the signature function
`g`, make (12rb) zero (each row `t` occurs as a source exactly `d_t` times).
Flags with different root signatures are incomparable in `I`; hence the
whole component of one signature and its complement are both upper sets.
The upper-set inequalities and zero global mass force zero mass on every
root-signature component separately.  Within each component, (12ra) is
therefore exactly multivariate first-order dominance of the source fiber
census over the incoming fiber census, with equal total mass.  A proof of
(12q) may consequently seek a strictly convex occupancy statistic from
(12r) that cannot be nonincreasing around all three color-pair dominance
systems unless one of the Hall cover inequalities (12fa) is already tight.

Equivalently, the finite-poset transport theorem (the max-flow form of
first-order stochastic dominance) replaces all upper-set inequalities by a
single monotone coupling.  For each root signature there is a nonnegative
transport matrix `pi` from its incoming flag measure to its source flag
measure such that

```text
pi(r_in,r_out)>0  implies  r_in <= r_out coordinatewise,   (12rc)
```

and the two marginals are exactly the incoming and source masses produced by
the fractional row matchings.  Necessity follows by testing upper sets;
sufficiency is the integral max-flow/min-cut theorem after clearing the
rational matching weights.  Thus a hypothetical failure of both branches
has a purely combinatorial normal form: locally feasible fractional
matchings, exact signature balance, and monotone transports of oriented
five-role fiber columns.  This is the natural place to apply the fixed
column sums and strictly convex collision energy in the oriented refinement
of (12r), rather than reason about fitted price coefficients.

There are sharp scalar consequences.  Let `p(t)` be the number of eligible
pair candidates missing one selected color and put `L=2n(t)-p(t)`, the total
selected-label mass.  Write

```text
L = 16a+r,  0<=r<16,       and       L = 5q+s,  0<=s<5.
```

Convexity, integrality, and the column cap five give

```text
(16-r) binom(a,2) + r binom(a+1,2)
  <= c(t) <= 10q + binom(s,2).                              (12s)
```

The lower equality has sixteen loads differing by at most one; the upper
equality fills `q` fibers to five and one fiber to `s`.  These bounds are
valid before using the individual role margins, so any proof by compression
can work inside the substantially smaller `(role,n,p,c)` range cut out by
(12s).

These scalar bounds do not distinguish the two branches.  In the four-seed
run, the nine Hall-failed rows have lower-bound gap `c-lower(12s)` between
9 and 15, while locally feasible rows range from 6 to 26; the upper-bound
gaps overlap as well.  Thus `(n,p,c)` is necessary root bookkeeping, not a
closing statistic.  The distribution of roles among the individual fiber
columns in `r_tb` is genuinely needed by the sampled certificates.

The smallest invariant ansatz for `W` can also be eliminated exactly on the
sampled designs.  Normalize the selected colors as low/high and give a row
one of five types: regular triple, exceptional hole, pair missing low, pair
missing high, or pair missing the third color.  Suppose `W_tu` depends only
on the ordered pair of these types and on `|S_t intersect S_u|` (zero or
one).  Antisymmetry leaves twenty coefficients.  For fixed coefficients,
the row optimum is still the exact binary matching problem in (12f).  A
cutting-plane LP, with those matching problems as separation oracles,
minimizes the worst total row optimum over the supplied outer witnesses.
Bounding each coefficient by one loses no strict separator, since a strict
separator can be rescaled.

On seed zero in both branches, every one of the six color-pair instances is
locally feasible, but fitting it *individually* gives optimum exactly zero.
Thus this feature class cannot produce (12h), even with coefficients chosen
separately for each design.  Across four seeds per branch, seven of the 24
instances instead have an ordinary local Hall obstruction; a simultaneous
fit to the other seventeen again has optimum zero.  Hence the required
potential must see more of the detailed ordered eligibility graph than row
types and support overlap.  The reproducible exact-oracle experiment is
`q9_structured_skew_potential.py`; `--individual` distinguishes failure of
the feature class on one witness from failure of a single potential shared
across witnesses.

There is nevertheless a canonical, if still overly detailed, refinement
which succeeds.  For each row record its five-way type, its number of
eligible candidate neighbors, and the sorted multiset of the nonzero loads
of the sixteen selected labels among those candidates.  Let `W_tu` depend
on the ordered pair of these **local load profiles** and support overlap.
The candidate-count refinement alone still has optimum zero on all six
seed-zero instances.  The load-profile refinement, fitted separately,
strictly separates all six, with normalized optima

```text
branch 3: -1.20490201, -3.61427179, -1.03339599,
branch 4: -2.19211409, -8.66096979, -1.87816915.
```

This locates the information threshold: the potential need not name rows or
use the full arbitrary Farkas ray, but it must at least detect the imbalance
pattern of the selected U1 fibers in each local eligibility graph.  The
profile is almost injective in the first instance (44 profiles on 47 rows),
so by itself this is not yet a uniform counting lemma.  However, the profile
can be compressed to two elementary row statistics.  Write `ell_b(t)` for
the number of eligible candidates at row `t` carrying selected label `b` and
set

```text
c(t) = sum_b binom(ell_b(t),2).                              (12i)
```

This is exactly the number of unordered pairs of eligible candidates which
conflict at a selected U1 label.  Equivalently, if `E_t` is the trace-eligible
candidate set, linearity of `Q` makes `c(t)` the number of pairs in `E_t`
whose supports share a point of either selected color: it is the edge count
of the selected-fiber conflict graph induced on `E_t`.  Thus both statistics
are read directly from `Q,K`, with no residual adjacency variables.

Refining the five-way row type by only the
candidate count and `c(t)`, and again indexing skew coefficients by ordered
refined types and support overlap, strictly separates all six seed-zero
instances.  Their normalized optima are

```text
branch 3: -0.493338506, -1.55163664, -0.722755960,
branch 4: -2.19211409,  -5.99921391, -0.481591077.
```

Both scalars matter: candidate count alone has optimum zero on all six;
total selected-label load in place of `c(t)` has optimum zero on the first;
and `c(t)` without candidate count also has optimum zero there.  Thus the
first reproducible positive compression is the pair `(number of eligible
candidates, number of candidate conflicts)`.  This suggests a concrete
uniform counting target: express the skew matching potential through local
capacity and collision excess rather than through sixteen named fibers.
The script modes `--features candidate-count`, `--features total-load`,
`--features collisions`, and `--features load-profile` reproduce this
boundary; every refined mode retains candidate count.

The dependence is not merely linear.  Give a row the seven coordinates
consisting of its five type indicators, candidate count, and `c(t)`, and let
`W_tu` be an arbitrary skew-bilinear form in these coordinates, with a
separate form for support overlap zero and one.  This 42-parameter family has
optimum zero on every seed-zero instance.  Hence the successful categorical
potential uses thresholds or other nonlinear dependence on local capacity
and collisions.  The mode `--features bilinear-collisions` records this
negative boundary.

Two further compressions fail, which shows what the nonlinear dependence
must retain.  Replacing `c(t)` by `(max_b ell_b(t), number of b with
ell_b(t)>=2)` separates five seed-zero instances but has optimum zero on
branch 3, colors `(0,1)`.  Indexing coefficients only by the ordered row
types and the differences `n(t)-n(u), c(t)-c(u)` (plus support overlap)
separates only three of six.  Absolute capacity/collision levels, not just
their order or difference, therefore matter in the sampled potential.  The
corresponding modes are `--features load-shape` and `--features
collision-differences`.

A scalar potential is also insufficient.  Even allowing one arbitrary
number `phi(t)` for every row and putting

```text
W_tu = phi(t) - phi(u)
```

has optimum zero on all six seed-zero instances (`--features
free-gradient`).  Conceptually, gradients test only whether the local
outgoing choices can be balanced to the required column degrees: their
value is `sum_t d_t phi(t) - sum_u colSum_u phi(u)`.  The zero result says
that this degree-balancing relaxation survives.  The obstruction appears
only when the incoming fiber caps are imposed, so the terminal `W` must have
genuine pairwise curl; it cannot be a difference of row potentials, however
those potentials are chosen.  Even the broader signature-based class with a
separate `phi(type,n,c)` for support overlap zero and one has optimum zero
(`--features gradient-collisions`).

Nor is `c(t)` merely a surrogate for local matching capacity.  The conflict
graph on `E_t` has `n(t)` vertices and `c(t)` edges, so the generic greedy
bound gives

```text
nu(t) >= ceil(n(t)^2 / (n(t)+2c(t))).                       (12j)
```

On the seed-zero instances this lower bound is usually two to five below the
true matching number and is too weak even to certify the required local
degree on most rows.  More decisively, replacing `c(t)` by the *exact* local
matching number `nu(t)` in the categorical signature has optimum zero on
five of the six instances (it separates only branch 4, colors `(0,2)`).
Thus the simultaneous obstruction sees the distribution of candidate
conflicts, not just how many candidates a single row can ultimately pack.
Mode `--features matching-capacity` reproduces this test.

There is a compact matrix interpretation of the two successful statistics.
Let `H` be the simple graph on ordinary rows whose distinct vertices are
trace-eligible.  Since `K` is symmetric, the two apparent trace directions
coincide, and

```text
H_tu=1  iff  t!=u and (Q K Q^T)_tu=0.
```

Let `G_C` be the simple graph joining two ordinary rows when their supports
share a point in the selected two colors.  Linearity makes its off-diagonal
entries zero or one.  Then

```text
n = H 1,
2c(t) = (H G_C H)_tt,
2 sum_t c(t) = trace(G_C H^2).                              (12k)
```

Indeed, `(H G_C H)_tt` counts both orientations of every `G_C`-edge inside
the `H`-neighborhood of `t`.  Thus the empirical certificate depends only on
the degree and rooted mixed-triangle count of a canonical pair of graphs
constructed from `Q,K`.  Equation (12k), rather than sixteen individual
fiber loads, is the natural interface for a uniform trace or flag-counting
inequality.

The three choices of two colors are coupled exactly.  The eligibility graph
`H` and hence `n(t)` do not depend on the selected colors.  If `G_g` records
support intersections through color `g` alone, linearity makes the three
edge sets disjoint and

```text
G_ij = G_i + G_j,
c_ij(t) = c_i(t) + c_j(t),
c_01(t)+c_02(t)+c_12(t) = 2(c_0(t)+c_1(t)+c_2(t)).           (12l)
```

The same identities hold after summing over rows or taking the traces in
(12k).  Thus a uniform proof may choose a favorable color pair by averaging
three rooted mixed-triangle counts; it need not construct three unrelated
certificates.  The current categorical potential is nonlinear, so (12l)
does not itself perform that averaging, but it is the exact coupling a
threshold inequality should exploit.

This also identifies exactly what the earlier reduced-`L`
``diagonal-even'' condition measured.  In that formulation

```text
Q is 47 by 24,   Q^T A = H-L,   X=(H-L)Q=Q^T A Q.
```

For every `b in U1`, symmetry and the zero diagonal of `A` give

```text
X_bb = sum_{t,t' in F_b} A_tt' = 2 |E(A[F_b])|.             (12a)
```

Thus the imposed range `X_bb in {0,2,4}` is automatic for a residual
adjacency matrix; equivalently, in the sampled reduced model where
`(HQ)_bb=5`, it only requires `(LQ)_bb` to be odd.  It does not determine
whether `|E(A[F_b])|` is odd.  The parity in (12) is instead
`T_R = trace(X)/2`, so it requires `trace(X) mod 4`, not merely evenness of
each diagonal entry.  Over `F2`, saying that `X` is alternating is just the
image of the symmetric-loopless law for `A` and supplies no additional B.3
constraint.  The previously observed fast infeasibility for one fixed outer
seed therefore came from coupling these automatic diagonal equations with
the sparse binary factor `L`, its exact row cardinalities, and integer
symmetry; diagonal evenness alone was not a hidden parity invariant.

There is a useful linear-algebra test for whether residual degree parity can
ever determine (12).  Let `H` be the graph of allowed residual B0 edges and
let `W` be the block-intersection graph

```text
W_uv = 1  iff  |S_u intersect S_v|=1.
```

Then `T_R=|E(A) intersect E(W)|`.  Over `F2`, two subgraphs of `H` with the
same degree-parity vector differ by an Eulerian subgraph, hence by an element
of the cycle space of `H`.  It follows that

```text
T_R mod 2 is determined by the degree-parity vector
iff every cycle of H meets W in an even number of edges
iff E(W) intersect E(H) is a cut of H.                        (13)
```

This criterion concerns degree parity, not realizability with the prescribed
exact degrees.  If (13) fails, an H-cycle with odd W-intersection is the exact
parity-switching direction at the linear layer.  If it holds, a cut potential
expresses `T_R mod 2` directly from the residual degree parities.  Thus (13)
is a small diagnostic for whether the remaining obstruction is already
linear or necessarily uses exact-degree/integrality information.

The diagnostic was run directly on four unrestricted outer seeds in each
branch.  Here `H` contains precisely the symmetric residual cells satisfying
the two trace-orthogonality directions.  In every seed `H` was connected and
`W intersect H` failed the cut-potential equations:

```text
branch 3: |E(H)| = 377, 378, 385, 389;  W is not a cut in all four,
branch 4: |E(H)| = 390, 386, 388, 379;  W is not a cut in all four.
```

For seed zero in either branch, the failure already has a three-edge witness:
an allowed residual triangle with mask weights `(0,1,0)`, hence odd
W-intersection.  Thus the parity of `T_R` is not determined by residual
degree parity even after imposing the full outer orthogonality support.
This is again a sampled failure certificate, not a graph realization.  An
odd cycle switches degree parity data but cannot in general be toggled while
preserving prescribed exact degrees.  Thus this probe only locates the
failure beyond the degree-parity linear layer.

A direct exact-degree check narrows the boundary further.  On seed zero in
each branch, impose only `A subset H` and the proved residual degrees (degree
five on regular triple rows; degree six on exceptional holes and all 21 pair
rows).  The resulting pure `f`-factor problem is satisfiable with either
parity of `|E(A) intersect E(W)|`:

```text
branch 3, seed 0: T_R parity 0 SAT; parity 1 SAT,
branch 4, seed 0: T_R parity 0 SAT; parity 1 SAT.
```

Therefore even the exact residual degree sequence plus the two-sided
orthogonality support does not determine `T_R`.  Any terminal must also use
the row-type/marked-group reciprocity, residual C4 common-neighbor structure,
or another constraint absent from the pure `f`-factor model.

Adding residual C4-freeness still does not determine the parity.  The mode
`--audit-residual-c4-parity` builds the symmetric graph directly on the
two-sided trace-orthogonal support, imposes degree five on regular triple
rows and degree six on exceptional-hole and pair rows, and requires every
two vertices to have at most one common residual neighbor.  On outer seed
zero it finds

```text
branch 3: T_R parity 0 SAT; parity 1 SAT,
branch 4: T_R parity 0 SAT; parity 1 SAT.
```

These are explicit failure certificates for the strengthened abstraction:
exact degrees, two-sided trace support, and the internal residual C4 law
together still admit both collision parities.  Thus the next terminal cannot
come from residual C4-freeness alone.  It must use the mixed B0--U1
common-neighbor budget (in particular the block-intersection Gram law), the
marked-row defect reciprocity, or a stronger coupling that implies one of
them.  No claim beyond the completed seed-zero witnesses is made.

The missing mixed Gram law reverses the result completely.  The mode
`--audit-residual-gram-parity` additionally requires two rows whose U1
blocks intersect to have no common residual neighbor.  On seed zero, both
parities are UNSAT in both branches.  More sharply,
`--audit-residual-gram-only` deletes the ordinary residual C4 constraint for
block-disjoint row pairs and retains only

```text
S_u intersect S_v != empty
 -> N_A(u) intersect N_A(v) = empty.                         (13a)
```

Even this Gram-only model is UNSAT for both parities in branch 3 and branch
4.  Since the two parity cases exhaust all residual graphs, the parity
constraint is inessential: on these fixed outer witnesses there is no
symmetric graph with the exact 5/6 degrees, two-sided trace-orthogonal edge
support, and (13a).  Marked-row defect variables, their row and column sums,
and ordinary residual C4 bounds are absent.

The first interpretation of this result as necessarily a simultaneous
47-row packing obstruction was too strong.  The follow-up mode
`--audit-residual-gram-local` checks each row separately.  In one completed
seed-zero invocation it found the entire UNSAT already at local independent-
set capacity:

```text
branch 3, seed 0: rows 24 and 25 demand 6 but have capacity 5,
branch 4, seed 0: row 4 demands 5 but has capacity 4.          (13b)
```

Here capacity means the largest `W`-independent subset of the row's
two-sided trace-eligible `H`-neighbors.  Thus symmetry and simultaneous
degree realization are not needed for those particular contradictions.

However, widening the local audit to eight generated witnesses per branch
immediately killed the uniform one-row conjecture.  Fifteen of the sixteen
witnesses had at least one deficient row (typically capacity one below
demand, once capacity two below), but branch 3 seed 1 had none.  Rechecking
the first two witnesses in the full Gram-only model nevertheless gave UNSAT
for both parities in both branches, including that locally feasible branch-3
survivor.  Consequently the sampled mechanism has a genuine dichotomy:

```text
some row has alpha_W(H-neighborhood) below its residual demand;
or every row is locally feasible but the symmetric degree realization
   with W-independent neighborhoods fails simultaneously.                (13c)
```

The proof-facing target must retain both horns.  The first is a local block-
packing statement aligned with the exceptional-hole complement-partition
obstruction; the second is a global compatibility theorem for the locally
feasible rows.  Generated solver witness numbering is not a canonical graph
identifier, so the seed labels and row indices above document reproducing
runs rather than invariant isomorphism classes.  All observations remain
sampled outer-design evidence, not proofs for every admissible design.

A grouped UNSAT core and a second widened sweep sharpen the second horn back
to a two-row local statement.  For a locally feasible row `u`, let

```text
F(u) := intersection of all demand(u)-element W-independent subsets
        of the trace-eligible neighborhood N_H(u).              (13d)
```

Thus `F(u)` is the set of residual neighbors forced by every local packing
at `u`.  In the first locally feasible branch-3 survivor, the grouped core
used only the degree equations of rows 3 and 16.  Their blocks intersected,
and both forced row 28.  Hence any simultaneous realization would contain
the forbidden common residual neighbor

```text
28 in F(3) intersect F(16),  while S_3 intersect S_16 != empty. (13e)
```

The mode now reports all such forced collisions.  In one completed sweep of
sixteen generated witnesses per branch, thirty witnesses had a deficient
row.  The two locally feasible witnesses (one in each branch) both had
forced collisions; indeed the branch-3 survivor had three and the branch-4
survivor had eight.  Therefore all thirty-two sampled witnesses satisfy the
purely local alternative

```text
some u has alpha_W(N_H(u)) < demand(u); or
some u,v,w have S_u intersect S_v != empty
  and w in F(u) intersect F(v).                                (13f)
```

Either horn immediately contradicts a Gram-compatible residual graph: the
first cannot realize the row degree, while the second forces two intersecting
blocks to share residual neighbor `w`.  Statement (13f), uniform over every
admissible outer design, is now the precise proof candidate.  It involves at
most two local packing polytopes and avoids the full symmetric factor model.
As before, the sweep is evidence for that candidate rather than a proof.

The summary mode `--audit-residual-gram-summary` then stress-tested (13f) on
sixty-four generated witnesses per branch.  It found no uncovered design:

```text
branch 3: 57 with a deficient row, 7 locally feasible with a forced
          collision (36 of the deficient cases also had a collision);
branch 4: all 64 with a deficient row (48 also had a collision);
uncovered: 0 of 128.                                      (13f')
```

This larger run preserves the parity asymmetry suggested by the smaller
sample: branch 4 repeatedly dies in the one-row horn, whereas branch 3
occasionally needs the two-row kernel collision.  The zero uncovered count
is strong falsification resistance for candidate (13f), but does not replace
a proof over the unrestricted outer design.

A repeated sixty-four-per-branch run retained the coarse row roles.  No
deficient row was ever a marked-pair row.  The deficient-role patterns were

```text
branch 3: hole only 29; hole+regular triple 20; regular triple only 8;
branch 4: hole only 32; hole+regular triple 25; regular triple only 7.
                                                                    (13f'')
```

Thus branch 4 does not reduce to the exceptional-hole conjecture: seven
witnesses had only regular-triple deficits.  On the seven locally feasible
branch-3 witnesses, all nineteen forced collisions joined a regular triple
to another triple center.  Their forced neighbor was a marked-pair row in
eighteen cases and a regular triple in one; the endpoint/neighbor role counts
were

```text
(regular triple, regular triple; pair): 8,
(regular triple, hole; pair):          10,
(regular triple, hole; regular triple): 1.              (13f''')
```

This reduces the candidate's obstruction centers from all 47 rows to the 26
triple centers.  Marked-pair rows remain essential as eligible or forced
neighbors, but sampled evidence never needs their own degree equation to
supply the deficit or either endpoint of a kernel collision.

The representative branch-3 collision has a particularly small exact-cover
profile.  The two core rows are regular rainbow triples

```text
S_3={3,11,19},       S_16={0,11,20},
```

sharing point 11.  Row 3 has exactly six feasible five-block packings and row
16 has exactly three.  Every one of the nine packings contains the same
marked-pair row 28 with

```text
S_28={11,23}.                                             (13g)
```

For row 3 all packings have block-size profile `(3,2,2,2,2)` and cover
eleven U1 labels.  Row 16 has profiles `(3,2,2,2,2)` or `(3,3,2,2,2)` and
covers eleven or twelve.  Thus this second horn is not an opaque SAT-core
artifact: two rainbow triples through one U1 point both force one marked pair
through that same point.  A useful route to (13f) is to classify when the
local exact-cover family of a triple or hole has a nonempty kernel `F(u)`,
then show that absence of a capacity deficit makes two kernels collide along
an intersecting row pair.

There is a useful but nonterminal linear dual.  Give the 24 U1 labels
nonnegative weights `lambda_b` and require every eligible candidate block to
have weight at least one.  Pairwise-disjoint chosen blocks then consume
disjoint label weights, so every local packing has size at most
`sum_b lambda_b`.  A total below `d(u)` certifies a deficit.  After deleting
one candidate `w`, the same inequality certifies `w in F(u)`.  The audit modes
`--audit-residual-gram-hitting` and
`--audit-residual-gram-dual-summary` compute integral and fractional versions
of this cover dual.

The fractional dual certifies nearly all sampled horns, but not all.  In a
sixty-four-per-branch run its coverage was

```text
branch 3: 63 of 64 witnesses;
branch 4: 64 of 64 witnesses.                                (13h)
```

The one uncovered branch-3 witness was locally feasible and had exactly one
forced collision `(u,v,w)=(11,16,27)`.  After deleting `w`, the optimal
fractional cover weights were `4.5` at row 11 and exactly `5.0` at row 16,
whose demand is five.  Thus the dual proves `w in F(11)` but cannot prove
`w in F(16)`; the latter forcedness is genuinely integral.  This counterexample
was captured inside the same sequential generator run because regenerated
seed handles are noncanonical.

The witness and exact certificates are now stored rather than left as
floating console output.  The file `q9_gram_fractional_gap_witness.json`
contains all 47 blocks and all 36 edges of `K`.  The mode
`--audit-residual-gram-gap-certificate` verifies by exact subset dynamic
programming that both base matching ranks are five and both ranks after
deleting row 27 are four.  It first fixes the stored blocks and `K` inside
the unrestricted outer-design solver and requires `SAT`, so admissibility is
also rechecked rather than trusted from provenance.  It rationalizes the LP
supports and then checks
every primal capacity inequality, every dual block-cover inequality, and
equality of the two rational objectives using `Fraction`.  The certified
values are

```text
row 11 after deletion:  nu=4, fractional optimum=9/2;
row 16 after deletion:  nu=4, fractional optimum=5.             (13h')
```

The integral gap at row 16 has a small visible support.  Two unit-weight
pair blocks are `{0,21}` and `{7,16}`.  The six half-weight blocks split as

```text
{4,12,20}, {2,20}, {2,12};
{4,13,23}, {3,23}, {3,13}.                              (13h'')
```

Each line is a three-edge Berge triangle: its blocks intersect pairwise at
three different labels.  The two triple blocks also meet at label 4.  Thus
the half weights contribute three fractionally, whereas integrally each
triangle contributes at most one; with the two unit pairs this is the
observed `5` versus `4` gap.  The exact dual of value five puts unit weight
on labels `{2,3,4,7,21}`.  This identifies the nonlinear residue as an odd-
cycle matching obstruction, not numerical solver noise.

Adding the corresponding valid odd-cycle inequalities closes this stored
integral gap exactly.  For every three pairwise-intersecting candidate
blocks `a,b,c`, a matching satisfies

```text
x_a+x_b+x_c<=1.                                           (13h''')
```

The exact certificate mode now solves the point-capacity relaxation with all
such Berge-triangle cuts and rationally verifies primal and dual objectives
equal to four on both deletion rows.  At row 16 the upper certificate uses
unit point prices at labels 7 and 21 together with unit prices on the two
triangles `(4,34,41)` and `(20,35,42)` displayed in (13h'').  At row 11 it
uses point prices at 8 and 14 and triangle prices on `(4,12,36)` and
`(19,24,33)`.  Thus

```text
triangle-augmented fractional optimum = integral rank = 4
at both sides of the stored forced collision.                    (13h'''')
```

This repairs the unique miss of the plain fractional label cover for the
stored witness.  It does not yet prove that point caps plus Berge-triangle
cuts suffice for every admissible outer design; that uniform assertion
requires a seed-free argument or a wider adversarial test.

The mode `--audit-residual-gram-triangle-summary` applies the strengthened
relaxation to generated witnesses.  An initial eight-per-branch run had no
uncovered design:

```text
branch 3: 7 triangle-certified deficits, 5 certified collisions;
branch 4: 8 triangle-certified deficits, 5 certified collisions;
uncovered: 0 of 16.                                      (13h''''')
```

The horns overlap in these counts.  This small run is only a regression test
that the odd-cycle refinement retains the earlier easy certificates while
closing the stored hard one; it is not evidence strong enough to promote the
triangle-augmented statement to a theorem.

Consequently a replacement using only fractional U1-label covers is false.
Those covers remain a compact proof tool for one-row deficits and most kernel
sides, but the exceptional branch-3 collision needs an additional integral
or odd-cycle matching ingredient such as (13h''').

The generic consumer of (13f) is now formalized in
`Erdos85LocalGramPacking.lean`.  The theorem
`false_of_localGramPacking_deficit_or_forced_collision` takes an arbitrary
finite symmetric residual relation with exact row demands, eligible support,
and the Gram common-neighbor law.  Its actual neighborhood at every row is a
local `W`-independent packing; hence either a missing local packing or an
intersecting pair forcing one common neighbor yields `False`.  This theorem
is parameter-free, compiles with no `sorry`, and uses only the standard
`propext` and `Quot.sound` axioms.  The sole B.3 gap at this interface is now
the outer-design statement (13f) itself.

There is an exact proof-facing simplification of the eligibility relation in
that remaining statement.  Write `B_t` for the two- or three-point U1 block
of row `t`, let `K` be the undirected cubic U1 graph, and put

```text
Gamma_K(B_t):=union_{b in B_t} N_K(b).
```

The implementation defines `core(t)=Gamma_K(B_t)` and excludes a candidate
`u` when either

```text
B_u intersects Gamma_K(B_t), or
B_t intersects Gamma_K(B_u).                              (13h)
```

These two conditions are equivalent, not independent.  Indeed either one
says that some `a in B_t` and `b in B_u` satisfy `a--b` in `K`; reversing
the edge proves the other because `K` is undirected.  Therefore the exact
eligible neighborhood is simply

```text
N_H(t)={u!=t : B_u intersect Gamma_K(B_t)=empty}.          (13i)
```

The Gram conflict relation is block intersection.  Consequently a local
packing at `t` is exactly a `d(t)`-edge matching in the linear 2/3-uniform
block hypergraph obtained by deleting row `t` and every block meeting the
single forbidden point set `Gamma_K(B_t)`.  Its forced set `F(t)` is the
set of hyperedges contained in every such `d(t)`-matching.  Thus (13f) is
equivalently the seed-free matching-kernel alternative

```text
some row t has matching number below d(t); or
some intersecting blocks B_u,B_v have a block B_w
contained in every d(u)-matching at u and every d(v)-matching at v.       (13j)
```

The sampled role reduction (13f''') suggests the stronger version in which
`t,u,v` may all be restricted to triple centers, but that restriction remains
conjectural.  Equations (13h)--(13j) without that restriction are identities
valid for every admissible outer design.  They remove one redundant trace-
orthogonality predicate from a seed-free encoding and expose the remaining
target as a statement about essential edges in matchings after one canonical
neighborhood deletion.

The essential-edge condition has an equivalent matching-rank test.  Let
`mathcal H_t` denote the eligible block hypergraph in (13i), and assume its
matching number meets the row demand.  Then

```text
w in F(t)
iff every d(t)-matching of mathcal H_t contains B_w
iff nu(mathcal H_t-B_w)<d(t).                              (13k)
```

The last equivalence is immediate: a demanded matching omitting `B_w` is
exactly a demanded matching in the deletion.  Consequently the complete
unrestricted candidate (13f) can be written without intersections over
families of packings:

```text
some t has nu(mathcal H_t)<d(t); or
some u,v,w satisfy B_u intersect B_v!=empty,
  nu(mathcal H_u)>=d(u),       nu(mathcal H_v)>=d(v),
  nu(mathcal H_u-B_w)<d(u),    nu(mathcal H_v-B_w)<d(v).        (13l)
```

Thus the second horn asks for one block whose deletion creates a simultaneous
unit-or-larger matching deficit at two intersecting rows.  Equations
(13i), (13k), and (13l) replace the nested universal quantifiers defining
`F` by four ordinary matching-number comparisons, which is the natural form
for a transversal dual or a seed-free finite encoding.

Only rank-tight rows can contribute to the second horn.  Indeed, if
`nu(mathcal H_t)>=d(t)+1`, choose a matching of size `d(t)+1`.  For any
prescribed block `B_w`, either it is absent, in which case any `d(t)` of
those edges avoid it, or it is present, in which case deleting it leaves a
`d(t)`-matching.  Therefore

```text
nu(mathcal H_t)>=d(t)+1  ->  F(t)=empty.                    (13m)
```

Equivalently, deleting one hyperedge lowers matching number by at most one,
so the inequalities in the second horn of (13l) force
`nu(mathcal H_u)=d(u)` and `nu(mathcal H_v)=d(v)`.  Candidate (13f) thus has
the sharper exact rank form

```text
some t has nu(mathcal H_t)<d(t); or
some intersecting u,v are both rank-tight,
  nu(mathcal H_u)=d(u), nu(mathcal H_v)=d(v),
and share one essential block B_w whose deletion lowers both ranks.       (13m')
```

Rows with surplus matching rank are irrelevant to the forced-collision
horn.  A proof of (13f) may therefore focus only on the canonical deletion
hypergraphs whose maximum matching has exactly the demanded size, then show
that their essential-edge kernels cannot remain disjoint along every
intersection of row blocks.

Each nonempty forced kernel is itself highly structured.  Assume row `t`
is locally feasible and choose one demanded matching.  Every block in
`F(t)` belongs to that matching, so two distinct blocks in `F(t)` are
disjoint and

```text
F(t) is a matching,             |F(t)|<=d(t).                 (13n)
```

For a rank-tight row, put `P_t:=union_{w in F(t)} B_w` and delete every
eligible block meeting `P_t`.  Removing the forced blocks from any maximum
matching leaves a matching of size `d(t)-|F(t)|` in this point-deleted
hypergraph.  Conversely, a larger matching there could be adjoined to the
pairwise disjoint forced blocks and would contradict rank tightness.  Hence

```text
nu(mathcal H_t-P_t)=d(t)-|F(t)|.                              (13o)
```

Thus the second horn of (13m') compares small disjoint essential matchings,
not arbitrary sets of block rows.  After contracting `F(t)`, every tight
local problem has exactly the residual rank in (13o); this supplies a
canonical smaller matching instance for a transversal or alternating-path
proof of kernel intersection.

The contraction in (13o) is canonical at the level of the complete matching
family.  Removing `F(t)` from a demanded matching leaves a maximum matching
of `mathcal H_t-P_t`.  Conversely, adjoining the disjoint blocks `F(t)` to
any maximum matching of the point-deleted hypergraph gives a demanded
matching of `mathcal H_t`.  These operations are inverse, so

```text
{d(t)-matchings of mathcal H_t}
  bijects with
{(d(t)-|F(t)|)-matchings of mathcal H_t-P_t}.                  (13p)
```

Moreover the matching family on the right has empty essential-edge kernel.
If one of its blocks occurred in every residual maximum matching, (13p)
would put that block in every demanded matching of `mathcal H_t`, hence in
`F(t)`; but every block of `F(t)` meets `P_t` and was deleted.  Thus every
tight row decomposes uniquely into its forced matching and a tight
kernel-free residual matching problem.  The remaining content of (13f) is
to show that the forced matchings of all intersecting tight rows cannot have
pairwise empty intersections as sets of block rows.

### Retraction: the local alternative (13f) is false in the outer abstraction

A wider adversarial sweep reported generated outer designs satisfying the
exact negation of (13f): every row has a demanded local packing, but no two
intersecting rows force one common neighbor.  The completed sequential
invocation used

```text
PYTHONHASHSEED=41 python3 q9_structured_skew_potential.py \
  --audit-residual-gram-summary --seeds 256 --timeout-seconds 60
```

and returned

```text
branch 3: 25 locally feasible with forced collision,
           8 locally feasible with no forced collision,
         223 with a deficient row;
branch 4: 10 locally feasible with forced collision,
           1 locally feasible with no forced collision,
         245 with a deficient row.                              (13q)
```

The uncovered generated-seed labels were

```text
branch 3: 112,119,129,137,172,188,190,218;
branch 4: 251.
```

These are run-local generator labels, not canonical isomorphism identifiers.
A focused rerun of label 112 returned `UNKNOWN` during outer generation, so
the labels are not independently reproducible handles even with the stated
hash seed.  The completed process did exact local matching enumeration after
each outer SAT result, but it did not serialize the nine outer-design
payloads.  Equation (13q) is therefore strong computational counterexample
evidence, not yet a stored independently checkable counterexample.

A seed-free exact-negation model subsequently supplied the missing durable
witness.  The full branch-3 block design and cubic `K` graph are stored in
`q9_13f_counterexample.json`.  The independent command

```text
python3 research/problems/erdos-85-wip-01/verify_q9_13f_counterexample.py
```

pins all 47 incidence blocks and every `K` edge back into the unrestricted
outer equations, obtains `SAT`, and then exhaustively recomputes

```text
local deficits = 0,       forced collisions = 0.              (13r)
```

Thus (13f), (13j), (13l), and (13m') are now independently refuted as
universal statements in the outer abstraction, not merely unsafe sampled
candidates.  The reductions (13h)--(13p) remain valid identities, and the
Lean consumer remains a valid conditional theorem; what is false is the
claim that every admissible outer design supplies its `hbad` hypothesis
through (13f).

The stored survivor nevertheless dies by a very small global compatibility
core.  Exact enumeration in the same verifier gives

```text
row 7:  4 demanded packings, all containing row 29;
row 29: 82 demanded packings, none containing row 7.            (13s)
```

Thus `29 in F(7)`, but the reverse incidence `7 in X_29` is impossible for
every demanded packing at row 29.  A symmetric simultaneous selection would
require `29 in X_7` iff `7 in X_29`, so none exists.  The abstract implication
and its actual-residual-graph consumer are kernel-checked as
`not_symmetricLocalGramPackingSelection_of_forced_not_reverse` and
`false_of_forcedLocalGramNeighbor_not_reverse`.

This isolates the precise replacement horn for the counterexample:

```text
some row u forces w, but no demanded packing at w contains u.   (13t)
```

Unlike (13f), (13t) uses the membership symmetry required by a global
residual graph.  It is not yet asserted uniformly over every outer design;
the next proof-facing candidate is the trichotomy of a deficit row, a forced
collision, or the reciprocity failure (13t).  A wider seed-free test must
either prove that trichotomy or expose a survivor requiring still more global
simultaneous-selection data.

The mode `--audit-residual-gram-reciprocity-summary` computes the prospective
trichotomy exactly on generated outer designs.  For every row `u` it forms
the intersection `F(u)` and union `P(u)` of its demanded packing family; the
reciprocity horn is precisely some `w in F(u)` with `u notin P(w)`.  On the
stored counterexample it returns the unique obstruction `(u,w)=(7,29)`.

One sixty-four-per-branch regression run returned

```text
branch 3: 57 with a deficit, 43 with a forced collision,
          50 with a reciprocity obstruction;
branch 4: 64 with a deficit, 48 with a forced collision,
          54 with a reciprocity obstruction;
uncovered: 0 of 128.                                      (13u)
```

The horn counts overlap.  More importantly, this is the older 128-design
corpus in which every design was already covered by a deficit or collision;
it therefore regression-tests the reciprocity computation but adds no real
falsification resistance to the universal trichotomy.  The stored survivor
and a seed-free negation model remain the decisive tests.

The seed-free test subsequently refuted that proposed three-horn replacement.
The durable witness `q9_13t_counterexample.json`, checked independently by
`verify_q9_13t_counterexample.py`, satisfies

```text
deficits = 0, forced collisions = 0, singleton reciprocity horns = 0,
but symmetric simultaneous selection = UNSAT.                 (13v)
```

It is nevertheless killed by a one-row compatibility obstruction.  Row 2
has five demanded packings; each contains row 24 or row 46, while no demanded
packing at either reverse row contains row 2.  Thus `{24,46}` is a minimum
reverse-impossible hitting set.  The exact formal hierarchy is banked as
`HasLocalGramPackingOneRowCompatibilityObstruction`,
`HasLocalGramPackingHittingSetReciprocityObstruction`, and their consumers.
The canonical incoming reverse bounds are

```text
F_u = {w : every demanded packing at w contains u},
I_u = {w : no demanded packing at w contains u}.               (13w)
```

A compatible packing at `u` is exactly a demanded packing `X` with
`F_u subset X` and `X intersect I_u = empty`.  Kernel-checked definitions
`IsReverseIntervalLocalGramPacking` and
`IsReverseIntervalContractedExtension` reduce this to extending the already
eligible, conflict-free lower fiber `F_u` inside the deletion of `I_u`.

The exact lazy seed-free negation remains unresolved, not refuted: branch 3
timed out after four interval-row cuts (600 seconds on the third solve), and
branch 4 timed out after its first cut round.  Randomized branch-3 outer
models expose only one-unit interval rank deficits so far.  Representative
regular-triple profiles have target 5 and contracted capacity 4:

```text
u=2:  F=empty,       I intersect H_u={24,46};
u=7:  F={11,19},     I intersect H_u={9};
u=19: F=empty,       I intersect H_u={7,18}.                    (13x)
```

These are computational classification data, not a universal bound.  The
proof-facing B.3 gap is now precise: prove every admissible outer design has
some interval-deficient row (or an older forced collision), equivalently
prove the contracted residual rank cannot reach `d(u)-|F_u|` simultaneously
at all rows.

Corrected first-round profiles across both outer branches suggest a sharper
prospective statement.  After discarding rows whose lower fiber is already
inconsistent because of an old forced collision, every observed finite
interval obstruction has capacity exactly one below demand:

```text
nu_interval(u) = d(u)-1.                                      (13y)
```

This holds for all ten noncollision branch-3 profiles from the durable
witness and random seeds 0,1,2, and for sixteen genuine branch-4 profiles
from random seeds 0,1,2.
The observed mechanisms are small upper deletions and small consistent lower
contractions.  Branch 3 has `|F_u|, |I_u intersect H_u| <= 2` in these runs;
branch 4 includes the clean row-40 contraction with `|F_u|=3` and no upper
deletion.  Neither the one-unit deficit nor these support bounds are proved
universally.  Equation (13y) is a falsifiable row-class target, not a theorem.

The clean branch-4 lower-contraction prototype is durable.  The stored
`q9_branch4_row40_interval_witness.json` pins the unrestricted outer model,
and its independent verifier obtains `F_40={1,9,24}`, demand 6, and no upper
deletion.  After contracting `F_40`, exactly five residual block rows remain:

```text
17:{6,8,21}, 23:{5,14,19}, 32:{8,19},
35:{6,19},   42:{2,8}.                                      (13z)
```

Every residual block meets the two-label transversal `{8,19}`, so at most
two residual rows can be pairwise disjoint; compatible pairs exist, proving
the residual rank is exactly 2.  Three residual rows are required to extend
`|F_40|=3` to demand 6, hence the interval capacity is exactly 5.  This is a
human-sized Hall certificate for one proof model, not yet a uniform
transversal theorem.

Integral point covers do not suffice uniformly even on this durable model.
For the genuine branch-4 row-0 upper-deletion profile, the residual matching
rank is 4 but the minimum integral point cover has size 5.  An exact
fractional point cover nevertheless assigns

```text
2:1/3, 3:1/3, 8:2/3, 9:1/3, 11:1/3,
12:1, 16:2/3, 19:1/3, 22:2/3,
```

has total value `14/3 < 5`, and covers every residual block with weight at
least one.  Hence the integral matching rank is at most 4, which is attained.
The exact fractional-cover diagnostic also gives values strictly below the
residual demand on row 24, row 40, and every genuine branch-3 and branch-4
profile from the durable fixtures and random seeds 0 through 4.  This is
sixteen genuine branch-3 profiles and twenty-four genuine branch-4 profiles;
collision-inconsistent rows are excluded.  These certificates now fit the
kernel-checked consumers `reverseIntervalRankDeficit_of_fractionalPointCover`
and `reverseIntervalRankDeficit_of_scaledPointCover`.

Raw optimizer output does not determine the minimum certificate denominator.
For example, branch 4, seed 1, row 0 was first emitted with quarter weights,
but exact integer SMT also finds a scale-two certificate: labels
`{3,6,8,13,19,20,22}` have numerator one and label 9 has numerator two,
for total numerator `9 < 2*5`.  Scale one is infeasible.  By contrast, the
durable branch-4 row-0 profile has scales one and two infeasible and first
admits the displayed total-14 certificate at scale three.  Thus
half-integrality is already false, while the weaker sampled possibility that
strict certificates can always be chosen with denominator at most three
remains unproved.
This suggests a stronger prospective route: derive a fractional U1-point
mass bound below `d(u)-|F_u|` at some row.  Its observed validity is sampled
data; no uniform fractional bound is asserted.

The correctly scoped prospective disjunction is therefore

```text
an old forced collision; or
some u has fractional residual point-cover value < d(u)-|F_u|. (13aa)
```

This is not contradicted by the earlier exact fractional value-5 witness:
that witness lies in a design already carrying a forced collision.  In the
current first-model tests through random seed 4 in both outer branches, every
finite noncollision interval obstruction satisfies the strict fractional
inequality, across both upper-deletion and lower-contraction mechanisms.
The formal consumers are banked; proving (13aa) from the outer equations is
the remaining fractional Hall leaf.

There is a cleaner primal formulation which subsumes both alternatives.
For every row `u`, ask for coefficients `x_{u,w}` of total `d(u)`, between
zero and one, supported on trace-eligible blocks, with every U1 point carrying
total mass at most one.  In addition require `x_{u,w}>0` only when some
demanded packing at reverse row `w` contains `u`, and require
`x_{u,w}<1` only when some demanded packing at `w` avoids `u`.  Equivalently,
the canonical lower fiber `F_u` has coefficient one and the upper forbidden
fiber `I_u` has coefficient zero.  Then the unified prospective statement is

```text
some row has no full-demand canonical fractional interval extension. (13ab)
```

An old forced collision already makes (13ab) true: two intersecting blocks
forced into `F_u` each have coefficient one, violating the shared-point
capacity.  When `F_u` is a prepacking, fractional matching/cover duality
turns (13ab) into the strict residual point-cover alternative of (13aa).
Thus (13ab) is a stronger single target whose two elementary cases recover
the corrected disjunction; no separate collision cuts are needed in its
negation model.  The exact script `q9_fractional_interval_negation_smt.py`
returns UNSAT on the stored branch-3 and branch-4 payloads, including the old
collision prototype, while the unrestricted relaxed branch-4 abstraction is
UNKNOWN at its first 90-second solve.  This is a computational boundary, not
a proof; any future SAT payload from the relaxed build must still be checked
against the full outer constraints.

The proof-facing interface for (13ab) is now kernel checked end to end.
`IsCanonicalFractionalIntervalExtension` is the primal predicate;
`no_canonicalFractionalIntervalExtension_of_forced_sharedPoint` handles the
collision case; and `totalMass_le_totalPointWeight` is fractional weak
duality.  More precisely,
`no_canonicalFractionalIntervalExtension_of_contractedPointCover` consumes
exactly the residual certificate shape emitted above: unit mass on `F_u`,
zero mass on `I_u`, point capacity, a nonnegative cover of every remaining
block disjoint from `F_u`, and `|F_u|+totalWeight<d(u)`.  On the graph side,
`exists_canonicalFractionalIntervalExtension_of_symmetricSelection` supplies
the characteristic zero-one mass of every actual symmetric selection, and
`false_of_no_canonicalFractionalIntervalExtension` closes the contradiction.
All compile without `sorry` and print only standard axioms.  Consequently the
sole mathematical B.3 leaf in this route is no longer a consumer lemma: it is
the outer-design assertion (13ab) itself.

The first seed-free lazy-row experiment identifies an important scope
boundary.  In the maximally relaxed `Q,K` abstraction, the first outer model
has no demanded local packing at rows 4, 19, and 25; adding a single symbolic
base-packing witness at row 4 already times out before any fractional or
reverse-incidence row is activated.  This is an encoding boundary, not a
fractional counterexample.  More importantly, an actual residual design does
not need independent base-packing variables: its residual adjacency row is
already the base packing.

Only a small, explicit part of the omitted outer structure is needed for
that fact.  Retaining `row-ledger` gives the exact demanded degree.  Retaining
`b0-c4` (and hence its nested `b0-orthogonal` clause) says that two residual
neighbors of one center cannot have intersecting U1 blocks, since the center
is already their residual common neighbor.  Retaining `dtb-common` and
`dtb-cap` activates `dtb-orthogonal`: if `x` is a residual neighbor of `u`
and `b` lies in `B_x`, their positive residual-common count forces the
`K`-core count between `B_u` and `b` to vanish, exactly trace eligibility.
All other current relaxations may remain for this base-packing implication.
Thus the next honest computational/proof target is (13ab) over the
row-ledger-plus-two-orthogonality abstraction, using the existing residual
edge row rather than fresh existential base variables.                    (13ac)

The branch-3 retention ladder confirms where complexity enters.  With only
`row-ledger` retained, round one is SAT with base-infeasible row 24; adding
that single base witness makes round two UNKNOWN at 60 seconds.  Retaining
`row-ledger+residual-c4` instead gives initial bad rows 14 and 25, then the
same timeout.  Retaining `row-ledger+b0-c4` gives bad rows 12,17,24,25, then
the same timeout.  Finally the exact (13ac) retention
`row-ledger+b0-c4+dtb-common+dtb-cap` is already UNKNOWN on its initial
60-second solve, before any base, fractional, or reverse row is added.
Accordingly these runs neither prove nor refute (13ab); they show that the
full DTB orthogonality equations themselves cross the current solver
boundary.  The adjacency-as-base encoding may state edge-to-eligibility
directly as the necessary consequence proved above and retain only the much
cheaper row ledger and B0 block orthogonality.
The corresponding direct `--relation-base` branch-3 probe is likewise
UNKNOWN on its initial 60-second solve, with zero added base, fractional, or
reverse rows.  It removes the base-witness issue semantically, but the joint
edge-to-eligibility/row-ledger/B0-orthogonality system itself is already past
the present solver boundary.

A fixed-outer Benders split exposes a substantially simpler obstruction than
(13ab).  Once `Q,K` are pinned, solve only for a symmetric residual relation
`A` with the exact degree ledger, mutual trace eligibility, and the Gram law
that block-intersecting centers have no residual common neighbor.  Residual
C4-freeness is not needed for the following durable branch-4 core.  Greedy
assumption minimization leaves degree equations at only four rows:

```text
rows              6, 15, 23, 28
demands           5,  5,  6,  6
blocks            {6,14,22}, {0,14,18}, {5,14,19}, {14,17}.   (13ad)
```

All four blocks share point 14, so Gram orthogonality makes their four
residual neighborhoods pairwise disjoint.  Their mutually trace-eligible,
internally block-disjoint demanded-neighborhood family sizes are respectively
`21,36,7,308`.  Symmetry leaves exactly four possible internal-edge patterns:
no internal edge, or exactly one of `28--6`, `28--15`, `28--23`.  The family
sizes after those four restrictions are

```text
none:   (14,10,3,227);  28--23: (14,10,4,34);
28--15: (14,20,3,39);   28--6:  (7,10,3,8),
```

and exhaustive set-family search finds no pairwise-disjoint choice in any
case.  The exact verifier `q9_branch4_relation_core_verifier.py` checks the
common point, all candidate/packing counts, the symmetry pattern census, and
zero extensions.  This is a durable proof model, not a uniform theorem.
Nevertheless it suggests a sharper outer leaf: force a small same-U1-fiber
set of centers whose mutually eligible packing families have no symmetric
disjoint transversal.  That statement would contradict the actual residual
relation directly and bypass reverse intervals and fractional duality.

Even the integrality in (13ad) is unnecessary on every model tested.  Put a
single nonnegative symmetric mass `x_{uv}=x_{vu}` on each mutually
trace-eligible pair, require exact row sums `sum_v x_{uv}=d(u)`, and impose
the ordered point capacities

```text
for every u and p:  sum_{v : p in B_v} x_{uv} <= 1.           (13ae)
```

An actual residual relation supplies a zero-one solution, so infeasibility
of (13ae) is already a contradiction; neither residual C4 nor integral
matching theory is needed.  `q9_symmetric_point_mass_obstruction.py` finds
this LP infeasible on all four stored fixed outer payloads.  A separate
cross-corpus run serialized ten further distinct outer payloads (random
seeds 0 through 4 in each branch) and found (13ae) infeasible on all ten as
well.  The branch-3 mutual-eligibility graphs had 386--393 edges and
758--761 active ordered point caps; branch 4 had 377--389 edges and
749--761 caps.  These are sampled results, not a universal proof.

The dual is now the sharpest proof target: find row prices `y_u` and
nonnegative ordered point prices `z_{u,p}` such that every eligible edge
satisfies

```text
y_u+y_v <= sum_{p in B_v} z_{u,p} + sum_{p in B_u} z_{v,p},
sum_u d(u)y_u > sum_{u,p} z_{u,p}.                            (13af)
```

Summing the edge inequalities against any putative symmetric mass and then
using (13ae) gives the contradiction immediately.  Exact sparse Farkas
prices already exist on stored payloads, but their uniform derivation from
the outer incidence/K equations remains open.  In light of the fourteen
successful LP tests, (13af) is presently a cleaner uniform B.3 target than
either the integral four-row classification or the reverse-interval route.
The complete consumer is kernel checked:
`weightedDegree_le_totalPointPrice_of_symmetricFractionalPacking` proves the
global weak-duality inequality, and
`false_of_symmetricRowPointPriceCertificate` instantiates the characteristic
matrix of the actual residual relation and closes the contradiction.  Both
compile without `sorry` and use only standard axioms.

The dual support is usually much smaller than this global formulation
suggests.  Among the ten fresh outer payloads, eight admit an exact dual with
only one nonzero row price.  The other two admit exact two-row support: in
branch 3 seed 0 the priced rows have degrees `(5,5)` and their blocks share
point 3; in branch 3 seed 3 their degrees are `(5,6)` and their blocks again
share point 3.  The stored branch-4 and fractional-gap payloads also admit
two-row certificates on intersecting blocks.  Only the two older stored
branch-3 payloads failed the current one/two-row price search and require
larger support under the present optimizer; this is not a lower-bound proof
on their support.  A plausible structural refinement of (13af) is therefore:
some row has a local fractional mutual-eligibility deficit, or some
same-U1-point pair has a coupled two-row deficit, with a separate branch-3
residual if those two alternatives genuinely fail.

There is a crucial corpus distinction.  The ten fresh outer payloads were
generated before imposing local base feasibility.  Direct fractional covers
of the mutually eligible block family show a strict one-row deficit in
exactly the same eight cases having one-row dual support; the two remaining
fresh branch-3 cases are the paired certificates above.  By contrast, none
of the four stored, locally feasible survivor payloads has any strict
one-row mutual-eligibility cover.  Hence the eight random single-row kills
are useful regressions but not representative of an actual-graph survivor.
The serious global coupling evidence is the stored corpus: branch 4, the
fractional-gap payload, and `13f` have paired certificates, while `13t` has
an exact four-row certificate.

Sparse-support minimization and a fiber-directed retry sharpen this further.
In `13t`, a minimum four-row support is exactly the four non-diagonal B0
blocks through point 0; the same full non-diagonal-fiber template also gives
certificates at points 13 and 17.  The fractional-gap payload has successful
non-diagonal fibers at points 9 and 12, and the durable branch-4 payload has
nine successful fibers, at points `3,4,6,12,13,18,19,20,23`.  Thus three of
the four serious survivors admit prices supported inside the canonical
four-row set

```text
{u : p in B_u} minus {the fixed diagonal triple at p}.         (13ag)
```

The sole exception is `13f`: no non-diagonal fiber supports a certificate,
but an exact two-row dual exists on diagonal triple row 7 and disjoint pair
row 29.  This suggests a much more concrete prospective dichotomy than
arbitrary sparse support: some U1 point has a bad non-diagonal fiber (13ag),
or a special diagonal/pair configuration supplies the price certificate.
The fiber successes and the `13f` exception are still fixed-model evidence,
not a proved classification.

There is now one exact reduced template covering all four serious survivors.
Allow the four non-diagonal rows through `p` together with at most one
arbitrary auxiliary row to carry nonnegative row prices.  Restrict ordered
point prices to those outgoing from the at most five allowed rows or incoming
at the single common point `p`.  The verifier
`q9_fiber_plus_aux_price_corpus.py` solves this restricted dual and then
rechecks every inequality and the strict margin over `Fraction`.  The three
models already covered by (13ag) retain pure-fiber certificates.  The `13f`
exception becomes a genuine fiber-plus-one-auxiliary certificate, for example
at `p=12` with fiber `{12,22,30,41}`, auxiliary row 4, actual priced rows
`{4,12,22,41}`, and exact margin 1.  Equally, the previously isolated
diagonal/pair mechanics occur at `p=14`, auxiliary row 7, with actual priced
rows `{7,13,16,29}`.  Thus the prospective outer theorem can be stated as a
single five-row horn rather than a disjunction between unrelated price
languages:

```text
some p and a admit a strict reduced price certificate supported on
({u : p in B_u} minus {p % 8}) union {a}.                     (13ah)
```

Independent integral-core evidence points to the same bounded shape without
proving (13ah).  Across seeds 0--4 in both branches, exact minimized residual
degree cores (with residual C4 ablated) have sizes
`[2,5,2,5,2]` in branch 3 and `[1,2,1,5,1]` in branch 4.  Every five-row core
is a dense four-row common-point cluster plus one auxiliary row.  This is a
useful structural target, but it must not be conflated with the dual result:
the core corpus includes locally infeasible random outers, while (13ah) has
so far been checked only on the four stored locally feasible survivors.
Deriving existence of `p,a` and the reduced prices from the outer equations
remains the decisive uniform gap.

An even cleaner regression supersedes (13ah) as the primary target: restore
the omitted diagonal row and use the full five-row point fiber
`F_p={u:p in B_u}`.  Unit row price on every member of `F_p`, with the same
local-outgoing/outside-at-`p` point-price mask, gives a strict exact
certificate on every serious survivor.  The successful point/cost examples
are `13f`: `p=4`, `26<27`; `13t`: `p=13`, `616/23<27`; fractional gap:
`p=9`, `105/4<27`; branch 4: `p=4`, `25<27`.  The exact scanner
`--scan-unit-full-fibers` checks all edge inequalities and costs over
`Fraction`.  This removes both the auxiliary-row choice and variable row
prices from the prospective outer theorem:

```text
some p has reduced unit full-fiber cover cost
  C_p < sum_{u:p in B_u} d(u).                               (13ai)
```

The most naive route to (13ai) is already falsified by the corpus.  Summing
the independently minimized gaps `C_p-D_p` over all 24 points gives positive
totals on every serious payload: approximately `10.179`, `27.985`, `15.458`,
and `5.903`, respectively.  Therefore an unweighted inequality
`sum_p C_p <= sum_p D_p` cannot prove existence of a strict fiber.  A uniform
argument must select or weight a structural class of points, or exploit
coupled covers rather than independent minima.  Statement (13ah) remains a
valid exact fallback regression, but (13ai) is now the sharper proof leaf.
Nor can the rational cover simply be replaced by an ordinary hitting set.
Binary point-price minimization gives strict full-fiber covers for `13f`, the
fractional-gap model, and branch 4, but none for `13t`.  There the best binary
cover is equality `27=27` at `p=0`; at the strict fractional point `p=13`,
the binary optimum is `28>27` while the rational optimum is
`616/23<27`.  Fractional weights are therefore essential to a uniform proof
of (13ai), not an artifact of the LP implementation.
They need not be arbitrary on the serious corpus.  After scaling all point
prices by a common denominator, the exact integer verifier
`q9_bounded_denominator_full_fiber.py` proves that denominator 1 suffices for
the other three models, while `13t` first becomes strict at denominator 6:
at `p=13` it has scaled cost `161<162`, with every scaled edge-cover slack
nonnegative.  Denominators 1 through 5 are integer-infeasible at every point
of that payload.  This suggests the finite prospective strengthening
`6 C_p <= 6 D_p-1` for some full fiber.  It is only a corpus bound—nothing yet
shows that sixth-integral prices suffice for every admissible outer design—
but it replaces the observed denominator 46 LP vertex by a much smaller
integer ledger and gives a concrete target for outer arithmetic.

One promising selector must retain the same scope discipline.  Among the
four serious survivors, `13t` is the only payload whose cubic U1 core `K` is
triangle-free; each other model has a strict rational full-fiber cover at a
triangle vertex.  However this is false in the outer-only relaxation:
branch-3 fresh seed 3 has triangle vertices `{4,8,19}` and none of their
fibers is strict, although other points do have strict fibers.  Exact
enumeration additionally shows that every row of this payload has an
eligible block-disjoint base packing of the demanded size.  Thus even
triangle incidence plus rowwise local base feasibility is insufficient; a
triangle horn would have to use stronger global symmetric-relation, Gram, or
reverse-compatibility consequences.  Moreover serious `13f` has no
*integral* strict cover at a triangle vertex, so rational prices remain
necessary in that branch as well.

Finally, combining the corrected core-edge contraction (5) with the
incidence-masked identity (9) gives the exact transfer

```text
t(K) + |E(K) intersect E(D)|
  = T_R + Z/2  (mod 2).                                      (14)
```

Here `E(K) intersect E(D)` is precisely the set of triangle-free original
edges internal to `U1` (the twelve same-color K-edges already lie in their
high-root triangles), while `Z` is the triangle-free U1--B0 incidence cut.
Thus (14) moves the collision parity between the internal-core description
and the residual-fiber/cut description without the formerly double-counted
marked-pair term.  By itself it is a transfer identity, not a parity
terminal.

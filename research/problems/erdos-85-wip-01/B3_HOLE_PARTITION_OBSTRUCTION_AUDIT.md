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
In all 24 four-seed pair/design instances the graph has only 6--22 arcs, all
recurrent strongly connected components have order two, four, or six, and
there is no odd directed closed walk.  This suggests the precise terminal

```text
FLAT-HANDOFF BIPARTITENESS:
the flat handoff graph of every admissible (Q,K) has no odd directed cycle.
                                                               (12qx)
```

The observed bipartition is not an affine parity of the obvious state data:
parallel class of the root and its unique neighbor, selected-label color,
and all binary digits of `(n,c_pair,c_all)` give an inconsistent `F_2`
edge-sign system across the 283 recurrent sampled arcs.  Thus (12qx) needs
the detailed realizable census/eligibility relation, but no matching or LP
variables remain.  Together with (12qv), it would eliminate the
collision-free odd residual and leave every alternating obstruction charged
to the finite root-own collision budget.

There is a smaller sufficient graph which explains the sampled parity.
Define the **flat signature graph** with vertex set the full signatures
`(role,n,c_pair,c_all)` which occur on flat flags.  Join signatures `sigma`
and `tau` when some shared-label pair `(t,b),(u,b)` is reciprocal and flat:
`t,u` have the same role, each is the other's unique same-role eligible
occupant in `F_b`, and their signatures are `sigma,tau`.  Every horizontal
step of a flat handoff walk crosses one such signature edge, while its
vertical step stays at the incoming signature.

In all 24 sampled instances this undirected signature graph is a **forest**.
It has between three and sixteen nonisolated vertices and between two and
nine edges; in every case `|E|=|V|-number_of_components`.  Therefore every
closed projected walk has even length, which proves (12qx) for that instance
without inspecting the detailed handoff arcs.  This suggests the sharper
uniform terminal

```text
FLAT-SIGNATURE FOREST:
reciprocal unique-same-role shared-label pairs form a forest on full
root signatures.                                               (12qy)
```

Statement (12qy) depends only on the outer eligibility graph and four scalar
root flags; the monotone transport disappears from the hypothesis.  A cycle
of signature classes would have to be realized by a cyclic sequence of
linear block intersections whose endpoints have matching
`(role,n,c_pair,c_all)` data and unique same-role fiber degree.  Excluding
exactly that configuration is now the most economical seed-free route to
the collision-free terminal.

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

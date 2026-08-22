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

Every row in `P_g` has residual degree six, while the marked B1 vertex has
exactly five B0 defect neighbors.  Hence `|M_g|=5` and

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

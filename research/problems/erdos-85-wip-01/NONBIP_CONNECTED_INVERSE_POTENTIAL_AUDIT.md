# NONBIP-CONNECTED: inverse-Laplacian neighborhood potentials

## Scope

This is a bounded probe beneath `A-REG-NONBIP -> NONBIP-CONNECTED [q]`.
It assumes the putative connected survivor, equivalently that its symmetric
adjacency matrix `A` is nonsingular, and asks what extra incidence structure
is visible in a column of `A^{-1}`.  This is not a terminal and it does not
replace the singularity gap.

Let `A` be loopless, symmetric, `q`-regular and C4-free on `n=q^2` points,
let `D` be the second-order defect graph, and write

```text
A^2 = L_D + J.
```

Suppose `D` is connected.  Then `A` is nonsingular.  Fix a point `y`, put
`S=N_A(y)`, and let

```text
x = A^{-1} e_y.
```

## Exact potential system

Since `A 1 = q 1`, symmetry gives

```text
sum_v x_v = 1/q.                                      (P1)
```

The square identity and `A x=e_y` then give

```text
L_D x = 1_S - (1/q) 1.                                (P2)
```

Thus `x` is the uniquely normalized electrical potential obtained by
injecting `1-1/q` at each point of `S` and extracting `1/q` at every point
outside `S`.  The original inverse equation is the stronger block-sum law

```text
sum_{u in N_A(z)} x_u = 1 if z=y, and 0 otherwise.     (P3)
```

In particular,

```text
sum_{u in S} x_u = 1,
sum_{u outside S} x_u = -(q-1)/q,                     (P4)
x^T L_D x = 1-1/q^2.                                  (P5)
```

The discrete maximum principle applied to (P2) says that every global
maximum of `x` lies in `S` and every global minimum lies outside `S`.
Equation (P4) makes the maximum positive and the minimum negative.  This does
**not** say that all sources are positive or all sinks are negative.

## Cross-neighborhood matching identity

For `v outside S`, let

```text
t_y(v) = (A^3)_{y,v}.
```

This is the number of edges between `N_A(y)` and `N_A(v)`.  C4-freeness
makes those edges a matching, so `0 <= t_y(v) <= q`.

Counting these length-three paths without weights gives

```text
sum_{v outside S} t_y(v) = q(q-1)^2,                 (P6a)
```

so their average over the `q(q-1)` sinks is `q-1`; in particular a
nonperfect sink always exists.

Here "outside `S`" includes the root `y` itself, because `A` is loopless.
Its matching count is

```text
t_y(y) = 2 triangle_A(y),
q-t_y(y) = deg_T(y),                                  (P6b)
```

where `T=A intersect D` is the triangle-free-edge graph.  Thus the root
term must not be silently treated like an ordinary off-diagonal sink.

Every block other than `N_A(y)` meets `S` in zero or one point.  Sum (P3)
over the `q-1` other blocks through each point of `S`.  A point `v` outside
`S` is counted exactly `t_y(v)` times.  Hence

```text
sum_{v outside S} t_y(v) x_v = -(q-1),                (P6)
sum_{v outside S} (q-t_y(v)) x_v = 0.                 (P7)
```

Equivalently, with `R=V minus (S union {y})`,

```text
deg_T(y) x_y + sum_{v in R} (q-t_y(v)) x_v = 0.       (P7')
```

The total deficiency in (P7) is `q(q-1)`.  Since the root coefficient is
at most `q`, for `q>=4` at least one off-diagonal sink in `R` is nonperfect.

Equation (P7) is the nonvacuous residue of the probe.  Its coefficients are
nonnegative matching deficiencies, and their parities are exactly the
nonadjacent transport data already exposed by the canonical `K` graph.
Together with the maximum principle it forces the following dichotomy:

* some negative sink has `t_y(v)=q`, i.e. its two neighborhoods are joined
  by a perfect matching; or
* some nonperfect sink has positive potential.

Indeed (P4) supplies a negative sink.  If no negative sink has zero
coefficient in (P7), its strictly negative weighted contribution must be
balanced by a positive term.

This is a genuine inverse/connectedness formulation, not a determinant or
Smith restatement.  An initially proposed sufficient terminal was the
root-aware sign condition

```text
x_v < 0 for every v in R,
deg_T(y) x_y <= 0.                                    (P8)
```

Indeed (P7') would then be nonpositive, and the guaranteed nonperfect
off-diagonal sink would make it strictly negative.  However, (P8) is not
merely unproved: it is incompatible with the original block-sum law (P3).
The radius-two Moore count already proves that `y` lies in at least one
triangle.  Since `D` has degree `q-1` and its A-edge part at `y` has degree
`deg_T(y)=q-2 triangle_A(y)`, the set
`N_D(y) minus N_A(y)` has size `2 triangle_A(y)-1>0`.  Choose `z` in that
set.  Then `y` and `z` are nonadjacent and have no common A-neighbor, so

```text
N_A(z) is a subset of R = V minus (S union {y}).       (P8-cut)
```

But (P3) at `z != y` gives `sum_(u in N_A(z)) x_u=0`, whereas strict
negativity on `R` would make this sum strictly negative.  Thus no survivor
can satisfy (P8).  More generally, each such non-A defect-neighbor block is
either identically zero in the potential or already contains both signs.
For a triangle-free A-edge `z in N_D(y) intersect S`, the same block-sum
argument includes the root term instead.  The mixed-sign horn is forced
locally rather than being an exceptional case to eliminate by a maximum
principle.

The diagonal sign is independently delicate: the Petersen graph, a nearby
nonsingular C4-free control at different parameters, has
`(A^{-1})_{yy}=1/3>0`.

### The correct weak-sign residue: a zero collar

Replacing strict negativity by the root-aware weak conditions

```text
x_v <= 0 for every v in R,
deg_T(y) x_y <= 0                                    (P8w)
```

does not give a contradiction, but it has a rigid exact consequence.  For
each source `s in S`, every D-neighbor lies in `R`, except possibly the root
`y`; the latter occurs exactly when `sy` is a triangle-free edge.  Under
(P8w) all those potentials are nonpositive.  Evaluating (P2) at `s` gives

```text
sum_(v in N_D(s)) x_v = (q-1)(x_s-1/q) <= 0.
```

Since `sum_(s in S) x_s=1`, all `q` inequalities must be equalities:

```text
x_s = 1/q for every s in S,
x_v = 0 for every v in N_D(S).                        (P11)
```

Here the second conclusion uses that every summand is nonpositive.  If the
root has a triangle-free incident edge, it too belongs to `N_D(S)`, so
`x_y=0`; otherwise its coefficient in (P8w) is already zero.

For an off-diagonal sink `v in R`, direct expansion of
`D=(q-1)I-A^2+J` gives

```text
q-t_y(v) = (AD)_{yv}
           = |N_A(y) intersect N_D(v)|.
```

Consequently `v` is nonperfect exactly when `v in N_D(S)`.  Thus (P11)
says that every nonperfect sink has potential zero.  All negative mass from
(P4) is confined to perfect-transport sinks (including the root only when
`deg_T(y)=0`).  This is the correct replacement for P8:

```text
positive root term `deg_T(y)x_y`, or a positive off-diagonal sink, or a zero
collar around S with all negative potential supported on `t_y(v)=q`. (P12)
```

The only plausible continuation of this lane is therefore a theorem
excluding the zero-collar/perfect-transport horn.  Uniform sink negativity
is not a candidate.

### Zero collar as a fractional transversal cover

For a root with `deg_T(y)>0`, the remaining horn has an exact positive
reformulation.  (The zero-degree root correction is recorded below.)  Let

```text
C_y = {z != y : (A^2)_{yz}=1}
```

be the collinearity layer of `y`.  It is the disjoint union, indexed by
`s in S`, of the `q` cells `N_A(s) minus {y}`, each of size `q-1`; hence
`|C_y|=q(q-1)`.  Under (P8w), let

```text
P_y^- = {p in R : t_y(p)=q and x_p<0},
w_p = -q x_p for p in P_y^-.
```

For `z in C_y`, exactly one source lies in `N_A(z)`.  Equation (P3), the
zero collar (P11), nonpositivity on `R`, and `x_y=0` (forced here by
`deg_T(y)>0`) therefore give

```text
sum_(p in P_y^- intersect N_A(z)) w_p = 1.            (P13)
```

Conversely, `t_y(p)=q` says that the A-edges between `S` and `N_A(p)` form
a perfect matching.  Thus `N_A(p)` is contained in `C_y` and contains
exactly one point from every cell `N_A(s) minus {y}`.  It is a transversal
of the q-cell partition.  C4-freeness says that two such transversal blocks
intersect in at most one point.

Double-counting (P13), and then evaluating it at a point of each block,
gives the exact fractional-cover ledger

```text
sum_(p in P_y^-) w_p = q-1,
0 < w_p <= 1.                                         (P14)
```

In particular `|P_y^-|>=q-1`, and the A-neighborhood of every one of the
`q(q-1)` points in `C_y` contains a negative perfect-transport sink.  If
the cover is
integral, then it consists of exactly `q-1` weight-one blocks whose
neighborhoods partition `C_y`.  Those `q-1` labels form a `K_(q-1)` in D,
because their A-neighborhoods are pairwise disjoint.  This is close to, but
not yet, a D-component: each clique vertex still has one D-neighbor outside
the clique, and proving that the neighbor is always `y` is an additional
location statement.

The exact remaining interface is therefore not a sign theorem.  It is an
integrality/location theorem for the self-polar fractional transversal cover
(P13)--(P14).  Generic fractional matching theory cannot be cited as if it
supplied integrality; the labels `p` and the blocks `N_A(p)` must enter.

If `deg_T(y)=0`, every source belongs to `C_y` and (P11) does not determine
`x_y`.  For `z in C_y minus S`, the right side of (P13) remains `1`; for
`z in S`, the root is also in `N_A(z)` and the right side becomes
`1+q x_y`.  Accordingly the total weight is

```text
sum_(p in P_y^-) w_p = q-1+q x_y.                    (P14-root)
```

Thus the clean unit cover and mass `q-1` must not be asserted in the
all-triangular root case without first controlling the diagonal inverse
entry `x_y`.  This is a separate horn, not a harmless normalization.

There is a sharp abstract countermodel to integrality already at `q=4`.
Take four cells indexed by the projective line
`P^1(F_3)=F_3 union {infinity}`, each containing the three symbols of `F_3`.
For `(a,b) in F_3^2`, take the transversal

```text
B_(a,b) = {(t, at+b) : t in F_3} union {(infinity,a)}.
```

Two distinct blocks meet in exactly one point: the difference of their two
linear forms has exactly one projective zero.  Each of the twelve points
lies in exactly three of the nine blocks.  Assigning weight `1/3` to every
block therefore satisfies (P13)--(P14), while no two blocks are disjoint,
so an integral three-block cover is impossible.  Hence cell transversality,
linearity, pairwise intersection at most one, and the exact fractional mass
still do not imply integrality.  Any successful continuation must use that
the block `N_A(p)` is indexed by its own point `p` inside the same symmetric
loopless incidence structure; dropping that self-polar placement makes the
desired conclusion false.

The bounded script
`inverse_potential_fractional_cover_selfpolar_q4.py` restores the first
piece of that placement data.  It assigns the nine projective blocks to
distinct point labels, requires looplessness (`p notin B_p`), and requires
symmetry between every pair of labelled blocks
(`p in B_r` iff `r in B_p`).  There are twelve cell points and exactly four
points outside `C_y`, matching the full `q^2=16` point budget.

The exact finite query is UNSAT at four outside points.  It remains UNSAT
with five, six, seven, or eight outside points, and becomes SAT with nine by
placing every block label outside the cells.  Thus the explicit nonintegral
cover above does **not** survive even the partial self-polar labelling law at
the correct square-order budget.  This is bounded evidence, not a universal
integrality theorem: the solver fixes one cover at `q=4`, and it does not
complete the unlabelled rows to an ambient regular C4-free adjacency matrix.
Its decision value is positive nonetheless.  Unlike generic transversal
linearity, self-polar placement plus the `q^2` point budget distinguishes the
known fractional countermodel, so that is the precise surviving mechanism
class to investigate.

The broader script
`inverse_potential_selfpolar_fractional_cover_q4_sat.py` quantifies over the
transversal blocks and positive rational cover weights themselves.  Merely
requiring labels to lie in `R` is still insufficient: it finds a six-block
model with every weight `1/2`, distinct loopless labels, symmetric labelled
incidence, and pairwise block intersection at most one.

That witness exposes one further incidence-location law.  If a perfect sink
`p` lies in the cell `N_A(s) minus {y}`, then `s in N_A(p)`.  Since
`N_A(p) subset C_y`, the source `s` must itself belong to `C_y`; equivalently
the root edge `ys` lies in a triangle.  At `q=4` with `deg_T(y)>0`, the root
has exactly one triangle.  Hence, up to cell symmetries, a negative perfect
sink has only five possible labels: the four nonsource points in the two
triangle-supported cells, and the unique point of
`R minus C_y = N_D(y) minus N_A(y)`.

With precisely this faithful label set, every nonintegral support size is
UNSAT: positive weights have total three, so a fractional cover needs four
or five blocks, and the solver excludes both sizes.  Three blocks would have
all weights one.  Thus the full partial-self-polar cover abstraction at the
faithful positive-`deg_T` q=4 root forces integrality.  This remains bounded
evidence, not a q-generic theorem and not an ambient graph classification,
but it identifies a sharper candidate mechanism than self-polarity alone:

```text
self-polarity + perfect-transport label location + square-order budget
    may force the zero-collar cover integral.          (P15 candidate)
```

At general root triangle count `r<q/2`, the same elementary location law
leaves `2r(q-2)` candidate labels inside the triangle-supported cells and
`2r-1` candidates in `R minus C_y`, for a total of
`2r(q-1)-1`.  Cardinality alone is therefore not enough at larger q; a
proof of (P15) must use symmetric incidence between those candidate labels.

#### P15 is false at the next even parameter

`inverse_potential_selfpolar_fractional_cover_generic_sat.py` implements the
same faithful abstraction for any even `q` and root triangle count
`0<r<q/2`.  At `q=6`, `r=1`, the candidate label set has size nine.  After
the sound symmetry break that orders the distinct block labels, the complete
support-size verdict is

```text
m=6: UNSAT
m=7: UNSAT
m=8: UNSAT
m=9: SAT
```

The `m=9` witness uses all nine allowed labels, eight weights `1/2`, and one
weight `1`.  The script independently checks exact rational unit coverage,
looplessness, symmetric incidence between all labelled blocks, transversal
support, and pairwise block intersection at most one.  Thus it is a faithful
countermodel to P15 at its stated partial interface.

This does not construct an ambient `6`-regular C4-free graph on 36 vertices:
the rows indexed by points outside the nine negative perfect sinks remain
unfilled.  It does prove that

```text
self-polarity + perfect-transport label location + q^2 point budget
```

does **not** force fractional-cover integrality uniformly in even `q`.
Consequently P15 is **CUT** as a q-generic terminal.  A continuation would
have to use completion of every unselected row to the same symmetric regular
C4-free adjacency matrix, not merely another constraint internal to the
fractional cover.  No q=8 version was launched: once the generic mechanism
failed at q=6, a finite order-64 probe would fall under the standing park and
would not repair the uniform proof gap.

The latter warning has an exact bounded control in
`nonbip_connected_inverse_potential_p2_control.py`.  A connected cubic graph
on 16 vertices with `q=4` and a four-point source set has the normalization
in (P1), satisfies (P2) exactly over `Q`, and has positive sink potentials at
vertices 10 and 14.  This is not an ambient incidence countermodel: it
isolates the fact that any proof of (P8) must consume (P3), rather than the
Laplacian maximum principle alone.

## Faithful q=4 falsifier probe

`nonbip_connected_inverse_potential_q4_sat.py` restores the full incidence
matrix: symmetric, loopless, 4-regular and C4-free on 16 vertices, with an
exact rational column equation `A x=e_y`.  C4-freeness makes the graph
induced on `N_A(y)` a matching, so the search splits exhaustively by zero,
one or two triangles through `y`.

The zero-triangle branch is UNSAT already at the graph layer (the usual
radius-two Moore count).  In each of the one- and two-triangle branches, a
bounded enumeration of 1,000 labelled graph models found every adjacency
matrix singular; a repeated 100-model run gave rank histogram `{15: 100}`
in each branch.  The direct mixed Boolean/rational sign-violation queries in
the latter two branches returned `unknown` at 300 seconds, not UNSAT.

This is evidence, not a classification: labelled model blocking does not
prove that all q=4 configurations were enumerated.  Its useful verdict is
that q=4 supplied no nonsingular incidence control on which (P8) could even
be evaluated.  The exact (P8-cut) argument above does kill the proposed
strict sign condition, so no further model search is needed to decide it.

## Global aggregation: exact collapse to a weighted complement

There is a compact matrix form of (P7), but summing it does not remove the
root-sign problem.  Define the symmetric nonnegative matrix

```text
C = (J-A) hadamard (qJ-A^3).
```

The mask `J-A` includes the diagonal and excludes exactly the A-edges.  On
its support, `(A^3)_{yv}` is a cross-neighborhood matching size, hence every
entry of `C` is nonnegative.  Equations (P6a) and (P6b) say

```text
C 1 = q(q-1) 1,
C_yy = deg_T(y).
```

For `X=A^{-1}`, the whole family (P7), for all roots at once, is precisely

```text
diag(CX) = 0.                                         (P9)
```

Consequently `trace(CX)=0`, while both `CX` and `XC` have row sum `q-1`.
The symmetrization `(CX+XC)/2` is therefore a symmetric zero-diagonal signed
matrix of row sum `q-1`.  This is a reformulation, not a positivity theorem:
neither factor order preserves entrywise signs.

The relation to the already-banked incidence bottleneck is exact.  For

```text
E = AD-(J-A) = qA-A^3+(q-1)J,
```

one has

```text
C = (J-A) hadamard (E+J).                             (P10)
```

Thus scalar Frobenius bounds on `E` do not control `trace(CX)` or the root
term; (P9) says that trace is already zero.  A tempting PSD exit is also
false at the ambient incidence level.  On the exact q=4 fixed-free control,
`C` has constant row sum 12, while `C_00=C_44=0` and `C_04=1`.  Therefore
`(e_0-e_4)^T C (e_0-e_4)=-2`, whereas `1^T C 1>0`.  Hence `C` is indefinite,
so no argument of the form `C >= 0`, `X^2 > 0`, and trace positivity is
available without a genuinely new q-dependent input.

**Aggregate verdict: CUT.**  Unweighted summation gives only (P9), and the
natural weighted-complement matrix is indefinite and is exactly the masked
incidence bottleneck already on the map.  The live content remains
pointwise but necessarily mixed-sign: exploit the forced sign changes inside
defect-neighbor blocks, or a nonscalar interaction of `C` with `A^{-1}`.
Further trace wrappers do not advance the node.

## Faithful-control boundary

The parameterized bounded falsifier
`nonbip_connected_inverse_potential_control_sat.py` makes explicit why a
larger example sweep is not a useful next lane.  It searches actual
symmetric loopless `q`-regular C4-free graphs on `q^2` vertices, splits by
the root matching, computes `A^{-1}e_y` exactly whenever `A` is nonsingular,
and reports the first P8 violation.

There are no odd-`q` controls: the degree sum `q^3` is odd.  The
zero-root-triangle stratum is uniformly empty because the root and its first
two distance layers would contain `1+q+q(q-1)=q^2+1` points.  Thus `q=3`
and `q=5` are eliminated without a solver, while the first even parameter
`q=4` is exactly the singular sampled regime recorded above.  At a binary
parameter `q>=8`, a faithful nonsingular control would itself be a
counterexample to NONBIP-CONNECTED, the theorem this lane is meant to prove.
Consequently example-based validation of P8 is not logically cheaper than
the target; escalating the labelled SAT search would be a disguised census.

**Control verdict: CUT.**  Keep the script as a falsifier for any externally
supplied nonbinary even control, but do not launch a larger graph census.
The sign target must respect the forced mixed signs in (P8-cut).  Any useful
replacement must use entrywise square-root/incidence data; unweighted trace
and generic connected-Laplacian information have already been eliminated.

## Verdict

**EXACT INTERFACE, PROPOSED SIGN TERMINAL RETRACTED.**  Equations (P1)--(P7')
remain valid, but (P8) is false by the one-line defect-neighbor block
argument (P8-cut).  The next bounded question, if this interface is pursued
at all, must use the mixed signs that (P3) forces inside every nonzero
defect-neighbor block; it cannot seek uniform negativity on `R` or a minor
variant of that condition.  Formalizing (P1)--(P7') without a new
mixed-sign/location theorem would be another wrapper and is not justified.

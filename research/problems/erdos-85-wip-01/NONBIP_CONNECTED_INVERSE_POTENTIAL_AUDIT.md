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
Choose any `z in N_D(y)`, which exists because `D` has degree `q-1>0`.
The definition of a defect edge says that `y` and `z` are nonadjacent and
have no common A-neighbor.  Therefore

```text
N_A(z) is a subset of R = V minus (S union {y}).       (P8-cut)
```

But (P3) at `z != y` gives `sum_(u in N_A(z)) x_u=0`, whereas strict
negativity on `R` would make this sum strictly negative.  Thus no survivor
can satisfy (P8).  More generally, each defect-neighbor block is either
identically zero in the potential or already contains both signs.  The
mixed-sign horn is forced locally rather than being an exceptional case to
eliminate by a maximum principle.

The diagonal sign is independently delicate: the Petersen graph, a nearby
nonsingular C4-free control at different parameters, has
`(A^{-1})_{yy}=1/3>0`.

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

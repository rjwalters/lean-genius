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
Smith restatement.  A terminal would follow from the still-unproved
root-aware sign conditions

```text
x_v < 0 for every v in R,
deg_T(y) x_y <= 0.                                    (P8)
```

Indeed (P7') would then be nonpositive, and the guaranteed nonperfect
off-diagonal sink would make it strictly negative.  Neither the maximum
principle nor the present incidence ledger proves (P8): Poisson potentials
on general connected graphs can have source and sink values on both sides of
the chosen normalization.  The diagonal sign is independently delicate:
the Petersen graph, a nearby nonsingular C4-free control at different
parameters, has `(A^{-1})_{yy}=1/3>0`.

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
be evaluated.  Thus the faithful bounded falsifier did not kill the route,
but neither did it validate the sign condition; the first decisive test must
use a nonsingular control at other parameters or a q-generic argument.

## Verdict

**NEW EXACT INTERFACE, NOT A TERMINAL.**  The next bounded question is
whether the self-indexed C4-free block sums (P3), beyond the Laplacian
equation alone, force the off-diagonal sign condition and control the root
term in (P8), or otherwise forbid the mixed-sign horn of (P7').  Formalizing
(P1)--(P7') without such a sign/location theorem would be another wrapper
and is not justified.

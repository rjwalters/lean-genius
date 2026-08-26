# NONBIP-CONNECTED triangle affine-potential q=4 audit

## Claim tested

For a 4-regular C4-free graph on 16 vertices, let `t_x` be the number of
triangles through `x`, let `H` be vertex-by-triangle incidence, let `K` be
the graph obtained by deleting all triangle edges, and put
`M = A_K - diag(t)`.  The probe tests the two local identities

1. `sum_{y in N_K(x)} t_y = t_x^2 - 5 t_x + 6` for every vertex `x`;
2. `sum_{x in tau} t_x = 5` for every triangle `tau`.

If both hold, the affine vector `z_x = (5 - 3 t_x)/2` satisfies
`Mz = 1` and `H^T z = 0`.  Since `A = M + HH^T`, the vector
`(1 - 4z)/3 = -M^-1 t` is then an explicit nonzero kernel vector of `A`.

The same algebra at general `q > 2` would use

`z_x = (q + 1 - 3 t_x)/(q - 2)`

and the candidate identities

`K t = t^2 - (q+1)t + (q^2+2)/3`,
`sum_{x in tau} t_x = q+1`.

## Global arithmetic terminal

The two local identities together have a stronger global consequence.  Put
`S1 = sum_x t_x`, `S2 = sum_x t_x^2`, and let `T` be the number of
triangles.  Summing the first identity over vertices and using
`deg_K(x)=q-2t_x` gives

```text
(2q+1) S1 - 3 S2 = q^2(q^2+2)/3.
```

Summing the second identity over triangles gives `S2=(q+1)T`, while
double-counting vertex-triangle incidences gives `S1=3T`.  Substitution
therefore forces

```text
T = q(q^2+2)/9.
```

For binary `q=2^k`, divisibility by nine holds exactly when
`q mod 9` is `4` or `5`, equivalently `k mod 6` is `2` or `5`.  The first
class begins with the genuine exceptional control `q=4`; among the intended
`k>=3` cases, proving both identities would immediately close four of the
six exponent classes, leaving only `k = 5 (mod 6)` (and later members of
`k = 2 (mod 6)`) for a further terminal.  Thus the affine route is not by
itself yet a uniform proof even if both identities are established.

## Bounded verification

Run:

```text
python3 research/problems/erdos-85-wip-01/nonbip_connected_triangle_affine_potential_q4.py --models 256
```

The rooted Z3 enumeration fixes `N(0)={1,2,3,4}`, imposes degree four and
at most one common neighbor for every vertex pair, and blocks each complete
labeled model after checking it.  On every checked model the program also
verifies exactly over `sympy.Rational` that `Mz=1`, `H^Tz=0`, and
`A((1-4z)/3)=0`.

Observed output:

```text
bounded_models=256
triangle_counts={8: 256}
T1_universal_on_sample=true
T2_universal_on_sample=true
affine_certificate_universal_on_sample=true
triangle_degree_constant_on_defect_edges=true
```

## Stronger defect-child propagation candidate

The same exhaustive run tests a stronger local pattern: whenever two
vertices have zero common neighbors (that is, they are adjacent in the
second-order defect graph `D`), their triangle degrees are equal.  This also
holds in all 256 controls.  In the q=4 profile it says that `t`, equivalently
`deg_K=q-2t`, is constant on each of the two defect components.

This suggests the q-generic Deza-child statement

```text
D.Adj u v -> t_u=t_v.
```

It would turn connectedness of `D` into global uniformity of triangle degree.
That conclusion is **not yet a terminal**: uniform `t` or `deg_K` alone does
not determine its value and does not imply the weighted-neighbor identity
`A deg_K=((q^2-4)/3)1`.  A successful use therefore still needs either an
independent arithmetic pin on the common degree or a structural exclusion
of the resulting uniform Deza graph.  The bounded observation must not be
cited as providing either missing step.

## Scope

This is positive bounded evidence, not a proof of either candidate identity.
The 256 rooted labeled models are not asserted to exhaust isomorphism classes,
and the faithful q=4 controls used here have disconnected deficiency graph.
No connected-deficiency hypothesis is encoded.  In particular, this probe
does not establish the q-generic NONBIP-CONNECTED terminal; its useful output
is a sharply local candidate whose two identities can now be attacked
combinatorially or falsified at larger parameters.

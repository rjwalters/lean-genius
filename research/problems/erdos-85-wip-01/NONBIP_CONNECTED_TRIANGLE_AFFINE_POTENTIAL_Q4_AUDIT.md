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
`k = 2 (mod 6)`) for a further terminal. This global divisibility argument
alone does not cover every exponent. The later
`NONBIP_CONNECTED_TRIANGLE_DEGREE_KERNEL_AUDIT.md` supplies the uniform
connected-defect consumer: the two identities imply
`At=((q²+2)/3)1`, which forces a nonzero kernel vector of A. The unresolved
step is proving the identities (or that weaker weighted-neighbor identity).

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

## Saturated triangle neighborhoods do not force the proposed triangle sum

Follow-up, 2026-09-06, Sol1. This is a uniform partial-graph control, not a
regular square-order graph or a counterexample to A-REG.

For binary q>=16 put s=q-2 and f=q/2-2. Take a root triangle u0,u1,u2
and three disjoint classes C0,C1,C2, each indexed by Z/s. Join ui to all
of Ci. Begin with s² outside vertices corresponding to the Latin triples
`(a,b,a+b mod s)`, each adjacent to its three class entries. The f triples
`(i,i,2i)`, `0<=i<f`, are disjoint in each coordinate. Replace each of
these outside vertices by three vertices corresponding to its three pairs.
Add three isolated outside vertices. In each class, pair up the vertices
not covered by the selected triples and add this matching. There are
`s-f=q/2` such vertices per class, an even number.

The vertex count is `3+3s+s²+2f+3=q²`. Each selected class vertex has
outside degree s+1 and one root neighbor. Each unselected class vertex has
outside degree s, one root neighbor and one matching neighbor. Thus all
roots and class vertices have degree q. Every outside vertex has degree
zero, two, or three; no outside-outside edges are added.

The partial graph is C4-free. Two different Latin triples share at most
one entry; replacing a triple by its three pairs preserves this property.
Each outside vertex meets each class at most once. Within a class, the
only edges form a matching, and between classes there are no edges.
These facts also exclude a second common neighbor for any pair involving
a root or class vertex. The triangles through ui are precisely the root
triangle and those formed with the matching inside Ci. Consequently

```text
t_ui = 1 + (s-f)/2 = q/4+1,
t_u0+t_u1+t_u2 = 3q/4+3 < q+1.
```

An exact q=16 construction checked all 32,640 unordered vertex pairs for
codegree at most one and all 45 root/class degrees for equality to 16.
Its degree counts are `{16:45, 2:18, 3:190, 0:3}` and its three root
triangle degrees are `(5,5,5)`, giving 15 rather than the proposed 17.
This is a direct construction check, not an enumeration of candidate graphs.

Therefore a proof of the proposed triangle-sum identity T2 must use more
than C4-freeness, square order, and saturation of the entire triangle
neighborhood. The outside degree equations and their global compatibility
are absent here. No completion is claimed or searched for; the weaker
weighted-neighbor terminal At=((q²+2)/3)1 remains a separate open target.

## A uniform triangle-edge bound from branch parity

Follow-up, 2026-09-06, Sol3. Here G is an actual q-regular C4-free graph
on q² vertices, with q even. If ua belongs to a triangle, then

```text
t_u + t_a >= q/2 + 1.                                  (P)
```

To prove this, write the triangle as uab. For each z in N(u), put
`S_z=N(z) minus N[u]`. These branches are pairwise disjoint. Together
with u, N(u), and the set F of vertices at distance at least three from
u, they partition the vertices. The radius-two count gives
`|F|=2t_u-1`. The branch S_a has q-2 vertices and induces a matching.

Let U consist of its internally unmatched vertices. A vertex x in U
has exactly one neighbor in N(u), namely a; none in S_a by definition;
none in S_b because an edge xy with y in S_b would form the C4 axyb;
and at most one in each other S_z, because two would have common
neighbors x and z. There are q-2 other branches. Thus x has at most
q-1 neighbors outside F and must have a neighbor in F. Conversely a
vertex of F has at most one neighbor in S_a, again by C4-freeness.
Counting edges from U to F yields `|U|<=|F|=2t_u-1`.

Since q-2 is even and S_a induces a matching, |U| is even. Hence
`|U|<=2t_u-2`. All triangles through a consist of uab and the internal
matching edges of S_a: no vertex of S_a can be adjacent to u or b.
Consequently

```text
t_a = 1 + (q-2-|U|)/2 >= q/2+1-t_u,
```

proving (P). No connectedness assumption on the defect graph is used.
Summing (P) over a triangle gives `4 sum_triangle t >= 3q+6`.
If t_u=1, both of its triangle-neighbors have t=q/2, so T2 holds on
that triangle. For general triangles this is only a lower bound, not
the proposed equality `sum_triangle t=q+1`. It does not give T1 or the
weighted-neighbor terminal, nor propagate triangle counts along the
distance-three relation. The existing partial control above is consistent
with (P): its root-edge sums are q/2+2. This bounded parity check stops
without another formalization or a claim that A-REG is closed.

For binary q>=8, the residual triangles with all three counts at least
two must actually occur, as observed by Sol2. Otherwise every triangle
has exactly one vertex of count 1 and two of count q/2. Every vertex
belongs to some triangle since `|F|=2t-1>=0`. If there are T triangles,
L low vertices and H high vertices, incidence counting gives
`L=T` and `(q/2)H=2T`. Therefore `q³=(q+4)T`. But
`q+4=4(2^(k-2)+1)` has an odd divisor greater than one for k>=3, and
cannot divide the power of two q³. Thus the t=1 case cannot cover all
triangles in a hypothetical binary candidate. This locates a necessary
residual; it is not an exclusion of that residual.

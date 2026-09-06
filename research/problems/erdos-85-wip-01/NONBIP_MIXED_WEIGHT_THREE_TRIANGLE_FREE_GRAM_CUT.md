# Triangle-free weight-three internal Gram model

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-3,3]`.

Status: explicit countermodel to an internal-only obstruction. Uniform
internal construction for even `q>=8`; full small-shore Gram construction
at `q=16`. No exterior completion or Lean theorem is claimed.

## The proposed obstruction and its failure

The short-cycle reduction makes a triangle or induced C5 exhaustive on a
nonbipartite weight-three component. The triangle-free alternative still
survives all of the following simultaneously: connected regular defect,
cubic self-indexed internal adjacency, exact commutation, internal C4 cap,
and disjoint internal neighborhoods across every defect edge.

Let `C=Z/(3q)`, with q even and at least 8. Define

```text
D(x,y) iff q < (y-x mod 3q) < 2q,
H(x,y) iff x+y belongs to {1,3,7} modulo 3q.
```

The defect D is symmetric, loopless, and `(q-1)`-regular. Its step interval
is sum-free modulo `3q`, so D is triangle-free. The two consecutive steps
`q+1,q+2` generate the cyclic group, so it is connected. It contains the
five-cycle

```text
0, q+1, 2q+2, 3, q+4, 0.
```

The successive step residues lie in the defining interval; the vertices
are distinct. Triangle-freeness makes this C5 induced and proves D is
nonbipartite.

H is a sum of three reflections with odd parameters. Each reflection has
no fixed point because `3q` is even; the three neighbors are distinct.
Every reflection commutes with a symmetric circulant, so `HD=DH`.
Composing two reflections shows

```text
H^2 = 3I + K,
K(x,y)=1 iff y-x belongs to {+/-2,+/-4,+/-6} mod 3q.
```

All six residues are distinct and outside the D step interval. Thus H is
C4-free and its neighborhoods are disjoint across every D-edge. This is
an explicit uniform model, not a conclusion inferred from sampled SAT.

## Full small-shore Gram at q=16

On `C=Z/48`, the complement of D has differences `+/-1,...,+/-16`.
The pairs accounted for by H neighborhoods have differences `+/-2,4,6`.
Partition all remaining positive differences below 16 into

```text
(7,8,15), (5,9,14), (3,10,13), (1,11,12),
```

each of the form `(a,b,c)` with `a+b=c`. For each triple take all 48
translates of the block `{0,a,c}`. These four orbits partition the edges
of their twelve difference classes into triangles. Finally take the 16
blocks `{x,x+16,x+32}`, `0<=x<16`, which partition the difference-16
edges. This gives `4*48+16=208=q(q-3)` distinct blocks.

Let F index these blocks and B be their unsigned point-block incidence.
Every column has size 3; every row has size 13. Every distinct point pair
is covered once unless it is a D-edge or already covered by H^2.
Consequently, entry by entry,

```text
H^2 + BB^T = 15I + J - D.
```

The partial ambient adjacency `[H B; B^T 0]` is C4-free on 256 vertices.
For pairs within C this follows from the displayed Gram. Within F it
follows from distinct blocks intersecting in at most one point. A C-point
and an F-point cannot have two common neighbors: two points of the block
would then share an H-neighbor, but the block difference classes exclude
every off-diagonal position of H^2. Its degree distribution is
`{3:208, 16:48}`.

The standard-library checker reconstructs all objects, verifies D's
connectivity and induced C5, every entry of HD=DH and the C Gram, and all
32,640 pairs of vertices in the partial graph. Run:

```sh
python3 research/problems/erdos-85-wip-01/check_weight_three_triangle_free_gram.py
```

## Scope and stopping point

This cuts an exclusion derived only from the listed internal hypotheses,
even when supplemented by the full C Gram and a C4-free partial ambient
realization. The 208 exterior vertices still need 13 neighbors each.
No symmetric exterior T satisfying `HB+BT=J` is supplied; neither the
exterior Gram equation nor a connected regular D_F is supplied. In this
partial graph C is not asserted to be an actual defect component of a
regular ambient graph. The uniform H,D construction is stronger in q
than the B construction, which is asserted only at q16.

The internal-only obstruction is therefore stopped. A successful argument
must couple this data to the same exterior labels via the cross equation,
the exterior Gram, and the required connected defect component. No
order-64 enumeration or search was used.

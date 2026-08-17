# A-REG: orthogonality of two size-two owner coordinates

Status: exact consequence of OWNER-CROSS plus the proved size-two selector
model, 2026-08-17.  This retains cross-coordinate incidence information that
is invisible to the ordinary owner spectra and triangle inventory.

## Setup

Let `c != d` be defect components with normalized orders
`m_c=m_d=2`.  Each component has `2q` vertices.  Put

```text
H_c = complement(D_c),       H_d = complement(D_d).
```

Each `H` is `q`-regular on `2q` vertices, hence has `q^2` edges.  The
size-two selector equivalence identifies the ambient vertex set `V` with
`E(H_c)` and also with `E(H_d)`.  Let `B_c,B_d` be the corresponding
unsigned vertex-edge incidence matrices; thus each column has two ones and

```text
B_c^T B_c = O_c + 2I = M_c,
B_d^T B_d = O_d + 2I = M_d.
```

OWNER-CROSS says

```text
B_c^T (B_c B_d^T) B_d = M_c M_d = 4J.              (1)
```

Write `R=B_c B_d^T`.  Its entry `R(a,b)` is the number of ambient labels
whose `c`-edge is incident with `a` and whose `d`-edge is incident with `b`.
Every row and column of `R` sums to `2q`.

## Rectangle equation

Evaluating (1) at a `c`-edge `aa'` and a `d`-edge `bb'` gives

```text
R(a,b)+R(a,b')+R(a',b)+R(a',b') = 4.                (2)
```

Fix an edge `aa'` of `H_c` and define
`s(b)=R(a,b)+R(a',b)`.  Equation (2) says

```text
s(b)+s(b')=4                    for every bb' in E(H_d).   (3)
```

The graph `H_d` is connected and nonbipartite.  Connectedness follows because
every component of a simple `q`-regular graph has at least `q+1` vertices, so
two components would require more than `2q` vertices.  A bipartite
`q`-regular graph on
`2q` vertices has two parts of size `q` and must be `K_{q,q}`.  Its complement
is then `K_q disjoint_union K_q`, contradicting connectedness of the defect
component `D_d`.

Along an odd cycle, (3) forces `s=2`; connectedness of `H_d` then propagates
this to every vertex.  Therefore for every edge `aa'` of `H_c`,

```text
R(a,-)+R(a',-)=2 * 1.                               (4)
```

Apply the same argument in the other coordinate (or fix a column and use an
odd cycle in `H_c`).  For every edge `bb'` of `H_d`,

```text
R(-,b)+R(-,b')=2 * 1.                               (5)
```

Now (4) along an odd cycle of `H_c` forces every row of `R` to be the all-ones
row.  Hence the cross-incidence matrix is rigid:

```text
                         B_c B_d^T = J.              (ORTH)
```

Equivalently, every vertex-star of `H_c` and every vertex-star of `H_d`
contain exactly one common ambient label.

## Rectangle decomposition and one-factor system

Each ambient label `x` determines an edge `e_c(x)` of `H_c` and an edge
`e_d(x)` of `H_d`.  ORTH says that the `q^2` rectangles

```text
e_c(x) times e_d(x)  subset V(H_c) times V(H_d)
```

partition the complete bipartite graph `K_{2q,2q}`: every ordered cross-pair
of vertices occurs in exactly one rectangle.

Fix `a in V(H_c)`.  The `q` labels incident with `a` have pairwise disjoint
`d`-edges (owner colors are edge-disjoint), while ORTH says that these edges
cover every vertex of `H_d` exactly once.  Thus they form a perfect matching
`F_a` of `H_d`.  Consequently `H_d` carries `2q` distinguished perfect
matchings satisfying

```text
|F_a intersect F_a'| = 1  if aa' is an edge of H_c,
|F_a intersect F_a'| = 0  otherwise,
```

and every edge of `H_d` lies in exactly two of the matchings.  The same holds
with `c,d` exchanged.

This is substantially sharper than the line-graph identity for one owner:
two size-two coordinates require mutually orthogonal edge-incidence
structures, or equivalently a rectangle decomposition with compatible
one-factor systems.  A terminal can now attack this finite combinatorial
object directly.  In particular, for `q=8` the all-size-two partition would
require four pairwise orthogonal systems of this kind.

## Next tests

1. Classify or rule out the rectangle decomposition for even prime-power
   `q` under the additional requirement that both complements `D_c,D_d` are
   connected `(q-1)`-regular defect graphs.
2. Use the `2q` one-factors as binary incidence vectors.  Their Gram matrix
   is `qI+A(H_c)` over the integers and `A(H_c)` over `F_2`; combine this with
   the fact that every edge of `H_d` occurs twice.
3. For the `q=8`, `2+2+2+2` sector, search at the rectangle/one-factor level
   rather than at the original 64-vertex graph level.

## Decisive audit: the pairwise object exists at `q=8`

The pairwise rectangle system alone is **not** a terminal.  There is an
explicit translation construction at `q=8`.  Identify the `16` vertices with
`F_2^4` (written as integers `0,...,15` under bitwise xor), and take the base
perfect matching

```text
P = {(4,12), (5,7), (15,8), (9,2),
     (0,1),  (3,10), (6,11), (13,14)}.
```

Its eight edge differences are distinct:

```text
S = {1,2,3,7,8,9,11,13}.
```

Let `H=K=Cay(F_2^4,S)` and, for every `a in F_2^4`, let `F_a=P+a` be the
translated perfect matching.  Every edge of `K` occurs in exactly two of the
`F_a`.  Distinct translated matchings satisfy

```text
|F_a intersect F_b| = 1  iff  a+b in S,
|F_a intersect F_b| = 0  otherwise.
```

Indeed, translation by `t` can carry a base edge to a base edge only when
their differences agree.  The differences in `P` are unique, so for
`t in S` the unique edge of difference `t` is fixed setwise, and no other
edge is shared.

The set `S` spans `F_2^4`, so the Cayley graph is connected.  It is
nonbipartite: there is no nonzero linear functional taking the value `1` on
every element of `S` (already `1,2,3 in S` contradict linearity, since
`3=1+2`).  Thus this construction meets even the connected/nonbipartite
conditions inherited from a defect-component complement.

Consequently ORTH is valuable structural compression, but a proof must use
compatibility among **three or more** coordinates, or another property of the
ambient graph not encoded by a single pair of owner incidence systems.  For
the `2+2+2+2` sector the correct next question is whether four such systems
can coexist with the same ambient adjacency/defect square identity; pairwise
nonexistence is false.

### First triple-compatibility scout

The displayed translation pair was tested for extension by a third size-two
coordinate.  A vertex-star of the third coordinate would have to be a set of
eight labels that is simultaneously a perfect matching in both copies of
`H`.  Direct backtracking finds exactly `64` such common perfect matchings.

Introduce one binary variable for each of these `64` matchings.  A third
coordinate requires:

```text
each of the 64 labels occurs in exactly two selected matchings;
two selected matchings share at most one label.
```

The first condition alone is feasible (with `16` selected matchings).  Adding
the second condition makes the `64`-variable integer system infeasible
(checked with SciPy/HiGHS).  The second condition is essential: if two stars
shared two labels, the third owner graph would have a multiple edge rather
than being simple.  Thus this explicit pair cannot extend even to three
size-two coordinates.

This is a scout, not a general proof or a checked certificate.  Its value is
that it isolates the likely terminal statement: prove that any two ORTH
coordinates force a collision in every twofold cover by common perfect
matchings.  Such a theorem would kill every partition containing at least
three size-two parts, including the `2+2+2+2` sector at `q=8`, without
returning to the 64-vertex ambient graph.

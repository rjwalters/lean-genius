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

The graph `H_d` is connected enough for this equation in the following
precise sense: it is not bipartite.  Indeed, a bipartite `q`-regular graph on
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


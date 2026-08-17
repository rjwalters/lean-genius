# A-REG: three size-two owners as incidence cubes

Status: exact reformulation of pairwise ORTH for three normalized size-two
defect components, 2026-08-17.

Let `X_1,X_2,X_3` be three sets of size `2q`.  An ambient label `v` determines
an edge

```text
e_i(v) in choose(X_i,2)
```

for each owner coordinate `i`.  The pairwise identity `B_i B_j^T=J` says
that, for every `i != j`, the rectangles

```text
e_i(v) times e_j(v)       (v in V, |V|=q^2)
```

partition `X_i times X_j`.

## Cube form

Attach to `v` the eight-point cube

```text
C_v = e_1(v) times e_2(v) times e_3(v)
      subset X_1 times X_2 times X_3.
```

The cubes are not required to partition the three-dimensional product: they
contain `8q^2` triples, while the product has `8q^3` triples.  Their decisive
property is instead that every two-dimensional projection is a partition:

```text
{proj_ij(C_v) : v in V} partitions X_i times X_j.       (CUBE-PROJ)
```

Equivalently, define the `0/1` tensor

```text
T(a,b,c) = 1 iff (a,b,c) belongs to some C_v.
```

Pairwise projection uniqueness makes the cubes disjoint: if two cubes shared
a triple, they would share its `(a,b)` projection.  Therefore `T` is indeed
`0/1`.  Every axis-parallel line has sum exactly two.  For example, fixing
`(a,b)` selects its unique label `v`; precisely the two endpoints of `e_3(v)`
complete that pair to a point of `T`.  Thus

```text
sum_c T(a,b,c) = sum_b T(a,b,c) = sum_a T(a,b,c) = 2.   (LINE-2)
```

Conversely, CUBE-PROJ is stronger than LINE-2 alone because the support must
split into `q^2` Cartesian `2x2x2` cubes.  This Cartesian decomposition is
the exact three-owner selector datum.

## Owner simplicity inside each coordinate

For fixed `i`, the `q^2` pairs `e_i(v)` form the edges of a simple
`q`-regular graph `H_i` on `2q` vertices.  Simplicity means no pair is
repeated.  Connectedness and nonbipartiteness follow as in the two-owner
analysis from connectedness of the complementary defect component.

Fixing `a in X_1`, the `q` labels with `a in e_1(v)` project to perfect
matchings of both `H_2` and `H_3`, with the *same label pairing*.  Hence a
third coordinate is not merely a common twofold cover: each selected common
perfect matching is one slice of a single Cartesian cube decomposition.

## Binary formulation

Reducing the tensor modulo two, LINE-2 says every line has parity zero.  Thus
`T` lies in the tensor product of the even-weight subspaces:

```text
T in E(X_1) tensor E(X_2) tensor E(X_3),
E(X) = {f : X -> F_2 | sum_x f(x)=0}.
```

The additional cube decomposition writes it over `F_2` as

```text
T = sum_v 1_{e_1(v)} tensor 1_{e_2(v)} tensor 1_{e_3(v)}.
```

Each factor has weight two.  This is the natural setting for a cubic parity
invariant: ordinary pairwise Gram identities see only contractions of `T`
and therefore cannot distinguish the realizable pair from a nonextendable
triple.

## Precise terminal candidates

1. Prove that no CUBE-PROJ decomposition exists when all three edge graphs
   are connected nonbipartite `q`-regular graphs and `q` is a power of two.
   The explicit pairwise construction shows that two projections alone are
   insufficient.
2. If the blanket statement is false, identify the extra identity imposed by
   the common ambient adjacency matrix `A`; CUBE-PROJ currently remembers the
   selector systems but not all incidences of `G`.
3. Search `q=8` directly at the cube level.  Variables are candidate common
   perfect matchings/cubes, many orders of magnitude fewer than arbitrary
   64-vertex graphs.


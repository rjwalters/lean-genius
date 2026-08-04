# Nonneighbor reduction checkpoint

The Boza-style closed-neighborhood deletion has now been formalized in
`Proofs/Erdos85NonneighborReduction.lean`.

For a `C₄`-free graph `G` and vertex `x`, let

```text
S = V(G) \ ({x} ∪ N(x)).
```

Every vertex of `S` loses at most one neighbor in `G[S]`.  Indeed, every lost
neighbor other than `x` is a common neighbor with `x`, while `x` itself is not
adjacent to a surviving vertex; two such common neighbors would form a
four-cycle.  The Lean development proves:

- the degree-loss bound `degree_G(y) ≤ degree_G[S](y) + 1`;
- inheritance of `C₄`-freeness by `G[S]`;
- the exact order `|S| = |V(G)| - degree_G(x) - 1`;
- transport of `G[S]` to a `C4FreeMinDegreeWitness` on a `Fin` type.

Applying this to an exact top witness and a minimum-degree vertex gives the
recursive witness statement

```text
C4FreeMinDegreeWitness (n - f(n)) (f(n) - 2).
```

Consequently, whenever `4 ≤ n - f(n)`, the checked threshold inequality is

```text
f(n) - 2 < f(n - f(n)).
```

This is a genuine recursive restriction on the witness spectrum, but it does
not by itself prove eventual monotonicity.  The next direction is to iterate
the reduction and to determine whether edge-minimal/layered witnesses force a
strictly better loss or a useful compatibility condition between successive
reduced witnesses.

## Iterated reduction

The reduction has since been iterated formally.  After every step the witness
is normalized back to exact minimum degree before a new tight vertex is chosen.
If the starting certified degree is `d`, the successive closed neighborhoods
have sizes `d+1, d, d-1, ...`.  Intermediate order assumptions are automatic
while the surviving certified degree is at least three.

Reducing all the way to degree three and using the checked fact that a
degree-three witness needs at least ten vertices gives

```text
C(d + 2, 2) ≤ n
```

for every `C₄`-free minimum-degree-`d` witness with `d ≥ 3`.  In particular the
result gives the sharp minimum orders 10 and 15 for certified degrees 3 and 4,
and the preliminary lower bound 21 for degree 5.  Equality at degree 5 would
force a 5-regular graph on 21 vertices, which the handshake parity excludes;
the checked degree-5 lower bound is therefore 22.  Combining the general bound
with the classical common-neighbor count yields

```text
max(C(d + 2, 2), d(d - 1) + 1) ≤ n.
```

The first term improves the usual count for degrees three and four, agrees at
degree five, and is weaker thereafter.  It is therefore a useful sharpened
low-degree obstruction and a general witness-spectrum normal form, but still
does not settle eventual monotonicity.

## Equality rigidity

The vertex-sensitive version of the reduction gives

```text
degree(x) + 1 + C(d + 1, 2) ≤ n
```

for every vertex of an exact minimum-degree-`d` witness, `d ≥ 4`.  Hence a
witness attaining the triangular order `n = C(d + 2, 2)` must be `d`-regular.
Moreover, deleting the closed neighborhood of any vertex then produces a
degree-`d-1` witness on exactly `C(d + 1, 2)` vertices.

Finally, the classical count strictly exceeds the triangular bound for
`d ≥ 6`.  Thus triangular equality can occur only for `d ≤ 5`; parity excludes
the degree-five order 21, leaving degree four/order 15 as the last nontrivial
equality case not excluded by these arguments.

## Distance layers and the repair obstruction

The canonical repair criterion has been factored through explicit candidate
reservoirs.  Its external reservoir consists of vertices at distance at least
three from the deleted vertex.  In a `d`-regular `C₄`-free graph, the
second-neighbor branches are pairwise disjoint and each has at least `d-2`
vertices, giving

```text
|external candidates at x| + d(d-1) + 1 ≤ n.
```

A repair set needs `d-1` candidates and may use at most one from `N(x)`.  If it
uses such an internal candidate, that neighbor has no edge inside `N(x)`, so
its second-layer branch gains one vertex.  This exactly cancels the internal
allowance and yields the necessary condition

```text
HasRepairSet G d  →  d² ≤ |V(G)|
```

for regular witnesses.  Hence every regular witness below `d²` fails the
canonical delete-one/add-pair surgery.  In particular, every 4-regular
`C₄`-free graph on 15 vertices has no `HasRepairSet`, uniformly explaining the
order-15 computational stress-test failure.  Eventual monotonicity will need
either nonregular witnesses or a genuinely broader surgery in this regime.

## Degree-compensated paired surgery

The paired-attachment construction has now been generalized in two stages.
First, the survivor graph may be replaced by an arbitrary spanning subgraph
before the adjacent pair is attached.  The exact sufficient condition at an
old vertex `v` is

```text
d ≤ degree_after_deletions(v) + 1[v ∈ S] + 1[v ∈ T].
```

Second, there is a concrete version which deletes every edge crossing between
the two attachment sets `S,T`.  This makes cross-compatibility automatic while
preserving the two within-set safety conditions.  The formal quantity
`crossEdgeLoss H S T v` counts precisely the incident edges removed at `v`,
and Lean checks the exact identity

```text
degree_H(v) = degree_after_cross_deletion(v) + crossEdgeLoss(H,S,T,v).
```

For `v ∈ S \ T`, this loss is `|N(v) ∩ T|`; for `v ∈ T \ S`, it is
`|N(v) ∩ S|`; and outside both sets it is zero.  Thus the checkable budget is

```text
d + crossEdgeLoss(H,S,T,v)
  ≤ degree_H(v) + 1[v ∈ S] + 1[v ∈ T].
```

The property `HasCompensatedCrossRepair G d` packages the existence of a
deleted vertex and two safe sets satisfying these size, intersection, and
loss inequalities.  A uniform proof of this property implies
`C4FreeWitnessExtension n`, so it is now a precise broader target for the
eventual-monotonicity argument.

This surgery is strictly more flexible at vertices with degree slack: a
vertex in one attachment set can pay for one deleted cross edge using its new
incident edge, and additional old-degree slack can pay for further losses.
In an exactly `d`-regular witness, however, a neighbor of the deleted vertex
starts at degree `d-1`, so a single attachment merely repairs that original
defect and cannot also pay for a cross-edge deletion.  Consequently the hard
regular case still requires a carefully arranged covering of the deleted
neighborhood (or a still broader local switch); arbitrary cross-edge deletion
alone does not erase the order-15 obstruction.

Commits: `22d1b67541`, `d7129b8e31`, `9d36eaf269`, `361d6606b7`,
`c1b828e493`, `2bcb1c2ef4`, `8f5f13e696`, `03397138eb`, `1e66a25d51`,
`a3227cd3e2`, `d204a06c79`, `3c5c7c3f81`, `f8cffd864a`, `be7fcbf754`,
`e90b783a5f`, `f52aaf1305`.

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
result gives the sharp minimum orders 10, 15, and 21 for certified degrees 3,
4, and 5.  Combining it with the classical common-neighbor count yields

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
`d ≥ 6`.  Thus triangular equality can occur only for `d ≤ 5`; the nontrivial
regular equality cases are precisely reduced to degrees four and five, at the
sharp orders 15 and 21.

Commits: `22d1b67541`, `d7129b8e31`, `9d36eaf269`, `361d6606b7`,
`c1b828e493`, `2bcb1c2ef4`, `8f5f13e696`.

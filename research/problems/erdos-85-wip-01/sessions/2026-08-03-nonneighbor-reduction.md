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

Commits: `22d1b67541`, `d7129b8e31`.

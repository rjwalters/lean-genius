# q=9 Petersen^8 quotient reduction

This is the first stage of the exhaustive disconnected-shadow classification
for a shadow consisting of eight Petersen components.

Let `T` be the triangular color. Because each Petersen component has diameter
two, the C4-free common-neighbor law makes every bipartite `T` graph between
two components a matching. Every vertex therefore has its six `T` neighbors
in six distinct other components and omits exactly one of the remaining
seven components.

The 80 `T` triangles induce a weighted 3-uniform hypergraph on the eight
components. Its weights satisfy:

- total weight 80;
- vertex degree 30 at every component;
- pair codegree at most 10.

For a vertex-transitive full graph, the component action is one of GAP's 50
transitive groups of degree eight. Moreover, the omitted-component map is
equivariant. Its support must therefore be one directed-pair orbital, with a
constant nonzero fiber size. Since matching sizes are symmetric, the orbital
is self-paired; its outdegree divides the ten vertices in a Petersen block.

[`q9_petersen8_quotient_patterns.py`](q9_petersen8_quotient_patterns.py)
enumerates every invariant nonnegative integer triple-weight vector and
checks this omission-orbital condition. The result is exact:

- 19 of 50 component actions already fail the elementary triple-weight
  equations;
- another 20 fail the equivariant omission-orbital condition;
- exactly 11 actions survive: transitive-group ordinals
  `1,2,4,5,6,7,8,11,12,15,23`.

Thus a direct subgroup census inside `Aut(Petersen) wr S8` is unnecessary and
infeasible; the lift stage only needs these eleven quotient actions and the
finite pattern lists pinned by their SHA-256 digests in the verifier output.

Run with:

```text
python3 research/problems/erdos-85-wip-01/q9_petersen8_quotient_patterns.py
```

Dependencies used for the recorded run: GAP 4.15.1 from
`gapsystem/gap-docker`, and `z3-solver` 4.15.3.

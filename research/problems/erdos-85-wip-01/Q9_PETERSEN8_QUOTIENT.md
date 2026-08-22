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

The verifier also exhausts all 2,880 perfect matchings between two Petersen
blocks which send Petersen edges to nonedges. They form one orbit under the
two block automorphism groups. For three mutually perfect block matchings,
the attainable triangle multiplicities are exactly `0,1,2,3,4,5,6` (with
the full frequency table pinned in the output), never `7,8,9,10`. Applying
this local lift obstruction reduces the surviving quotient list from 432 to
324 patterns, without changing the eleven surviving component actions.

Every one of those 324 patterns has omission outdegree one: the components
are partitioned into four pairs with no `T` edges inside a pair, and all
other component pairs carry perfect size-ten matchings. Equivalently, the
component support is `K_{2,2,2,2}`. The verifier additionally checks the
vertex-local lift condition: around each vertex, the other six components
must be paired into the three incident triangles, one of the eight perfect
matchings of `K_{2,2,2}`; each component multiplicity vector must be a sum of
ten such local types. All 324 patterns pass this necessary factorization, so
the next exclusion must use compatibility among the perfect Petersen
anti-matchings, not another component-count identity.

The initial Z3 model in
[`q9_petersen8_perfect_matching_lift.py`](q9_petersen8_perfect_matching_lift.py)
records the exact lift constraints but is too slow to serve as the final
certificate.  The direct CNF encoding in
[`q9_petersen8_kissat_lift.py`](q9_petersen8_kissat_lift.py) instead uses a
10-by-10 Boolean permutation matrix on each of the 24 supported component
pairs.  It enforces row and column uniqueness, the Petersen
edge-to-nonedge condition, functional triangle composition, the selected
quotient multiplicities, and uniqueness of the triangle containing every
matching edge.  The same lossless spanning-tree gauge fixes a root edge and
restricts every subsequent tree edge to 24 target-automorphism
representatives.

There are only 19 quotient patterns up to arbitrary relabeling of the eight
components.  Twelve are UNSAT already in the lift model without imposing a
component action.  For each of the remaining seven geometric patterns, the
lifted generators of the transitive component action must act inside every
Petersen block by a Petersen automorphism and conjugate every matching
correctly.  Quotienting the remaining action-pattern pairs by the normalizer
of each of the eleven surviving transitive groups leaves 39 representatives.
All 39 are UNSAT with these necessary lifted-action constraints.  Thus the
12 base representatives plus 39 action representatives exclude all 324
action-pattern pairs.  Every solve is UNSAT before any lazy C4 cut is added:
the matching, triangle, and vertex-transitivity constraints alone are
inconsistent.

[`q9_petersen8_exhaustive_lift.py`](q9_petersen8_exhaustive_lift.py) audits
both reductions rather than trusting the representative lists: it rebuilds
all 324 patterns, canonicalizes them to 19 geometric classes, computes the
normalizer of every surviving transitive group inside `S8`, and asserts that
the seven hard geometric classes split into exactly the pinned 39 action
classes.  With `--verify`, it reruns all 51 UNSAT representatives and prints
`excluded_petersen8_action_patterns 324` only after every solver result has
been checked.

Run with:

```text
python3 research/problems/erdos-85-wip-01/q9_petersen8_quotient_patterns.py
python3 research/problems/erdos-85-wip-01/q9_petersen8_exhaustive_lift.py
python3 research/problems/erdos-85-wip-01/q9_petersen8_exhaustive_lift.py --verify --workers 2
```

Dependencies used for the recorded runs: GAP 4.15.1 from
`gapsystem/gap-docker`, `z3-solver` 4.15.3 for the specification model, and
Kissat 4.0.4 for the exhaustive CNF suite.

# A-REG defect vertex-cut audit

## Setting

Let `A` be a loopless symmetric `q`-regular `C4`-free graph on `q^2`
vertices, with even `q >= 8`, and let

```text
D = (q - 1) I + J - A^2.
```

Assume that `D` is connected.  The cut-variance theorem gives, for a shore
`S` of order `s = q a + r`, `0 <= r < q`,

```text
|delta_D(S)| >= r(q-r).
```

It also proves that `D` has no one- or two-edge cut.  In particular, a
nontrivial `q`-divisible shore has boundary at least four.

## No articulation vertex

Suppose that deleting a vertex `w` leaves components `S_1,...,S_k`, with
`k >= 2`.  Their `D`-boundaries are disjoint subsets of the `q-1` edges at
`w`, so

```text
sum_i |delta_D(S_i)| <= q - 1.                 (1)
```

Write `|S_i| = q a_i + r_i`.  Since their orders sum to `q^2-1`, the residues
sum to `-1` modulo `q`.  If all but one residue vanish, the nonzero residue is
`q-1`; its cut already has size at least `q-1`, while every zero-residue
component contributes at least four.  If at least two residues are nonzero,
the sum of the bounds `r_i(q-r_i)` is strictly greater than `q-1` (the
minimum split of residue `q-1` starts with `1` and `q-2`, giving
`(q-1)+2(q-2)`).  Adding further positive residues or a full extra `q` to the
residue sum cannot lower the total to `q-1`.  Both cases contradict (1).

Thus connected `D` has no articulation vertex: its vertex connectivity is at
least two.

## Exact two-vertex-separator escape

The same argument does not prove three-connectivity.  If deleting
`W = {x,y}` leaves at least two components, their boundaries total at most
`2(q-1)`.  The residue bounds leave one sharp possibility:

- there are exactly two components `S_1,S_2`;
- `|S_i| = q a_i - 1`, with `a_1+a_2=q`;
- both cuts have size exactly `q-1`;
- every `D`-edge at `x` or `y` enters one of the two components, so `xy` is
  not a `D`-edge.

(The restriction `q >= 8` matters to this uniqueness statement; the small
`q = 4` residue optimization has an additional `(1,1)` equality pattern.)

Cut-variance equality gives a `q`-set `Z_i` for each component such that

```text
deg_A(v,S_i) = a_i - 1_Z_i(v).
```

Because `S_1,S_2,W` partition the vertices, pointwise degree addition yields

```text
1_Z1(v) + 1_Z2(v) = deg_A(v,W)
                         = 1_NA(x)(v) + 1_NA(y)(v).       (2)
```

Consequently the two low sets have the same union, intersection, and
symmetric difference as `N_A(x),N_A(y)`.  Since `xy` is not a `D`-edge,
`x,y` have their unique permitted common `A`-neighbor, so both pairs of
`q`-sets meet in one point.

Put

```text
P = N_A(x) \ N_A(y),   Q = N_A(y) \ N_A(x),
p = |P intersect Z_1|.
```

Then (2) only says that `Z_1` selects `q-1` points from the disjoint union
`P union Q`, and direct use of `D = (q-1)I+J-A^2` gives

```text
deg_D(x,S_1) = p,              deg_D(y,S_1) = q-1-p,
deg_D(x,S_2) = q-1-p,          deg_D(y,S_2) = p.
```

Every value `0 <= p <= q-1` satisfies all scalar cut, equality, and pair
codegree constraints.  Hence the cut theorem proves two-connectivity but
does not exclude a two-vertex separator.  A proof of three-connectivity would
need location information that distinguishes how the two low sets split the
two punctured neighborhoods.

There is an exact C4-free description of that remaining location problem.
All vertices in `N_A(x)` already have the common neighbor `x`, so their
neighborhoods outside `x` are pairwise disjoint.  Restricting these fibers to
`S_1` and using the equality degree pattern gives

```text
sum_{u in N_A(x)} |N_A(u) intersect S_1| = |S_1| - p.
```

The uncovered points are exactly `N_D(x) intersect S_1`, whose cardinality
is `p`.  The `y`-fibers give a second punctured parallel class on the same
shore, missing exactly `N_D(y) intersect S_1`, of size `q-1-p`.  The same
description holds with `S_1,S_2` interchanged.  Cross-fibers from the two
classes may meet once, so C4-freeness supplies no contradiction for an
intermediate value of `p`; it converts the escape into two compatible partial
resolutions.

This interface has an abstract control for every `a_i` and `p`.  On the
`q x q` grid of pairs of `x`- and `y`-fibers, take a simple
`(a_i-1)`-regular bipartite graph (cyclic shifts give one), representing the
`q(a_i-1)` shore points covered by both classes.  Add `q-1-p` points covered
only by distinct `x`-fibers and `p` points covered only by distinct
`y`-fibers.  The result has `q a_i-1` points, the required near-constant cell
sizes on both sides, and every cross-cell intersection at most one.  Thus all
pair-capacity consequences of C4-freeness are compatible with every value of
`p`; any exclusion must restore how these abstract cells are located at their
own vertices in the original graph.

## Status

- **Proved mathematically here:** connected `D` has no articulation vertex.
- **Exact unresolved boundary:** the paired minimum-cut configuration above.
- **Location interface:** two cross-intersecting punctured parallel classes
  whose omission sizes are `p` and `q-1-p`.
- **Not claimed:** a Lean theorem or three-vertex-connectivity.

# Compensated surgery: the generic matching reduction

## Scope

This note records the surviving `k = 1`, empty-gadget branch of Science Card
#15.  It is a Goal #7 mechanism audit, not an order-64 computation and not a
proof of plateau compression.  The source graph is a finite simple
`d`-regular `C4`-free graph `G`, `x` is the old vertex to be deleted, and `d`
is positive and even.

The tight proposed surgery deletes `x`, deletes a matching `M` of `d / 2`
survivor edges, and adds two nonadjacent vertices with selectors of size `d`.
The pointwise degree equations and the exact compatibility reduction are
recorded on Science Card #15.  The new observation here is that the existence
of a correctly sized matching is not a scaling obstruction.

## Distance-two reservoir lemma

Put

```text
X = V(G) \ ({x} union N_G(x)).
```

For every `v in X`,

```text
deg_{G[X]}(v) >= d - 1.
```

Indeed, `v` is not adjacent to `x`.  It has at most one neighbour in
`N_G(x)`: two distinct such neighbours `a,b` would give the four-cycle
`x-a-v-b-x`.  Of the `d` neighbours of `v`, therefore, at least `d-1` lie in
`X`.

Consequently `G[X]` contains a matching of size at least `d / 2`.  Take any
maximal matching of size `r`.  If `r < d / 2`, its endpoint set has size
`2r <= d-2`.  Provided an unmatched vertex exists, maximality says every
neighbour of that vertex is a matched endpoint, contradicting the preceding
minimum-degree bound.  An unmatched vertex does exist in the plateau regime:
the standard lower bound

```text
|V(G)| >= d(d-1) + 3
```

gives

```text
|X| = |V(G)| - d - 1 >= (d-1)^2 + 1 > d-2 >= 2r.
```

Thus one may choose the required `d / 2` edges wholly inside `X`.  In
particular their endpoints are disjoint from `N_G(x)`; the exceptional shared
selector vertex allowed by the more general normal form is unnecessary for
the degree bookkeeping.

## Exact residual target

Choose such a matching `M`, put

```text
K = G - x - M,
S = N_G(x) union V(M).
```

The two sets in the union are disjoint and each has cardinality `d`, so
`|S| = 2d`.  Define the conflict graph `C_K[S]` by joining distinct `a,b in S`
when they have a common neighbour in `K`.  The tight compensated surgery now
exists exactly when one can choose `M` so that `C_K[S]` is bipartite with two
color classes of size `d`; the two classes are the selectors.

This formulation absorbs all degree compensation:

* every vertex of `N_G(x)` lost its edge to `x` and is selected once;
* every endpoint of `M` lost its matching edge and is selected once;
* every other old vertex loses nothing and is not selected;
* each new vertex receives exactly `d` selector edges.

Also, `N_G(x)` is an independent set in `C_K[S]`, since two neighbours of `x`
cannot retain another common neighbour in a `C4`-free graph.  Hence every
possible obstruction lies in conflicts involving `V(M)`, not inside the old
neighbourhood.

## What this does and does not settle

The generic task has therefore lost its matching-existence component.  Its
first real obstruction is the following choice theorem.

> **External-matching conflict-coloring target.**  For some matching `M` of
> size `d / 2` in `G[X]`, the graph
> `C_{G-x-M}[N_G(x) union V(M)]` is bipartite and has a balanced bipartition.

Neither high minimum degree in `G[X]` nor the raw relieved-pair budget proves
this target.  Bipartiteness can fail through an odd conflict cycle involving
matching endpoints, and even a bipartite conflict graph can have component
imbalances that cannot be flipped to total color-class sizes `d,d`.  A future
argument must control those two phenomena by choosing `M`; merely producing a
large matching, or counting available relieved pairs, is insufficient.

The `d = 4` controls in `compensated_surgery_control.py` verify that the target
can hold and that survivor-edge deletion is essential.  They do not establish
the target uniformly.

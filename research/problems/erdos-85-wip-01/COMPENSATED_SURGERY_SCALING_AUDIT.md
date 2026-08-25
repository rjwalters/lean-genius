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
particular their endpoints are disjoint from `N_G(x)`.  This proves that an
external matching is always available for the degree bookkeeping.  It does
**not** show that an external matching can satisfy compatibility: the exact
`d=4` regression below shows that the permitted one-cross-endpoint variant
can be essential.

## The restricted external-matching target

Choose such a matching `M`, put

```text
K = G - x - M,
S = N_G(x) union V(M).
```

The two sets in the union are disjoint and each has cardinality `d`, so
`|S| = 2d`.  Define the conflict graph `C_K[S]` by joining distinct `a,b in S`
when they have a common neighbour in `K`.  The tight compensated surgery with
an external matching exists exactly when one can choose `M` so that `C_K[S]`
is bipartite with two color classes of size `d`; the two classes are the
selectors.

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

The external subcase has therefore lost its matching-existence component.
Its first real obstruction would be the following choice theorem.

> **External-matching conflict-coloring target.**  For some matching `M` of
> size `d / 2` in `G[X]`, the graph
> `C_{G-x-M}[N_G(x) union V(M)]` is bipartite and has a balanced bipartition.

Neither high minimum degree in `G[X]` nor the raw relieved-pair budget proves
this target.  In fact `compensated_surgery_control.py` exhaustively refutes it
on the repository `d=4` control: a tight compensated repair exists, but none
exists when every removed survivor edge is required to lie outside
`N_G(x)`.  Every successful control repair uses a matching with exactly one
endpoint in `N_G(x)`, and that endpoint is the unique vertex shared by the
two selectors.  Thus the generic matching lemma is useful reservoir data,
not a consumer-complete reduction.  Any surviving `k=1` theorem must allow
the one-cross-endpoint form.

## A low-excess scaling obstruction

In the positive-excess band write

```text
|V(G)| = d(d-1) + 3 + e.
```

The original safe graph (the complement of the common-neighbour conflict
graph) is the second-order defect graph and is `(e+2)`-regular.  This gives a
necessary inequality for the full tight matching target.

Fix one proposed selector and put `T = A_i intersect V(M)`, `t = |T|`.  Allow
the full tight normal form `|V(M) intersect N_G(x)| <= 1`.  For a matching
endpoint `a`, write `mate(a)` for its partner in `M`.  If distinct
`a,b in T` were not already a safe pair in `G`, their unique common-neighbour
path must have been destroyed by deleting `M`.  Deletion of `x` cannot help
this pair because at most one matching endpoint lies in `N_G(x)`.  Thus
exactly one of

```text
mate(a) adjacent to b,    mate(b) adjacent to a
```

holds.  At least one holds because the pair is safe after deleting `M`; both
cannot hold because those two cross edges and the two matching edges form a
four-cycle.  Orient the pair `a -> b` in the first case.

For a fixed `c in T`, its predecessors form a clique in the original defect
graph.  Indeed, if `a -> c`, `b -> c`, and (say) `a -> b`, then `mate(a)` and
`mate(b)` have the two common neighbours `b` and `c`, again a four-cycle.
The reverse orientation is symmetric.  Consequently a pair of predecessors
must instead be an original safe pair, and

```text
indegree(c) <= e + 3.
```

There are at least

```text
choose(t,2) - t(e+2)/2
```

non-defect pairs to orient, while the sum of the indegrees is at most
`t(e+3)`.  Multiplying by two and cancelling `t` (the `t=0` case is trivial)
gives

```text
t <= 3e + 9.
```

For an external matching, the two selectors partition all `d` endpoints.  In
the one-cross-endpoint form, the exceptional endpoint belongs to both
selectors, so the two endpoint counts instead sum to `d+1`.  Applying the
bound to both selectors therefore gives `d+s <= 6e+18`, where
`s in {0,1}` is the number of matching endpoints in `N_G(x)`.  In particular
both forms obey the necessary condition

```text
d <= 6e + 18.
```

Therefore the tight `k=1`, empty-gadget matching construction is
not a uniform Goal #7 mechanism: it is impossible at fixed excess once `d`
is large, and more generally whenever `d > 6e+18`.  A uniform compensated
surgery must use selector slack, a nonmatching survivor-edge deletion graph,
or a deletion set whose size grows with `d`.  The matching lemma remains a
useful reduction, but bipartiteness is not merely a choice issue that can be
expected to hold throughout the band.

The `d = 4` controls in `compensated_surgery_control.py` verify that the tight
one-cross-endpoint matching normal form can hold and that survivor-edge
deletion is essential.  They also refute the external-matching specialization
at the smallest control.  They are consistent with `d <= 6e+18`, but do not
establish the broader target uniformly.

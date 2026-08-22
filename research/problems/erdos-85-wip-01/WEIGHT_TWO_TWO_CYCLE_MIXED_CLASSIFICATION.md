# Weight-two two-cycle mixed-orientation classification

## Statement

Let a weight-two alternating-eigenline component at parameter `q` have

```text
H = C_(2a) disjoint-union C_(2b),          a+b=q,
```

with both cycles of length at least six.  Let `F` be its graph of exterior
two-point traces.  Suppose one cycle is T-saturated (none of its cycle edges
is in `F`) and the other is cross-saturated (all of its cycle edges are in
`F`).  Then, after naming the T-saturated cycle `C_(2a)`:

1. the two cross blocks of `F` are the complete opposite-sign blocks
   `K_(a,b) disjoint-union K_(a,b)`;
2. on `C_(2a)`, the internal trace graph is exactly
   `K_(a,a) minus C_(2a)`;
3. on `C_(2b)`, the internal trace graph is
   `K_(b,b) minus P_t`, where
   `P_t=Cay(Z/(2b), {+t,-t})` for one odd step `t` not congruent to `+1` or
   `-1`.

Thus every mixed two-cycle survivor is classified by its ordered half-lengths
`(a,b)` and one cyclic hole step on the cross-saturated cycle.  The earlier
`C6 + C_(2q-6)` survivor is the case `a=3`, where the T-side internal graph
reduces to the opposite matching.

## Capacity proof

Every trace joins opposite alternating signs, and `F` is `(q-2)`-regular.
Commutation `[H,F]=0` makes the internal `F`-degree constant on each cycle;
write these degrees as `r_a,r_b`.

Consider the T-saturated `C_(2a)`.  Its internal trace graph omits the two
cycle neighbors of every vertex, so

```text
r_a <= a-2.
```

On the other hand a vertex has only `b` eligible opposite-sign vertices in
the other cycle.  Its cross degree is `q-2-r_a`, whence

```text
q-2-r_a <= b,
r_a >= q-2-b = a-2.
```

Therefore `r_a=a-2`, and its cross degree is exactly `b`.  It is adjacent in
`F` to every eligible vertex of the other cycle.  Cross-edge balance then
forces cross degree `a` at every vertex of `C_(2b)`, so

```text
r_b=q-2-a=b-2.
```

This proves the complete cross blocks.  It also identifies the T-side
internal graph: among its `a` opposite-sign candidates, precisely the two
cycle neighbors are forbidden, so it is `K_(a,a)-C_(2a)`.

## Hole classification on the cross side

The complement of the cross-side internal trace graph inside `K_(b,b)` has
degree two.  Call it `P`.  Cross saturation says that the two cycle edges at
each vertex belong to `F`, so `P` avoids the cycle.  The diagonal block of
`[H,F]=0` says that the internal trace graph commutes with `C_(2b)`; hence so
does `P`.

The cycle-centralizer lemma proved in
`WEIGHT_TWO_SIX_LONG_ORIENTATION_CLASSIFICATION.md` now applies.  A symmetric
bipartite matrix commuting with the cycle and vanishing on its edges is
circulant.  Since `P` is a simple 2-factor, its support is one inverse pair
`{+t,-t}`.  Bipartiteness makes `t` odd, and cycle-edge avoidance excludes
`t=+1,-1`.  This gives item 3.

## Consequence and remaining gap

The quotient equation alone appeared to leave broad degree freedom when both
cycles had length at least eight.  The shore-capacity inequalities remove
that freedom completely: the universal degrees `a-2,b-2` are not merely one
solution but the only mixed solution, and they force the cross blocks.

This remains a classification rather than an exclusion.  Every individual
exterior row passes Hall, the shared-trace resolver layer has a uniform Euler
completion, and the scalar disjoint-pair capacity is an identity, as shown in
the companion report.  The unresolved terminal is the simultaneous integral
placement of the remaining disjoint-trace edges with exterior codegree at
most one, now for the explicit family `(a,b,t)` rather than arbitrary trace
graphs.

# NONBIP-CONNECTED Reiman/stability equality audit

Date: 2026-08-26.  Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **global extremal-equality mechanism cut**.

## Question

Can exact q-regularity on `q^2` vertices, C4-freeness, and the null
self-polar incidence interpretation put `A` in an equality or stability regime
for the C4 extremal bound?  Such a theorem could reconstruct a finite-plane
geometry and make the connected defect graph impossible.

The relevant modern stability result is He--Ma--Yang,
[Some exact results on 4-cycles: stability and
supersaturation](https://arxiv.org/abs/1912.00986).  At `q^2+q+1` vertices it
reconstructs a unique polarity graph when the edge count is within order `q`
of the extremal value.  Firke--Kosek--Nash--Williford,
[Extremal Graphs Without 4-Cycles](https://arxiv.org/abs/1201.4912), treats the
nearby even-order extremal problem at `q^2+q` vertices.  Our square-order
regular graph lies in neither equality window.

## Exact Reiman slack

For every C4-free graph, each unordered vertex pair has at most one common
neighbor.  Counting pairs of neighbors of a center gives

```text
sum_v binom(deg(v),2) <= binom(n,2).                  (1)
```

At `n=q^2` and constant degree `q`, the two sides of (1) differ by

```text
binom(q^2,2) - q^2 binom(q,2)
  = q^2(q-1)/2.                                      (2)
```

But the second-order defect graph `D` is `(q-1)`-regular on `q^2` vertices,
so

```text
q^2(q-1)/2 = |E(D)|.                                 (3)
```

Thus the entire Reiman slack is *exactly* the set of defect pairs.  Defect
connectedness changes how this slack is located, but does not reduce it by a
single unit.  Equality in (1) would require `D` to be empty, the opposite of
the intended branch.

The usual edge form of Reiman's bound is

```text
e(G) <= n(1+sqrt(4n-3))/4.
```

At `n=q^2`, our edge count is `q^3/2`, while the gap to this upper bound is

```text
q^2 (1 + sqrt(4q^2-3) - 2q) / 4 = Theta(q^2).        (4)
```

So even in edge-count coordinates this is not a vanishing-error equality
case.

## Comparison with polarity stability

To compare at the order used by polarity stability, adjoin `q+1` isolated
vertices.  This preserves C4-freeness and gives `N=q^2+q+1` vertices with the
same `q^3/2` edges.  The polarity extremal value at that order is

```text
q(q+1)^2/2.
```

The deficit of the augmented graph is therefore

```text
q(q+1)^2/2 - q^3/2 = q^2 + q/2.                      (5)
```

He--Ma--Yang's reconstruction window has deficit only order `q` (their
sharpened threshold is one half `q`, up to a lower-order term).  The deficit
in (5) is order `q^2`.  Reaching that window requires adding essentially the
missing point/line incidences of a plane; constructing those incidences is
the proposed completion theorem itself, not a consequence of stability.

## Why self-polarity does not repair the count

The symmetric zero-diagonal incidence matrix gives valuable structure, but
the proof of (1) sees only row weights and pairwise row intersections.  Those
data are already exactly

```text
A A^T = (q-1)I + J - D.
```

They do not see whether a uniquely covered pair is also an A-edge, which is
the triangle information `t_x`.  Consequently any entropy, Jensen, or
Cauchy--Schwarz refinement using only the same one- and two-row marginals
reduces to (2)--(3).  A stability successor would need a new theorem using
the placement of the polarity incidences inside those pairs; generic
C4-free stability and symmetric-configuration deficiency do not supply it.

## Verdict

The square-order model has macroscopic, exactly evaluated extremal slack:
pair-count slack `|E(D)|=Theta(q^3)` and edge-bound slack `Theta(q^2)`.
Connectedness merely connects the slack graph.  Published polarity stability
acts in an order-`q` deficit window after projective completion, while the
uncompleted model is order `q^2` away.  Therefore Reiman equality, standard
entropy refinements, and current polarity-stability reconstruction cannot
force either rooted triangle congruence.

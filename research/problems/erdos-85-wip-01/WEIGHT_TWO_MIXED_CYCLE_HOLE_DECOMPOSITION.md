# Weight-two mixed-cycle hole decomposition

## Statement

Let `C` be a weight-two alternating-eigenline component at parameter `q`.
Write its internal ambient two-factor as a disjoint union of even cycles

```text
H = disjoint-union_i C_(2a_i),             sum_i a_i=q,
```

and suppose every cycle has propagated to either the T-saturated orientation
(none of its `H`-edges is an exterior trace) or the cross-saturated
orientation (all of its `H`-edges are exterior traces).  Let `F` be the graph
of exterior two-point traces on `C`.

Then the global hole complement

```text
P = K_(q,q) - F
```

is a bipartite 2-factor commuting with `H`.  More precisely:

* every T-saturated cycle of `H` is an isolated component of `P`, equal to
  that cycle itself;
* `P` has no edge of a cross-saturated cycle;
* after deleting the T-saturated cycles, the restriction of `P` to the union
  of cross-saturated cycles is a 2-factor commuting with their cycle union
  and avoiding every internal cycle edge.

Equivalently, every T-saturated cycle is complete in `F` to every other cycle
on the eligible opposite-sign pairs, and has internal trace graph
`K_(a_i,a_i)-C_(2a_i)`.  All remaining freedom is concentrated in one
commuting hole 2-factor on the cross-saturated sector.

## Proof

The alternating eigenline makes every exterior trace join opposite signs.
There are `q` vertices of each sign, and `F` is `(q-2)`-regular.  Therefore
its complement in the complete opposite-sign graph is 2-regular:

```text
degree(P)=q-(q-2)=2.
```

The exact cross-block equation implies `[H,F]=0`.  The complete bipartite
graph `K_(q,q)` also commutes with `H`, because `H` has degree two on both
sign shores.  Hence `[H,P]=0`.

If a cycle is T-saturated, both `H`-neighbors of each of its vertices are
absent from `F` and therefore present in `P`.  They already exhaust degree
two in `P`.  No vertex of that cycle can have any further `P`-neighbor, so
the whole cycle is an isolated component of `P`.  Complementing back inside
`K_(q,q)` proves both cross-completeness and the stated internal trace graph.

If a cycle is cross-saturated, all of its `H`-edges lie in `F`, hence none
lies in `P`.  Removing the isolated T-cycle components leaves every remaining
vertex with degree two, preserves commutation with the corresponding block of
`H`, and leaves precisely the asserted cross-saturated hole sector.

## Important special cases

* If exactly one cycle is cross-saturated, the remaining hole sector lies on
  one cycle.  The reviewed cycle-centralizer lemma makes it
  `Cay(Z/(2b),{+t,-t})` for an odd `t` not congruent to `+1` or `-1`.
  Thus every such mixed profile is completely classified by its cycle
  lengths and this one step.
* For two cycles this recovers
  `WEIGHT_TWO_TWO_CYCLE_MIXED_CLASSIFICATION.md` immediately.
* If two or more cycles are cross-saturated, the unresolved component-side
  problem is no longer an arbitrary trace graph: it is exactly a commuting
  2-factor between a specified disjoint union of cycles, with all diagonal
  cycle edges forbidden.  This is the rectangular-intertwiner frontier.

## Scope

This is a q-generic reduction beneath `A-REG-NONBIP`.  It does not exclude
the cross-saturated hole sector or solve exterior completion.  It does remove
all T-saturated cycles from that algebraic problem and shows that mixed
orientation data are encoded exactly as isolated versus edge-avoiding
components of one global commuting 2-factor.

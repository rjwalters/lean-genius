# SIZE-TWO-CYCLIC: collision Levi-cycle audit

## A cycle forced by an empty selected fibre

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

Fix a difference fibre `t`.  Form the bipartite incidence graph whose left
vertices are the `q` source bases `x`, whose right vertices are absolute
matching edges in `sizeTwoCyclicMatchingOrbitSupport code {t}`, and where
`x` is incident to `e` exactly when `e` belongs to the source matching
`sizeTwoCyclicSourceMatching code (x,t)`.

This uses the hypotheses of the existing empty-fibre support theorem: a
full permutation code, looplessness, `a != -1-a`, and an empty selected
fibre.  It is therefore an interface for the current five-cell/full-code
subtree, not by itself a theorem about every reduced
`SizeTwoCyclicSameDifferenceCode`.

Every left vertex has degree `q-2`, so this graph has

```text
E = q(q-2)
```

edges.  If the selected-fibre graph at `t` is empty, the proved support
exclusion
`sizeTwoCyclicMatchingOrbitSupport_card_le_of_noAdj` gives at most
`q(q-3)` right vertices.  Hence

```text
V <= q + q(q-3) = q(q-2) = E.
```

For `q>=3` the graph is nonempty, and a finite forest has strictly fewer
edges than vertices.  Therefore this incidence graph contains a cycle.
The same-difference agreement cap excludes a 4-cycle: two distinct left
vertices on such a cycle would own the same two distinct absolute matching
edges, giving their row inner product at least two.  Thus every shortest
collision Levi cycle has length at least six.

This packages the empty-fibre duplicate-load lower bound into a connected,
base-resolved object rather than a histogram.  It retains exactly the fixed
source-pair/common-target incidences required by the corrected packing
terminal.

## Binary valuation law on a collision cycle

Write the left vertices encountered around a collision cycle as

```text
x_0, x_1, ..., x_(m-1), x_m=x_0
```

and let `d_i=x_(i+1)-x_i`.  Consecutive left vertices are distinct, so every
`d_i` is nonzero, and telescoping gives

```text
sum_i d_i = 0  in Z/(2^k).
```

Let `s=min_i v2(d_i)`.  Since every nonzero element of `Z/(2^k)` has
valuation below `k`, divide the congruence by `2^s` and reduce modulo two.
Exactly the terms with valuation `s` remain odd.  Consequently:

> The minimum separation valuation on every collision Levi cycle in a
> cyclic binary group occurs a positive even number of times.

This is genuinely binary at the top layer.  For `Z/12`, a cycle whose
increments all lie in the order-three subgroup can have minimum 2-adic
valuation at the full 2-primary exponent; division leaves a congruence
modulo three, not a parity statement.  The q12 five-cap countermodel is
therefore not a formal counterexample to this cycle invariant.

## What remains

The parity law alone is not a contradiction: a cycle may have two or more
minimum-valuation edges.  The terminal-facing missing lemma is now concrete:

```text
on a shortest collision Levi cycle compatible with the designated caps
and consecutive moving holes, two minimum-valuation source steps force
either a chord (hence a shorter cycle) or a repeated target for one fixed
source pair (hence a 4-cycle / cap violation).
```

This is a sharper target than a free-floating valuation-flow identity.  Its
bounded falsifier is the tuple-level `--dump-pair-supports` output augmented
with the incidence graph and its shortest cycles.  A q16 SAT model can test
the chord claim directly; q16 UNSAT would justify formalizing the cycle
existence and minimum-valuation parity interfaces.  Until that verdict,
those Lean interfaces would be premature.

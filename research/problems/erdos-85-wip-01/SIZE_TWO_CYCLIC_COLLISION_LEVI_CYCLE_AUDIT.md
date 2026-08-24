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
bounded diagnostic is the tuple-level `--dump-pair-supports` output augmented
with the incidence graph and its shortest cycles, but there is an important
scope restriction.  The current reduced q16 control imposes only the four or
five designated caps; the proof above excludes *all* Levi 4-cycles using the
full same-fibre cap family.  Thus a reduced q16 SAT model directly refutes the
chord claim only for cycles all of whose required pair separations are among
the imposed caps.  An uncapped 4-cycle in that model is irrelevant.  A q16
UNSAT verdict would support the smaller designated-cap subtree, while the
full-cycle route needs either a full-cap bounded model or a theorem reducing
its cycle separations to the designated set.  Until one of those exists,
formalizing the graph interfaces would be premature.

## Local chord mechanism is false

Valuation parity plus consecutive-hole admissibility does not force the
proposed chord.  At `q=8`, take `a=2`, selected fibre `t=0`, and three source
bases

```text
x_0=0, x_1=1, x_2=2.
```

Use the following three absolute target cells, written as `(row,column)`:

```text
w_01=(4,5),  w_12=(5,6),  w_20=(6,4).
```

Their target differences are respectively `1,1,6`, all allowed at `a=2`.
The incidences prescribe these relative row/column pairs:

```text
source 0: 4->5, 6->4
source 1: 3->4, 4->5
source 2: 3->4, 4->2.
```

For `t=0`, admissible rows exclude `0,1`; admissible columns exclude `0,7`.
Every displayed pair is admissible, and each source uses distinct rows and
columns, so its two assignments extend to a bijection between the six
admissible rows and columns.  The resulting incidence pattern is a
chordless six-cycle with no repeated target for a source pair.  Its source
increments are

```text
1, 1, 6,
```

whose minimum 2-adic valuation occurs twice, exactly satisfying the binary
cycle parity law.

The specified fragment is also closed under local route reversal.  Reversing
an incidence from source `(x,0)` with relative row `r` to target `(Y,u)`
prescribes, in the target source permutation `(Y,u)`, the assignment

```text
-r -> -r
```

back to `(x,0)`.  At the three target sources `(4,1)`, `(5,1)`, and `(6,6)`,
the two resulting reverse rows/columns are respectively `{4,5}`, `{4,5}`,
and `{2,4}`.  They avoid the appropriate consecutive row holes and fixed
column holes and are pairwise distinct within each source, so these reverse
partial assignments also extend to local bijections without conflict.

Therefore the hoped-for chord cannot follow from the cycle valuation,
consecutive moving holes, and reciprocity restricted to the cycle fragment.
A revival must use constraints from a *global* reciprocal completion through
the other routes (or additional designated caps), and must be tested before
any Levi graph formalization.  The cycle/parity observation remains correct
but is not currently a route to the terminal.

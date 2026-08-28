# Triple size-two Hamilton-decomposition parity audit

Node: `ThreeSizeTwoViaTripleExclusionPrinciple` beneath
`A-REG-NONBIP / NONBIP-MIXED`.

## Question

Can Thomason's parity theorem for Hamilton decompositions turn the six
connected restricted owner factors on three size-two components into the
missing genuinely ternary contradiction?

The relevant classical statement is the following.  If `X` is a 4-regular
graph and `e,f` are two fixed edges, then the number of decompositions of
`E(X)` into two Hamilton cycles in which `e` and `f` lie in different cycles
is even.  This is the `m = 2` case of Thomason's result on collections of
edge-disjoint Hamilton cycles [Thomason 1978, Section 2](https://www.dpmms.cam.ac.uk/~agt2/HC.pdf),
DOI `10.1016/S0167-5060(08)70511-9`.

## Exact attempted application

For distinct size-two components `a,b,c`, cyclicity says that the six graphs

`R_ab, R_ba, R_ac, R_ca, R_bc, R_cb`

are Hamilton cycles on the corresponding `2q`-vertex component supports.
On a fixed support, for example `a`, the union

`X_a = R_ab union R_ac`

is a 4-regular multigraph, counting a shared edge twice if necessary.  Its
displayed Hamilton decomposition is `{R_ab,R_ac}`.  Thomason therefore says
that after choosing one edge from each displayed cycle, an even number of
separated Hamilton decompositions of `X_a` exist.  In particular the
displayed decomposition is not unique in the relevant pointed class.

This conclusion is correct, genuinely about the two owner colours on one
component, and does not follow merely from connectedness of either cycle.
It nevertheless has no known consumer in the triple-exclusion principle.

## Why parity alone does not close the node

1. The principle assumes existence of three prescribed colours; it does not
   assert uniqueness of a Hamilton decomposition of any `X_a`.  Evenness of
   the number of decompositions is compatible with their existence.

2. An alternate decomposition of `X_a` is only a pair of Hamilton cycles on
   `a.supp`.  There is no theorem saying that its cycles are restricted owner
   graphs of actual defect components, or that they lift through the common
   `q^2` edge-label set to perfect-matching stars in `S_b` and `S_c`.

3. Applying parity independently to `X_a,X_b,X_c` produces three local even
   sets.  Coherent ambient edge labels do not define a map between these sets:
   an alternate cycle is made of owner edges, whereas the banked coherent ODC
   bijections act on selector edges/ambient vertex labels.  Thus there is no
   parity product or fixed-point count to compare.

4. The affine coherent-ODC countermodel is not contradicted.  It already
   realizes the common-label and perfect-matching-star laws, and parity merely
   supplies further local Hamilton decompositions whenever Hamilton cycles are
   chosen.  What the affine model lacks is precisely the self-indexed placement
   and the requirement that alternate cycles remain valid owner colours.

Consequently the implication

`three prescribed Hamilton owner pairs -> an odd/unique Hamilton decomposition`

is unsupported and, as stated, false at the abstract graph level.

## Smallest possible salvage

A Hamilton-parity route can be reopened only after proving a closure lemma of
the following form (or a weaker parity-preserving version):

> Every Hamilton decomposition of `R_ab union R_ac` that separates a fixed
> `b`-edge from a fixed `c`-edge canonically lifts, via the self-indexed
> component labels, to a permutation of the actual owner colours/components.

Then the finite number of available components could constrain the even
decomposition count simultaneously on `a,b,c`.  None of the current banked
dictionary theorems provides this closure; the star-perfect-matching and
coherent-composition laws concern selector edges, not arbitrary alternate
owner cycles.

## Disposition

Do not open a Lean parity wrapper: it would only prove existence/evenness of
uncontrolled alternate Hamilton decompositions and would not advance
`ThreeSizeTwoViaTripleExclusionPrinciple`.  The useful new target isolated by
this audit is **self-indexed alternate-decomposition closure**, not Hamilton
parity itself.  Absent that closure, this route is stopped.

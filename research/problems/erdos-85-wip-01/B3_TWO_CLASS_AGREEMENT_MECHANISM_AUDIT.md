# B.3 two-class agreement mechanism: outside-theorem audit

Status: **CUT, both as an imported rainbow-matching route and as a literal
two-class mechanism; retained only as a graph-derived certificate target.**
This note audits the outside-first route
requested at the current B.3 boundary.  It does not promote corpus evidence to
a theorem and does not revive (13f), (13t), or (13bn).

## Exact interface being sought

The surviving branch-3 consumer is not merely a choice of one representative
from each of two regular-triple classes.  After replacing selected degree
equalities by covering inequalities, the current audit has reduced the desired
contradiction to a strict nonnegative row-price separator supported on at most
three rows.  Equivalently, one needs to derive from the *actual* symmetric
C4-free residual relation and the two linked outer classes either

1. a strict one-fiber point-price certificate, or
2. a strict joint two-fiber certificate consumable by
   `false_of_scaledTwoUnitSupportsPointPriceCertificate`.

The word "linked" is load-bearing: the two class systems share row labels and
the same symmetric residual variables.  Separate matchings in the two systems
do not supply the certificate.

## Transfer test against known rainbow theorems

Three nearby frameworks were checked.

* Lu--Yu--Yuan, *Rainbow matchings for 3-uniform hypergraphs*
  (<https://arxiv.org/abs/2004.12558>), assumes sufficiently large order and a
  dense minimum vertex-degree threshold in every colour hypergraph.  The B.3
  object is an exact sparse order-nine boundary object, so neither hypothesis
  transfers.
* Lu--Wang, *Rainbow perfect matchings in 3-partite 3-uniform hypergraphs*
  (<https://arxiv.org/abs/2408.08523>), is likewise sufficiently-large and
  minimum-degree driven.  Its fractional rainbow input cannot see the shared
  symmetric residual edge variables that create the B.3 obstruction.
* Aharoni--Holzman--Jiang, *Rainbow fractional matchings*
  (<https://arxiv.org/abs/1805.09732>), obtains a rainbow fractional matching
  from `ceil(r n)` colour classes each already carrying a fractional matching
  of size `n` (or `rn-r+1` in the partite integral case).  Here there are only
  the two classes whose simultaneous agreement is in question.  Encoding
  rows as colours therefore fails its cardinality hypothesis.  Grouping rows
  into two colours loses the row prices and proves only the already-known
  separate feasibility.

The Aharoni--Haxell Hall condition has the same problem in a sharper form: to
apply it one must prove a matching-number lower bound for every union of the
relevant colour hypergraphs.  For the critical two-class union, that lower
bound is precisely the missing agreement/coupling assertion.  It is a valid
reformulation, not an imported proof.  This agrees with the earlier exact
fractional-deletion audit: the contracted object has fractional matching
number `7/2`, and essential two-point deletions recover the coupling source in
only 8 of 19 corpus cases.

## Decision

There is no honest q-generic theorem import at this interface.  In particular,
"apply a rainbow matching theorem to the two regular-triple classes" is cut:
it either fails the published density/colour-count hypotheses or assumes a
union-Hall inequality equivalent to the desired result.

The surviving target is narrower and graph-derived:

> **Support-three residual separator target.**  For the parameterized
> symmetric C4-free residual relation with the exact regular/exceptional row
> demands and its outer block partitions, **conditional on failure of the
> maximum-load full-fiber horn and the resulting exact exceptional-hole
> partition**, infeasibility of the global covering-degree system is witnessed
> by one exceptional and at most two regular row equations with a nonnegative
> separator.

This target is q-generic in the relevant sense: it mentions no enumeration of
the two order-nine triple classes.  The elementary truncation argument already
shows equality/covering equivalence on every chosen three-row support.  What is
still missing is the converse localization from global infeasibility to such a
support.  The corpus (all currently stored branch-3 payloads) supports it, but
that is evidence only.

Consequently the next admissible move is a Helly/facet argument for the
down-monotone covering-degree projection, using symmetry and C4-free caps.  A
finite proof that merely checks simultaneous agreement of the two order-nine
classes does not meet the transfer criterion and should not be formalized.

The unfiltered random-outer scans are regression tests for the conclusion,
not tests of this conditional implication: they do not encode the negation of
the full-fiber horn.  A decisive computational attack must jointly impose that
negation, the exact exceptional-hole partition, global infeasibility, and
feasibility of all 552 partial systems.  Merely accumulating more unrestricted
seeds cannot discharge the theorem.

## Direct class-support falsification

The phrase "two-class agreement" also fails as a description of the actual
small certificates.  The 24 regular triple rows form three parallel classes
`0..7`, `8..15`, and `16..23`.  A complete partial-primal census records the
parallel-class pair of every exceptional-plus-two-regular obstruction.

The durable seed-116 outer has exactly one such obstruction,
`{25,0,21}`.  Its regular rows have class pair `(0,2)`, so the certificate
does not use class 1 at all.  Fresh seeds 133--138 supply same-class as well as
cross-class obstructions; seeds 133, 134, 136, and 137 realize all six
unordered class-pair types.  Therefore neither "one row from each
non-diagonal class" nor even "two distinct regular classes" is a necessary
certificate shape.

`q9_branch3_partial_primal_audit.py` now reports this as
`parallel_class_pair_histogram`, derived from the exact infeasible partial
primals rather than from floating dual supports.  The surviving localization
target must quantify over an exceptional row and *arbitrary* two regular
rows.  This is a strict correction to the lane name, not evidence against the
broader support-three target.

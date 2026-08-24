# SIZE-TWO-CYCLIC: binary-only mechanism audit

## Context

The natural four-short forcing statement is false at general even modulus:
a translation-invariant q12 exact model has an empty selected middle fibre.
Any rescue for `BinarySizeTwoCyclicPackingBound` must therefore use a feature
specific to `q = 2^k`.

## Direct dyadic descent needs a selection theorem

The two holes behave perfectly under `Z/(2q) → Z/q`: if `a` maps to `a'`,
then `-1-a` maps to `-1-a'`.  Exact row and column hits do not descend
directly, however.  Every lower row or column has two upper lifts and each is
hit once, so projection produces multiplicity two rather than a unique hit.
Reduction mod two erases the hits, while selecting one lift has no automatic
compatibility with reciprocity.

Thus a counterexample at `2q` does not simply project to a counterexample at
`q`.  A descent proof needs a coherent halving or matching-selection theorem
for this multiplicity-two folded object.

## Hall--Paige does not forbid the two-hole blocks

The ordinary Hall--Paige theorem forbids a complete mapping when the Sylow
2-subgroup is nontrivial and cyclic.  That obstruction disappears after the
relevant two punctures.  Wang's
[On Special Near Orthomorphisms](https://combinatorialpress.com/jcmcc-articles/volume-021/on-special-near-orthomorphisms/)
proves that every abelian group whose cyclic Sylow 2-subgroup has order
greater than six admits a bijection on `G \ {e,h}` whose associated
orthomorphism is again a bijection on `G \ {e,h}`, where `h` is the unique
involution.  The paper includes an explicit example for `Z/8`.

Consequently, no per-fibre argument saying that a two-hole near-complete
mapping cannot exist can prove the packing bound.  A viable Hall--Paige
defect invariant must couple several fibres through reciprocity and the
agreement caps.

## Surviving structural route

Over a binary cyclic group,

```text
F₂[C_(2^k)] = F₂[z] / (z^(2^k)),  z = 1 + X,
```

so the group algebra is local and has one augmentation-ideal chain.  The
Frobenius identities `z^(2^j) = 1 + X^(2^j)` put the observed short,
quarter-turn, and half-turn separations on this chain.  The q12 countermodel
has an odd-factor semisimple component and does not test such a uniserial
valuation argument.

This makes an augmentation-filtration flow or a coherent dyadic halving
the current binary-specific candidates.  Both must still incorporate the
simultaneous multi-fibre caps; the bare half-turn differential is exact and
the per-fibre near-orthomorphisms exist.

## The base-resolved tensor exists, but linear flow is tautological

The required base coordinates have already been retained in
`Erdos85SizeTwoEigenlineCyclicBaseResolvedReciprocity.lean`.  Write

```text
K((x,t),(y,u)) = card (SizeTwoCyclicBaseResolvedRoute code x t y u).
```

The proved facts are stronger than the displacement marginals:

- `K` is `0/1` (`sizeTwoCyclicBaseResolvedRoute_card_le_one`);
- `K(v,w)=K(w,v)` pointwise (`..._card_symm`);
- fixing both bases partitions the allowed difference fibres away from the
  two moving holes (`..._card_sum_targetDifferences` and its transpose);
- fixing a source cell and an absolute target column gives exactly one route
  away from the two column holes
  (`sizeTwoCyclicBaseResolvedColumnRoute_card`).

Thus the proposed full non-translation-invariant object does not need a new
interface.  It also shows exactly why a *linear* valuation flow cannot be the
missing obstruction.  For any endpoint weight `lambda`, every routed dart
and its reverse contribute

```text
(lambda(v) + lambda(w)) K(v,w)
```

twice to the global directed sum.  Over `F2` this vanishes solely from
transpose symmetry.  Equivalently, summing any endpoint coboundary around
the symmetric tensor gives `0=0`.  Refining `lambda` by the 2-adic valuation
of `y-x`, by a base residue class, or by a fibre label does not change this:
reversal preserves `v2(y-x)`.  This recovers the previously observed
collision/common-target pairing, now before the base coordinate is summed
out.  It is parity bookkeeping, not a contradiction.

The packing information first appears quadratically.  The theorem
`sizeTwoCyclicBaseResolvedRoute_row_innerProduct_le_one` says that two
distinct rows in one difference fibre have inner product at most one.  A
binary-specific proof must therefore combine these quadratic inequalities
for several capped fibres with the exact linear partitions above.  The
minimal missing statement is not another conservation law but a
**three-cap valuation-change lemma**: under the designated short caps, an
empty middle fibre forces either

1. a collision/common-target pair at strictly smaller `v2` separation, or
2. the same pair of source rows owning two distinct precise target cells at
   the same separation.

The first alternative can descend only finitely in a cyclic 2-group; the
second makes the row inner product at least two and contradicts the cap.
Two source rows owning only one common target cell is allowed (it gives the
extremal inner product one), so any descent invariant must retain accumulated
common-target support for a fixed row pair.  No currently proved tensor
identity supplies either alternative.  In particular, aggregating `K` to
the displacement tensor loses exactly the correlations on which the
quadratic cap acts, while applying any linear `F2` weight directly to `K`
collapses by symmetry.  Future work on augmentation flow should start with
a weighted sum of these row inner products (or a coherent halving that
controls them), not with another marginal or endpoint-parity theorem.

The reduced q16 translation-invariant empty-middle control is exported to
DIMACS and running independently under Z3 and Kissat.  SAT would refute the
natural binary four-short forcing even in this symmetric subclass; UNSAT
would support, but not prove, a binary-only invariant.

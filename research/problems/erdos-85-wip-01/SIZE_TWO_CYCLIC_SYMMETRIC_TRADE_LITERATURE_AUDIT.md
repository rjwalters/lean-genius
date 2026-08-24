# Symmetric trade literature audit

Node: cap-preserving rank descent toward
`BinarySizeTwoCyclicPackingBound`.

## Question

A source-local change of its punctured row/column matching is a union of
alternating assignment cycles.  In absolute target coordinates, a
transposition is the familiar rectangle trade

```text
(y1,c1), (y2,c2)  <->  (y1,c2), (y2,c1).
```

It preserves both exact projections at that source.  The global problem is
to close such changes under edge reciprocity while retaining every
same-fibre owner-pair cap.  This audit asks whether Latin-trade or
one-factorization switching theory supplies that closure.

## Latin bitrades name the local symmetric difference only

The standard fact that the symmetric difference of two one-fold MDS codes
is a multidimensional Latin bitrade appears in Potapov,
[Multidimensional Latin
Bitrade](https://arxiv.org/abs/1104.1295).  It cleanly names the union of
assignment cycles between a routing and a locally improved routing, but it
starts with two already-valid global codes.  It does not extend one local
cycle through transpose reciprocity or prove that the second code exists.

Likewise, constructions of Latin bitrades from autoparatopism groups, such
as Cavenagh--Drápal--Hämäläinen,
[Latin bitrades derived from groups](https://arxiv.org/abs/0704.1730), and
the newer autoparatopism construction literature produce trades from a
specified symmetry group.  Our arbitrary-base routing has no global
translation/autoparatopism hypothesis; the shifted-base reciprocal
involution is only one fixed symmetry and does not close a source rectangle
by itself.

The term **self-orthogonal Latin square** is also a false friend here.  It
means a Latin square orthogonal to its transpose, not a trade invariant
under transpose.  Its broad existence theory therefore supplies neither
our entrywise symmetric graph nor the moving two-hole constraints.

## One-factor switches carry an explicit connectivity warning

Gill--Wanless,
[Switching in One-Factorisations](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v21i2p49/pdf/0),
study the closest standard cycle switch: interchange two factor colours on
an even cycle in their union.  Such a switch preserves a parity invariant,
and the resulting switching graph of one-factorizations is disconnected
for the relevant larger orders.  Thus even in the complete, unpunctured
setting, alternating-cycle switches are not a general connectivity or
descent theorem.

This warning matches the present obstruction.  A local rectangle changes
degrees and exact projections at its old and new target cells after
reciprocity is restored.  Closing those defects requires further rectangles,
but generic trade theory gives no guarantee that the closure lands in the
desired parity component, avoids the moving holes, or preserves the
owner-pair caps.

## Verdict

The literature provides good language—Latin bitrade, autoparatopism orbit,
and factor switch—but no off-the-shelf cap-preserving reciprocal closure.
More strongly, one-factorization switching shows that an unrestricted
claim of cycle-switch connectivity would be false even before adding our
affine holes and caps.

The surviving descent lemma must therefore be code-specific.  It should
construct a transpose-stable union of assignment cycles and prove all four
properties directly:

1. row and absolute-column projections cancel at every affected source;
2. old/new target imbalances cancel after shifted-base reciprocity;
3. no owner pair gains a second common target; and
4. total defect rank strictly decreases.

The q8 short-cycle census verifies only the source-local precursor to item
1.  Items 2--4 remain the global theorem; calling the move a Latin trade or
a one-factor switch does not discharge them.

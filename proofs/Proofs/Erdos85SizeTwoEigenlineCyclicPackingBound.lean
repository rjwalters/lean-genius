import Proofs.Erdos85SizeTwoEigenlineCyclicCrossAgreement

/-!
# The cyclic partial-permutation packing gap

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

The grid construction produces `q * (q - 2)` partial permutations.  Their
domains and ranges each omit two cyclically correlated points, distinct
codewords agree in at most one admissible position, and the routing is
reciprocal and loopless.  For total permutations on `q - 2` points, the
usual two-position injection would allow at most `(q - 2) * (q - 3)`
codewords.  The moving holes are exactly what prevents that elementary
argument from applying directly.

This file states the missing packing assertion without assuming it, and
provides the graph-facing consumer.  Proving `sizeTwoCyclicPackingExclusion`
for binary `q` would finish the abstract refutation half of the
size-two-eigenline node.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The reduced code isolated by the small-`q` probes.  Only agreements
between two sources at the *same* allowed difference are retained.  The
cross-difference bounds and the graph have been forgotten; reciprocity is
still present. -/
structure SizeTwoCyclicSameDifferenceCode
    (q : ℕ) [NeZero q] (a : ZMod q) where
  toReciprocalCode : SizeTwoCyclicReciprocalPermutationCode q a
  same_difference_agreement_le_one : ∀ (x d : ZMod q), d ≠ 0 →
    ∀ t : sizeTwoAllowedDifference q a,
      Fintype.card (SizeTwoCrossShiftedPermutationAgreement q a
        toReciprocalCode.toPermutationCode.perm x d t t) ≤ 1

/-- Every full code restricts to the same-difference code. -/
def SizeTwoCyclicFullPermutationCode.toSameDifferenceCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a) :
    SizeTwoCyclicSameDifferenceCode q a where
  toReciprocalCode := code.toReciprocalCode
  same_difference_agreement_le_one := by
    intro x d hd t
    exact code.cross_agreement_le_one x d t t (Or.inl hd)

/-- The precise abstract packing assertion at parameters `q,a`: even the
reduced same-difference reciprocal code cannot exist.  This is stronger and
cleaner than merely excluding the full code. -/
def SizeTwoCyclicPackingExclusion
    (q : ℕ) [NeZero q] (a : ZMod q) : Prop :=
  IsEmpty (SizeTwoCyclicSameDifferenceCode q a)

/-- Binary-family form of the packing conjecture needed by the Erdős-85
critical path.  The restrictions on `a` are the non-hole conclusions of the
reflection-circulant classification. -/
def BinarySizeTwoCyclicPackingBound : Prop :=
  ∀ (k : ℕ), 3 ≤ k →
    let q := 2 ^ k
    ∀ a : ZMod q, a ≠ 0 → a ≠ -1 →
      SizeTwoCyclicPackingExclusion q a

/-- Consumer from the abstract packing assertion back to the exterior grid.
It deliberately exposes only the hypotheses used to construct the full
partial-permutation code. -/
theorem false_of_sizeTwoCyclicPackingExclusion
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (v : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset v).filter fun w => w.1.1 = y).card =
        if v.1.2 = y ∨ v.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (v : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset v).filter fun w => w.1.2 = z).card =
        if v.1.1 = z ∨ v.1.1 = z + 1 then 0 else 1)
    (hpack : SizeTwoCyclicPackingExclusion q a) : False :=
  hpack.false
    (sizeTwoCyclicFullPermutationCode_of_grid
      q a C hfree hrow_hit hcol_hit).toSameDifferenceCode

end

end Erdos85

#print axioms Erdos85.false_of_sizeTwoCyclicPackingExclusion

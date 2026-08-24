import Proofs.Erdos85FinsetInvolutionParity

/-!
# Boundary parity for labeled paired occurrences

Cycle routing pairs the flip-edge occurrences by a fixed-point-free
involution.  For any block of witness labels, a crossing pair has a unique
endpoint whose label lies in the block.  The parity of these representatives
equals the parity of all occurrences in the block.  This is the abstract
handshake identity used in `(73rnz_cjibkzj)--(73rnz_cjibkzk)`.
-/

namespace Erdos85

/-- Occurrences whose label lies in a chosen label block. -/
def labeledOccurrenceBlock
    {O L : Type*} [DecidableEq O] [DecidableEq L]
    (S : Finset O) (label : O → L) (R : Finset L) : Finset O :=
  S.filter fun e => label e ∈ R

/-- Representatives of paired crossings, chosen canonically as the endpoint
whose label lies in `R`.  Thus every crossing pair is counted exactly once. -/
def labeledPairBoundaryRepresentatives
    {O L : Type*} [DecidableEq O] [DecidableEq L]
    (mate : O → O) (S : Finset O) (label : O → L) (R : Finset L) : Finset O :=
  S.filter fun e => label e ∈ R ∧ label (mate e) ∉ R

private def labeledPairInternalOccurrences
    {O L : Type*} [DecidableEq O] [DecidableEq L]
    (mate : O → O) (S : Finset O) (label : O → L) (R : Finset L) : Finset O :=
  S.filter fun e => label e ∈ R ∧ label (mate e) ∈ R

/-- The occurrences internal to a label block are themselves closed under
the pairing involution and therefore have even cardinality. -/
theorem even_labeledPairInternalOccurrences
    {O L : Type*} [DecidableEq O] [DecidableEq L]
    (mate : O → O) (S : Finset O) (label : O → L) (R : Finset L)
    (hclosed : ∀ e ∈ S, mate e ∈ S)
    (hinvol : ∀ e ∈ S, mate (mate e) = e)
    (hfree : ∀ e ∈ S, mate e ≠ e) :
    Even (labeledPairInternalOccurrences mate S label R).card := by
  apply even_card_of_closed_fixedPointFree_involution mate
  · intro e he
    simp only [labeledPairInternalOccurrences, Finset.mem_filter] at he ⊢
    refine ⟨hclosed e he.1, he.2.2, ?_⟩
    rw [hinvol e he.1]
    exact he.2.1
  · intro e he
    exact hinvol e (Finset.mem_filter.mp he).1
  · intro e he
    exact hfree e (Finset.mem_filter.mp he).1

/-- **Labeled involution boundary parity.**  The parity of all paired
occurrences labeled in `R` is the parity of pairs crossing the label cut,
represented by their unique `R`-side occurrence. -/
theorem even_labeledOccurrenceBlock_iff_even_boundaryRepresentatives
    {O L : Type*} [DecidableEq O] [DecidableEq L]
    (mate : O → O) (S : Finset O) (label : O → L) (R : Finset L)
    (hclosed : ∀ e ∈ S, mate e ∈ S)
    (hinvol : ∀ e ∈ S, mate (mate e) = e)
    (hfree : ∀ e ∈ S, mate e ≠ e) :
    Even (labeledOccurrenceBlock S label R).card ↔
      Even (labeledPairBoundaryRepresentatives mate S label R).card := by
  let I := labeledPairInternalOccurrences mate S label R
  let B := labeledPairBoundaryRepresentatives mate S label R
  have hpartition : labeledOccurrenceBlock S label R = I ∪ B := by
    ext e
    simp only [labeledOccurrenceBlock, I, B,
      labeledPairInternalOccurrences, labeledPairBoundaryRepresentatives,
      Finset.mem_filter, Finset.mem_union]
    by_cases hm : label (mate e) ∈ R <;> simp [hm]
  have hdisj : Disjoint I B := by
    rw [Finset.disjoint_left]
    intro e heI heB
    simp only [I, labeledPairInternalOccurrences, Finset.mem_filter] at heI
    simp only [B, labeledPairBoundaryRepresentatives, Finset.mem_filter] at heB
    exact heB.2.2 heI.2.2
  have hcard : (labeledOccurrenceBlock S label R).card = I.card + B.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisj]
  have hevenI : Even I.card :=
    even_labeledPairInternalOccurrences mate S label R hclosed hinvol hfree
  rw [hcard]
  constructor
  · intro htotal
    exact (Nat.even_add.mp htotal).mp hevenI
  · intro hevenB
    exact Nat.even_add.mpr (iff_of_true hevenI hevenB)

/-- Odd form of the same boundary handshake identity. -/
theorem odd_labeledOccurrenceBlock_iff_odd_boundaryRepresentatives
    {O L : Type*} [DecidableEq O] [DecidableEq L]
    (mate : O → O) (S : Finset O) (label : O → L) (R : Finset L)
    (hclosed : ∀ e ∈ S, mate e ∈ S)
    (hinvol : ∀ e ∈ S, mate (mate e) = e)
    (hfree : ∀ e ∈ S, mate e ≠ e) :
    Odd (labeledOccurrenceBlock S label R).card ↔
      Odd (labeledPairBoundaryRepresentatives mate S label R).card := by
  rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, not_iff_not]
  exact even_labeledOccurrenceBlock_iff_even_boundaryRepresentatives
    mate S label R hclosed hinvol hfree

end Erdos85

#print axioms Erdos85.even_labeledPairInternalOccurrences
#print axioms Erdos85.even_labeledOccurrenceBlock_iff_even_boundaryRepresentatives
#print axioms Erdos85.odd_labeledOccurrenceBlock_iff_odd_boundaryRepresentatives

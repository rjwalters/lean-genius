import Proofs.Erdos85OneHighGraphPairingRefinement
import Proofs.Erdos85OneHighOddProfileSlotVariantCoverage
import Proofs.Erdos85OneHighRefinementPinnedCnfSatisfaction

/-! # The graph pairing in canonical CNF edge slots

`oneHighGraphPairingRefinement` sorts matching edges by their full pair code,
which is the right representation for the finite table inventory.  Pinned CNF
units instead refer to the literal canonical leaf slots `01` and `23`.  This
file records that second representation directly, before proving that its
rowwise sort is the inventory refinement.
-/

namespace Erdos85

noncomputable section

/-- Unique missed branch label at one canonical leaf coordinate.  Callers use
this only at the matched offsets `0,1` and, in a two-edge row, `2,3`. -/
def oneHighGraphCanonicalSlotLabel
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) (offset : Fin 5) : Fin 8 :=
  let s := p.branchLabel.symm source
  p.branchLabel (oneHighMissingBranch G v p.mate s
    ((p.leafLabel s).symm offset).1)

/-- Miss-label pairs in the literal canonical matching-edge order. -/
def oneHighGraphCanonicalSlotRow
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) : List OneHighLabelPair :=
  let label := oneHighGraphCanonicalSlotLabel G hfree p source
  if oneHighFamilyInternalEdges p.profile source = 1 then
    [(label 0, label 1)]
  else
    [(label 0, label 1), (label 2, label 3)]

/-- The eight canonical-slot rows that the refinement-pinned CNF sees. -/
def oneHighGraphCanonicalSlotRefinement
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) :
    List (List OneHighLabelPair) :=
  List.ofFn fun source : Fin 8 =>
    oneHighGraphCanonicalSlotRow G hfree p source

@[simp] theorem oneHighGraphCanonicalSlotRefinement_length
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) :
    (oneHighGraphCanonicalSlotRefinement G hfree p).length = 8 := by
  simp [oneHighGraphCanonicalSlotRefinement]

theorem oneHighGraphCanonicalSlotRow_length
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    (oneHighGraphCanonicalSlotRow G hfree p source).length =
      oneHighFamilyInternalEdges p.profile source := by
  rw [oneHighGraphCanonicalSlotRow]
  by_cases h : oneHighFamilyInternalEdges p.profile source = 1
  · simp [h]
  · have htwo : oneHighFamilyInternalEdges p.profile source = 2 := by
      unfold oneHighFamilyInternalEdges at h ⊢
      split <;> simp_all
    simp [htwo]

end

end Erdos85

#print axioms Erdos85.oneHighGraphCanonicalSlotRow_length

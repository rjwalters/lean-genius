import Proofs.Erdos85OneHighGraphCanonicalSlotDuplicate

/-! # Global canonical-slot coverage for one-high graph refinements -/

namespace Erdos85

noncomputable section

/-- Every literal canonical graph row is one of the slot orders admitted by
its sorted matching-pairing row. -/
theorem oneHighGraphCanonicalSlotRow_mem_variants
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    oneHighGraphCanonicalSlotRow G hfree p source ∈
      oneHighPairingRowSlotVariants
        (oneHighGraphSourcePairing G hfree hv p source) := by
  by_cases hone : oneHighFamilyInternalEdges p.profile source = 1
  · exact oneHighGraphCanonicalSlotRow_mem_variants_of_internalEdges_eq_one
      G hfree hv p source hone
  · have htwo : oneHighFamilyInternalEdges p.profile source = 2 := by
      unfold oneHighFamilyInternalEdges at hone ⊢
      split <;> simp_all
    by_cases hequal :
        (oneHighGraphCanonicalSlotLabel G hfree p source 0,
          oneHighGraphCanonicalSlotLabel G hfree p source 1) =
        (oneHighGraphCanonicalSlotLabel G hfree p source 2,
          oneHighGraphCanonicalSlotLabel G hfree p source 3)
    · exact oneHighGraphCanonicalSlotRow_mem_variants_of_two_equal
        G hfree hv p source htwo hequal
    · exact oneHighGraphCanonicalSlotRow_mem_variants_of_two_distinct
        G hfree hv p source htwo hequal

/-- The literal eight-row graph refinement is pointwise compatible with the
canonical-slot expansion of its authoritative sorted pairing refinement. -/
theorem oneHighGraphCanonicalSlotRefinement_slotCompatible
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) :
    OneHighRefinementSlotCompatible
      (oneHighGraphPairingRefinement G hfree hv p)
      (oneHighGraphCanonicalSlotRefinement G hfree p) := by
  unfold OneHighRefinementSlotCompatible
  unfold oneHighGraphPairingRefinement
  unfold oneHighGraphCanonicalSlotRefinement
  simp only [List.ofFn_succ, List.map_cons, OneHighChoicesCompatible]
  exact ⟨oneHighGraphCanonicalSlotRow_mem_variants G hfree hv p 0,
    oneHighGraphCanonicalSlotRow_mem_variants G hfree hv p 1,
    oneHighGraphCanonicalSlotRow_mem_variants G hfree hv p 2,
    oneHighGraphCanonicalSlotRow_mem_variants G hfree hv p 3,
    oneHighGraphCanonicalSlotRow_mem_variants G hfree hv p 4,
    oneHighGraphCanonicalSlotRow_mem_variants G hfree hv p 5,
    oneHighGraphCanonicalSlotRow_mem_variants G hfree hv p 6,
    oneHighGraphCanonicalSlotRow_mem_variants G hfree hv p 7,
    trivial⟩

end

end Erdos85

#print axioms Erdos85.oneHighGraphCanonicalSlotRow_mem_variants
#print axioms Erdos85.oneHighGraphCanonicalSlotRefinement_slotCompatible

import Proofs.Erdos85ThreeSeparatorUniformRFiberOverlapLedger

/-!
# The residual-overlap graph injects into the exceptional K-star

Edges of `Γ_R` are labeled by the points of `C \ U_P`.  The same point
labels a unique edge of `Γ_K` incident with the exceptional center `c`.
This gives the canonical injection in B39, and the unused part of the
`c`-star is labeled by `C ∩ U_P`.
-/

open Finset

namespace Erdos85

noncomputable section

/-- Abstract label form of the canonical B39 injection.  Each residual
overlap edge has a unique star edge carrying the same label; distinct
residual edges have distinct labels. -/
theorem exists_injective_designStarMap_of_unique_label
    {X ER EK : Type*} [DecidableEq ER] [DecidableEq EK]
    (residualEdges : Finset ER) (exceptionalStar : Finset EK)
    (residualLabel : ER → X) (starLabel : EK → X)
    (hlabelInj : Set.InjOn residualLabel residualEdges)
    (hunique : ∀ e ∈ residualEdges,
      ∃! k, k ∈ exceptionalStar ∧ starLabel k = residualLabel e) :
    ∃ f : (e : ↥residualEdges) → ↥exceptionalStar,
      Function.Injective f ∧
        ∀ e, starLabel (f e) = residualLabel e := by
  let f : (e : ↥residualEdges) → ↥exceptionalStar := fun e =>
    ⟨Classical.choose (ExistsUnique.exists (hunique e e.property)),
      (Classical.choose_spec
        (ExistsUnique.exists (hunique e e.property))).1⟩
  have hflabel : ∀ e, starLabel (f e) = residualLabel e := by
    intro e
    exact (Classical.choose_spec
      (ExistsUnique.exists (hunique e e.property))).2
  refine ⟨f, ?_, hflabel⟩
  intro e e' heq
  apply Subtype.ext
  apply hlabelInj e.property e'.property
  calc
    residualLabel e = starLabel (f e) := (hflabel e).symm
    _ = starLabel (f e') := by rw [heq]
    _ = residualLabel e' := hflabel e'

/-- Exact cardinality split of the B39 star.  The residual overlap edges
are labeled by `C \ U`, the full exceptional star by `C`, and its
complement is therefore `C ∩ U`. -/
theorem designStar_card_eq_residualEdges_add_overlap
    {X ER EK : Type*} [DecidableEq X] [DecidableEq ER] [DecidableEq EK]
    (C U : Finset X) (residualEdges : Finset ER)
    (exceptionalStar : Finset EK) (a : ℕ)
    (hCcard : C.card = a)
    (hresidual : residualEdges.card = (C \ U).card)
    (hstar : exceptionalStar.card = C.card) :
    exceptionalStar.card = residualEdges.card + (C ∩ U).card ∧
      exceptionalStar.card = a := by
  have hsplit := Finset.card_sdiff_add_card_inter C U
  omega

/-- Combined B39 interface: the canonical label-preserving injection and
the exact decomposition of the exceptional star. -/
theorem exists_designStar_injection_and_card_ledger
    {X ER EK : Type*} [DecidableEq X] [DecidableEq ER] [DecidableEq EK]
    (C U : Finset X) (residualEdges : Finset ER)
    (exceptionalStar : Finset EK)
    (residualLabel : ER → X) (starLabel : EK → X) (a : ℕ)
    (hlabelInj : Set.InjOn residualLabel residualEdges)
    (hunique : ∀ e ∈ residualEdges,
      ∃! k, k ∈ exceptionalStar ∧ starLabel k = residualLabel e)
    (hCcard : C.card = a)
    (hresidual : residualEdges.card = (C \ U).card)
    (hstar : exceptionalStar.card = C.card) :
    (∃ f : (e : ↥residualEdges) → ↥exceptionalStar,
      Function.Injective f ∧
        ∀ e, starLabel (f e) = residualLabel e) ∧
      exceptionalStar.card = residualEdges.card + (C ∩ U).card ∧
      exceptionalStar.card = a := by
  exact ⟨exists_injective_designStarMap_of_unique_label residualEdges
      exceptionalStar residualLabel starLabel hlabelInj hunique,
    designStar_card_eq_residualEdges_add_overlap C U residualEdges
      exceptionalStar a hCcard hresidual hstar⟩

end


end Erdos85


#print axioms Erdos85.exists_injective_designStarMap_of_unique_label
#print axioms Erdos85.designStar_card_eq_residualEdges_add_overlap
#print axioms Erdos85.exists_designStar_injection_and_card_ledger

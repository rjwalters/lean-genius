import Proofs.Erdos85ThreeHighExternalFarColoring

namespace Erdos85

/-- A finite obstruction using common-neighbor and canonical-block inequalities. -/
def ThreeHighExternalFarObstruction {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15) : Prop :=
  (∀ i, encodedRowDegree (U (v i)) ≤ 2) ∧
  ¬ ∃ c : Fin n → Fin 2,
    ∀ i j, v i ≠ v j → ((∃ s, U (v i) s = true ∧ U (v j) s = true) ∨
      ((@finProdFinEquiv 3 5).symm (v i)).1 = ((@finProdFinEquiv 3 5).symm (v j)).1) → c i ≠ c j

instance {n : Nat} (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15) :
    Decidable (ThreeHighExternalFarObstruction U v) := by
  unfold ThreeHighExternalFarObstruction
  infer_instance

attribute [local irreducible] threeHighCrossDomain

theorem ThreeHighExternalFarObstruction.no_external_cross {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15)
    (h : ThreeHighExternalFarObstruction U v)
    (R : Fin 8 → Fin 8 → Bool) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) : False := by
  rw [threeHighExternalBlockCap_factor] at hExt
  simp only [Bool.and_eq_true] at hExt
  obtain ⟨c,hc⟩ := threeHighCrossDomain_external_far_coloring U R cross hc
    hExt.2
  apply h.2
  refine ⟨fun i => c (v i),?_⟩
  intro i j hij hconf
  exact hc _ _ (h.1 i) (h.1 j) hij hconf

end Erdos85
#print axioms Erdos85.ThreeHighExternalFarObstruction.no_external_cross

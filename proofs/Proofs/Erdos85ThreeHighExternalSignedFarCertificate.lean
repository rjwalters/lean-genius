import Proofs.Erdos85ThreeHighExternalSignedFarColoring

namespace Erdos85

/-- A selected finite set of low-degree labels has no compatible two-coloring.
Selected labels may repeat; neither injectivity nor coverage is assumed. -/
def ThreeHighExternalSignedFarObstruction {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15) : Prop :=
  (∀ i, encodedRowDegree (U (v i)) ≤ 2) ∧
  ¬ ∃ c : Fin n → Fin 2,
    (∀ i j, U (v i) (v j) = true → c i = c j) ∧
    (∀ i j, v i ≠ v j →
      ((∃ s, U (v i) s = true ∧ U (v j) s = true) ∨
        ((@finProdFinEquiv 3 5).symm (v i)).1 = ((@finProdFinEquiv 3 5).symm (v j)).1) → c i ≠ c j)

instance {n : Nat} (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15) :
    Decidable (ThreeHighExternalSignedFarObstruction U v) := by
  unfold ThreeHighExternalSignedFarObstruction
  infer_instance

attribute [local irreducible] threeHighCrossDomain

theorem ThreeHighExternalSignedFarObstruction.no_external_cross {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15)
    (h : ThreeHighExternalSignedFarObstruction U v)
    (R : Fin 8 → Fin 8 → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (hExt : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) : False := by
  rw [threeHighExternalBlockCap_factor] at hExt
  simp only [Bool.and_eq_true] at hExt
  obtain ⟨c,heq,hne⟩ := threeHighCrossDomain_external_signed_far_coloring U R cross hc hExt.2 h67 h76
  apply h.2
  refine ⟨fun i => c (v i),?_,?_⟩
  · intro i j hij
    exact heq _ _ (h.1 i) (h.1 j) hij
  · intro i j hij hcommon
    exact hne _ _ (h.1 i) (h.1 j) hij hcommon

end Erdos85
#print axioms Erdos85.ThreeHighExternalSignedFarObstruction.no_external_cross

import Proofs.Erdos85ThreeHighFarEdgeColoring

namespace Erdos85

/-- A selected finite set of low-degree labels has no compatible two-coloring.
Selected labels may repeat; neither injectivity nor coverage is assumed. -/
def ThreeHighFarColorObstruction {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15) : Prop :=
  (∀ i, encodedRowDegree (U (v i)) ≤ 2) ∧
  ¬ ∃ c : Fin n → Fin 2,
    (∀ i j, U (v i) (v j) = true → c i = c j) ∧
    (∀ i j, v i ≠ v j →
      (∃ s, U (v i) s = true ∧ U (v j) s = true) → c i ≠ c j)

instance {n : Nat} (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15) :
    Decidable (ThreeHighFarColorObstruction U v) := by
  unfold ThreeHighFarColorObstruction
  infer_instance

attribute [local irreducible] threeHighCrossDomain

theorem ThreeHighFarColorObstruction.no_cross {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (v : Fin n → Fin 15)
    (h : ThreeHighFarColorObstruction U v)
    (R : Fin 8 → Fin 8 → Bool) (h67 : R 6 7 = true) (h76 : R 7 6 = true)
    (cross : ThreeHighCross) : cross ∉ threeHighCrossDomain U R := by
  intro hc
  obtain ⟨c,heq,hne⟩ := threeHighCrossDomain_far_edge_coloring U R cross hc h67 h76
  apply h.2
  refine ⟨fun i => c (v i),?_,?_⟩
  · intro i j hij
    exact heq _ _ (h.1 i) (h.1 j) hij
  · intro i j hij hcommon
    exact hne _ _ (h.1 i) (h.1 j) hij hcommon

end Erdos85
#print axioms Erdos85.ThreeHighFarColorObstruction.no_cross

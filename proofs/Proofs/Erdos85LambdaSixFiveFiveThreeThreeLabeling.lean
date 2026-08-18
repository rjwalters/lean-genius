import Proofs.Erdos85OrderSixtyFourTenSixComponentLabeling
import Proofs.Erdos85LambdaSixClassificationSAT

/-! # Canonical labeling for the `[5,5,3,3]` lambda-six component -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The exact `C₅ ⊔ C₅ ⊔ C₃ ⊔ C₃` graph used by the lambda-six census. -/
def fiveFiveThreeThreeCycleGraph : SimpleGraph (Fin 16) where
  Adj x y := bitAdj256 lambdaSixFiveFiveThreeThreeH256 x y = true
  symm := ⟨by native_decide⟩
  loopless := ⟨by native_decide⟩

instance fiveFiveThreeThreeCycleGraph_adjDecidable :
    DecidableRel fiveFiveThreeThreeCycleGraph.Adj := by
  intro x y
  change Decidable (bitAdj256 lambdaSixFiveFiveThreeThreeH256 x y = true)
  infer_instance

@[simp] theorem fiveFiveThreeThreeCycleGraph_adj_iff (x y : Fin 16) :
    fiveFiveThreeThreeCycleGraph.Adj x y ↔
      bitAdj256 lambdaSixFiveFiveThreeThreeH256 x y = true := Iff.rfl

theorem fiveFiveThreeThreeCycleGraph_degree :
    ∀ x, fiveFiveThreeThreeCycleGraph.degree x = 2 := by
  native_decide

/-- A graph carries the exact census labeling when an equivalence transports
its adjacency relation to the fixed `C₅ ⊔ C₅ ⊔ C₃ ⊔ C₃` graph. -/
structure FiveFiveThreeThreeComponentLabeling
    {V : Type*} (H : SimpleGraph V) where
  toEquiv : V ≃ Fin 16
  map_adj_iff : ∀ u v,
    H.Adj u v ↔ fiveFiveThreeThreeCycleGraph.Adj (toEquiv u) (toEquiv v)

/-- Relabel any graph on the component support into census coordinates. -/
def fiveFiveThreeThreeRelabeledGraph
    {V : Type*} (R : SimpleGraph V)
    (label : FiveFiveThreeThreeComponentLabeling R) :
    SimpleGraph (Fin 16) := R.map label.toEquiv.toEmbedding

@[simp] theorem fiveFiveThreeThreeRelabeledGraph_adj
    {V : Type*} (R : SimpleGraph V)
    (label : FiveFiveThreeThreeComponentLabeling R) (x y : Fin 16) :
    (fiveFiveThreeThreeRelabeledGraph R label).Adj x y ↔
      R.Adj (label.toEquiv.symm x) (label.toEquiv.symm y) := by
  rw [fiveFiveThreeThreeRelabeledGraph, SimpleGraph.map_adj]
  constructor
  · rintro ⟨u, v, huv, rfl, rfl⟩
    simpa using huv
  · intro hxy
    exact ⟨label.toEquiv.symm x, label.toEquiv.symm y, hxy,
      label.toEquiv.apply_symm_apply x, label.toEquiv.apply_symm_apply y⟩

end

end Erdos85

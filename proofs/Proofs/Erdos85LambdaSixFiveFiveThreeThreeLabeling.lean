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

def fiveFiveThreeThreeSizes : Fin 4 → ℕ := ![5, 5, 3, 3]

theorem fiveFiveThreeThreeSizes_sum :
    ∑ i, fiveFiveThreeThreeSizes i = 16 := by decide

/-- The abstract disjoint union of cycles before flattening its four fibers
into the census ordering on `Fin 16`. -/
def fiveFiveThreeThreeSigmaGraph :
    SimpleGraph ((i : Fin 4) × Fin (fiveFiveThreeThreeSizes i)) where
  Adj z w := ∃ (i : Fin 4) (x y : Fin (fiveFiveThreeThreeSizes i)),
    z = ⟨i, x⟩ ∧ w = ⟨i, y⟩ ∧
      (cycleGraph (fiveFiveThreeThreeSizes i)).Adj x y
  symm := ⟨by
    rintro z w ⟨i, x, y, rfl, rfl, hxy⟩
    exact ⟨i, y, x, rfl, rfl, hxy.symm⟩⟩
  loopless := ⟨by
    rintro z ⟨i, x, y, hzx, hzy, hxy⟩
    subst z
    have hxy' : x = y := by
      cases hzy
      rfl
    subst y
    exact (cycleGraph _).loopless.irrefl x hxy⟩

instance fiveFiveThreeThreeSigmaGraph_adjDecidable :
    DecidableRel fiveFiveThreeThreeSigmaGraph.Adj := by
  intro z w
  change Decidable (∃ (i : Fin 4) (x y : Fin (fiveFiveThreeThreeSizes i)),
    z = ⟨i, x⟩ ∧ w = ⟨i, y⟩ ∧
      (cycleGraph (fiveFiveThreeThreeSizes i)).Adj x y)
  infer_instance

def fiveFiveThreeThreeSigmaEquiv :
    ((i : Fin 4) × Fin (fiveFiveThreeThreeSizes i)) ≃ Fin 16 :=
  finSigmaFinEquiv.trans (finCongr fiveFiveThreeThreeSizes_sum)

theorem fiveFiveThreeThreeSigmaEquiv_map_adj :
    ∀ z w,
      fiveFiveThreeThreeSigmaGraph.Adj z w ↔
        fiveFiveThreeThreeCycleGraph.Adj
          (fiveFiveThreeThreeSigmaEquiv z)
          (fiveFiveThreeThreeSigmaEquiv w) := by
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

/-- A two-regular graph whose component-size multiset is `[5,5,3,3]`
admits the exact labeling used by the lambda-six census. -/
theorem exists_fiveFiveThreeThreeComponentLabeling_of_componentSizes
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (hdeg : ∀ x, H.degree x = 2)
    (hsizes : (↑[5, 5, 3, 3] : Multiset ℕ) =
      (Finset.univ : Finset H.ConnectedComponent).val.map
        (fun c ↦ c.supp.ncard)) :
    Nonempty (FiveFiveThreeThreeComponentLabeling H) := by
  classical
  obtain ⟨e, he⟩ := exists_equiv_fin_of_multiset_eq_map
    (fun c : H.ConnectedComponent ↦ c.supp.ncard) [5, 5, 3, 3] hsizes
  have hsize : ∀ i : Fin 4,
      (e i).supp.ncard = fiveFiveThreeThreeSizes i := by
    intro i
    calc
      (e i).supp.ncard = [5, 5, 3, 3].get i := he i
      _ = fiveFiveThreeThreeSizes i := by fin_cases i <;> rfl
  have hex : ∀ i : Fin 4,
      ∃ q : Fin (fiveFiveThreeThreeSizes i) ≃ (e i).supp,
        ∀ x y, (cycleGraph (fiveFiveThreeThreeSizes i)).Adj x y ↔
          H.Adj (q x).1 (q y).1 := by
    intro i
    exact exists_componentCycleEquiv H hdeg (e i)
      (fiveFiveThreeThreeSizes i) (hsize i)
  choose q hq using hex
  let coords : (Σ c : H.ConnectedComponent, c.supp) ≃
      ((i : Fin 4) × Fin (fiveFiveThreeThreeSizes i)) :=
    (Equiv.sigmaCongr e q).symm
  let θ : V ≃ Fin 16 :=
    (vertexConnectedComponentEquiv H).trans
      (coords.trans fiveFiveThreeThreeSigmaEquiv)
  refine ⟨⟨θ, ?_⟩⟩
  intro u v
  change H.Adj u v ↔ fiveFiveThreeThreeCycleGraph.Adj
    (fiveFiveThreeThreeSigmaEquiv
      (coords (vertexConnectedComponentEquiv H u)))
    (fiveFiveThreeThreeSigmaEquiv
      (coords (vertexConnectedComponentEquiv H v)))
  rw [← fiveFiveThreeThreeSigmaEquiv_map_adj]
  constructor
  · intro huv
    have hc : H.connectedComponentMk u = H.connectedComponentMk v :=
      ConnectedComponent.connectedComponentMk_eq_of_adj huv
    generalize hzu : coords (vertexConnectedComponentEquiv H u) = zu
    generalize hzv : coords (vertexConnectedComponentEquiv H v) = zv
    have hfirst : zu.1 = zv.1 := by
      rw [← hzu, ← hzv]
      simp [coords, Equiv.sigmaCongr, Equiv.sigmaCongrLeft,
        Equiv.sigmaCongrRight, vertexConnectedComponentEquiv, hc]
    rcases zu with ⟨i, x⟩
    rcases zv with ⟨j, y⟩
    dsimp only at hfirst
    subst j
    simp only [fiveFiveThreeThreeSigmaGraph]
    refine ⟨i, x, y, rfl, rfl, ?_⟩
    have huinv : vertexConnectedComponentEquiv H u =
        coords.symm ⟨i, x⟩ := by
      simpa using congrArg coords.symm hzu
    have hvinv : vertexConnectedComponentEquiv H v =
        coords.symm ⟨i, y⟩ := by
      simpa using congrArg coords.symm hzv
    have huq : (q i x).1 = u := by
      have := congrArg
        (fun z : (Σ c : H.ConnectedComponent, c.supp) => z.2.1) huinv
      change u = (q i x).1 at this
      exact this.symm
    have hvq : (q i y).1 = v := by
      have := congrArg
        (fun z : (Σ c : H.ConnectedComponent, c.supp) => z.2.1) hvinv
      change v = (q i y).1 at this
      exact this.symm
    apply (hq i x y).mpr
    simpa only [huq, hvq] using huv
  · rintro ⟨i, x, y, hx, hy, hxy⟩
    have hcycle := (hq i x y).mp hxy
    have hxu : (q i x).1 = u := by
      have hx' : vertexConnectedComponentEquiv H u =
          coords.symm ⟨i, x⟩ := by
        simpa using congrArg coords.symm hx
      have := congrArg
        (fun z : (Σ c : H.ConnectedComponent, c.supp) => z.2.1) hx'
      have hcoord : (coords.symm ⟨i, x⟩).2.1 = (q i x).1 := by
        rfl
      rw [hcoord] at this
      simpa [vertexConnectedComponentEquiv] using this.symm
    have hyv : (q i y).1 = v := by
      have hy' : vertexConnectedComponentEquiv H v =
          coords.symm ⟨i, y⟩ := by
        simpa using congrArg coords.symm hy
      have := congrArg
        (fun z : (Σ c : H.ConnectedComponent, c.supp) => z.2.1) hy'
      have hcoord : (coords.symm ⟨i, y⟩).2.1 = (q i y).1 := by
        rfl
      rw [hcoord] at this
      simpa [vertexConnectedComponentEquiv] using this.symm
    simpa [hxu, hyv] using hcycle

end

end Erdos85

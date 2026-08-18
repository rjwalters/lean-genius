import Proofs.Erdos85MuThreeKSymmetryClassificationExhaustive
import Proofs.Erdos85MuThreeMixedGridCode

/-! # From factor-cycle compatibility to sector constancy -/

namespace Erdos85

theorem RelationFactorCycleCompatible.edge_status_eq_of_reachable
    {X Y : Type*} (H K : X → Y → Prop)
    (hcycle : RelationFactorCycleCompatible H K)
    {x x' : X} {y y' : Y}
    (hxy : H x y) (hx'y' : H x' y')
    (hreach : (relationBipartiteGraph H).Reachable
      (Sum.inl x) (Sum.inl x')) :
    (K x y ↔ K x' y') := by
  let c := (relationBipartiteGraph H).connectedComponentMk (Sum.inl x)
  have hxc : Sum.inl x ∈ c.supp := by
    change (relationBipartiteGraph H).connectedComponentMk (Sum.inl x) = c
    rfl
  have hx'c : Sum.inl x' ∈ c.supp := by
    change (relationBipartiteGraph H).connectedComponentMk (Sum.inl x') = c
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm
  rcases hcycle c with hall | hnone
  · exact ⟨fun _ => hall x' y' hx'y' hx'c,
      fun _ => hall x y hxy hxc⟩
  · exact ⟨fun hk => absurd hk (hnone x y hxy hxc),
      fun hk => absurd hk (hnone x' y' hx'y' hx'c)⟩

theorem relationBipartiteGraph_left_reachable_of_common_right
    {X Y : Type*} (H : X → Y → Prop) {x x' : X} {y : Y}
    (hxy : H x y) (hx'y : H x' y) :
    (relationBipartiteGraph H).Reachable (Sum.inl x) (Sum.inl x') := by
  have h₁ : (relationBipartiteGraph H).Adj (Sum.inl x) (Sum.inr y) := hxy
  have h₂ : (relationBipartiteGraph H).Adj (Sum.inl x') (Sum.inr y) := hx'y
  exact h₁.reachable.trans h₂.symm.reachable

def mu3HRel (Hrows : Nat → Mu3KRow) : Fin 8 → Fin 8 → Prop :=
  fun x y => y.val ∈ Hrows x.val

instance mu3HRel_decidable (Hrows : Nat → Mu3KRow) :
    DecidableRel (mu3HRel Hrows) := by
  intro x y
  unfold mu3HRel
  infer_instance

theorem mu3H16Rel_reachable_zero (x : Fin 8) :
    (relationBipartiteGraph (mu3HRel mu3H16Row)).Reachable
      (Sum.inl (0 : Fin 8)) (Sum.inl x) := by
  have step (a b y : Fin 8) (ha : mu3HRel mu3H16Row a y)
      (hb : mu3HRel mu3H16Row b y) :=
    relationBipartiteGraph_left_reachable_of_common_right _ ha hb
  have h01 := step 0 1 0 (by decide) (by decide)
  have h12 := step 1 2 1 (by decide) (by decide)
  have h23 := step 2 3 2 (by decide) (by decide)
  have h34 := step 3 4 3 (by decide) (by decide)
  have h45 := step 4 5 4 (by decide) (by decide)
  have h56 := step 5 6 5 (by decide) (by decide)
  have h67 := step 6 7 6 (by decide) (by decide)
  fin_cases x
  · exact .refl _
  · exact h01
  · exact h01.trans h12
  · exact (h01.trans h12).trans h23
  · exact ((h01.trans h12).trans h23).trans h34
  · exact (((h01.trans h12).trans h23).trans h34).trans h45
  · exact ((((h01.trans h12).trans h23).trans h34).trans h45).trans h56
  · exact (((((h01.trans h12).trans h23).trans h34).trans h45).trans h56).trans h67

theorem mu3H88Rel_reachable_representative (x : Fin 8) :
    (relationBipartiteGraph (mu3HRel mu3H88Row)).Reachable
      (Sum.inl (if x.val < 4 then (0 : Fin 8) else (4 : Fin 8)))
      (Sum.inl x) := by
  have step (a b y : Fin 8) (ha : mu3HRel mu3H88Row a y)
      (hb : mu3HRel mu3H88Row b y) :=
    relationBipartiteGraph_left_reachable_of_common_right _ ha hb
  have h01 := step 0 1 0 (by decide) (by decide)
  have h12 := step 1 2 1 (by decide) (by decide)
  have h23 := step 2 3 2 (by decide) (by decide)
  have h45 := step 4 5 4 (by decide) (by decide)
  have h56 := step 5 6 5 (by decide) (by decide)
  have h67 := step 6 7 6 (by decide) (by decide)
  fin_cases x
  · exact .refl _
  · exact h01
  · exact h01.trans h12
  · exact (h01.trans h12).trans h23
  · exact .refl _
  · exact h45
  · exact h45.trans h56
  · exact (h45.trans h56).trans h67

theorem mu3H106Rel_reachable_representative (x : Fin 8) :
    (relationBipartiteGraph (mu3HRel mu3H106Row)).Reachable
      (Sum.inl (if x.val < 5 then (0 : Fin 8) else (5 : Fin 8)))
      (Sum.inl x) := by
  have step (a b y : Fin 8) (ha : mu3HRel mu3H106Row a y)
      (hb : mu3HRel mu3H106Row b y) :=
    relationBipartiteGraph_left_reachable_of_common_right _ ha hb
  have h01 := step 0 1 0 (by decide) (by decide)
  have h12 := step 1 2 1 (by decide) (by decide)
  have h23 := step 2 3 2 (by decide) (by decide)
  have h34 := step 3 4 3 (by decide) (by decide)
  have h56 := step 5 6 5 (by decide) (by decide)
  have h67 := step 6 7 6 (by decide) (by decide)
  fin_cases x
  · exact .refl _
  · exact h01
  · exact h01.trans h12
  · exact (h01.trans h12).trans h23
  · exact ((h01.trans h12).trans h23).trans h34
  · exact .refl _
  · exact h56
  · exact h56.trans h67

theorem exists_mu3KSectorChoice_H16
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hcycle : RelationFactorCycleCompatible (mu3HRel mu3H16Row) K) :
    ∃ sector : Mu3KSectorChoice,
      sector.HRows = mu3H16Row ∧
      ∀ x y, y.val ∈ sector.HRows x.val →
        (K x y ↔ y.val ∈ sector.TRows x.val) := by
  by_cases hk : K 0 0
  · refine ⟨.c16AllTf, rfl, ?_⟩
    intro x y hxy
    have h00 : mu3HRel mu3H16Row 0 0 := by decide
    have hrel := hcycle.edge_status_eq_of_reachable
      (H := mu3HRel mu3H16Row) (K := K) h00 hxy
      (mu3H16Rel_reachable_zero x)
    change K 0 0 ↔ K x y at hrel
    simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows] at hxy ⊢
    exact ⟨fun _ => hxy, fun _ => hrel.mp hk⟩
  · refine ⟨.c16AllTriangle, rfl, ?_⟩
    intro x y hxy
    have h00 : mu3HRel mu3H16Row 0 0 := by decide
    have hrel := hcycle.edge_status_eq_of_reachable
      (H := mu3HRel mu3H16Row) (K := K) h00 hxy
      (mu3H16Rel_reachable_zero x)
    change K 0 0 ↔ K x y at hrel
    simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
      mu3EmptyRows, Finset.notMem_empty, iff_false]
    exact fun hkxy => hk (hrel.mpr hkxy)

end Erdos85

#print axioms Erdos85.RelationFactorCycleCompatible.edge_status_eq_of_reachable
#print axioms Erdos85.mu3H16Rel_reachable_zero
#print axioms Erdos85.mu3H88Rel_reachable_representative
#print axioms Erdos85.mu3H106Rel_reachable_representative
#print axioms Erdos85.exists_mu3KSectorChoice_H16

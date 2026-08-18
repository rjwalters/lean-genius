import Proofs.Erdos85MuThreeKSymmetryClassificationExhaustive
import Proofs.Erdos85MuThreeMixedGridCode

/-! # From factor-cycle compatibility to sector constancy -/

namespace Erdos85

def RelationEdgeStatusComponentwise
    {X Y : Type*} (H K : X → Y → Prop) : Prop :=
  ∀ ⦃x x' : X⦄ ⦃y y' : Y⦄, H x y → H x' y' →
    (relationBipartiteGraph H).Reachable (Sum.inl x) (Sum.inl x') →
      (K x y ↔ K x' y')

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

theorem RelationFactorCycleCompatible.edgeStatusComponentwise
    {X Y : Type*} (H K : X → Y → Prop)
    (hcycle : RelationFactorCycleCompatible H K) :
    RelationEdgeStatusComponentwise H K := by
  intro x x' y y' hxy hx'y' hreach
  exact hcycle.edge_status_eq_of_reachable
    (H := H) (K := K) hxy hx'y' hreach

def mu3NormalizeRelationBipartiteHom
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) :
    relationBipartiteGraph (mu3NormalizeRelation row column H) →g
      relationBipartiteGraph H where
  toFun
    | Sum.inl x => Sum.inl (row.symm x)
    | Sum.inr y => Sum.inr (column.symm y)
  map_rel' := by
    intro a b hab
    cases a <;> cases b <;>
      simp only [relationBipartiteGraph, mu3NormalizeRelation] at hab ⊢
    · exact hab
    · exact hab

theorem RelationEdgeStatusComponentwise.normalize
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) (h : RelationEdgeStatusComponentwise H K) :
    RelationEdgeStatusComponentwise
      (mu3NormalizeRelation row column H)
      (mu3NormalizeRelation row column K) := by
  intro x x' y y' hxy hx'y' hreach
  exact h hxy hx'y'
    (hreach.map (mu3NormalizeRelationBipartiteHom row column H))

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
    (hstatus : RelationEdgeStatusComponentwise (mu3HRel mu3H16Row) K) :
    ∃ sector : Mu3KSectorChoice,
      sector.HRows = mu3H16Row ∧
      ∀ x y, y.val ∈ sector.HRows x.val →
        (K x y ↔ y.val ∈ sector.TRows x.val) := by
  by_cases hk : K 0 0
  · refine ⟨.c16AllTf, rfl, ?_⟩
    intro x y hxy
    have h00 : mu3HRel mu3H16Row 0 0 := by decide
    have hrel := hstatus h00 hxy
      (mu3H16Rel_reachable_zero x)
    change K 0 0 ↔ K x y at hrel
    simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows] at hxy ⊢
    exact ⟨fun _ => hxy, fun _ => hrel.mp hk⟩
  · refine ⟨.c16AllTriangle, rfl, ?_⟩
    intro x y hxy
    have h00 : mu3HRel mu3H16Row 0 0 := by decide
    have hrel := hstatus h00 hxy
      (mu3H16Rel_reachable_zero x)
    change K 0 0 ↔ K x y at hrel
    simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
      mu3EmptyRows, Finset.notMem_empty, iff_false]
    exact fun hkxy => hk (hrel.mpr hkxy)

theorem mu3H88_K_status_iff_representative
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hstatus : RelationEdgeStatusComponentwise (mu3HRel mu3H88Row) K)
    (x y : Fin 8) (hxy : mu3HRel mu3H88Row x y) :
    K (if x.val < 4 then 0 else 4) (if x.val < 4 then 0 else 4) ↔ K x y := by
  have hrep : mu3HRel mu3H88Row
      (if x.val < 4 then 0 else 4) (if x.val < 4 then 0 else 4) := by
    fin_cases x <;> decide
  exact hstatus hrep hxy
    (mu3H88Rel_reachable_representative x)

theorem exists_mu3KSectorChoice_H88
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hstatus : RelationEdgeStatusComponentwise (mu3HRel mu3H88Row) K) :
    ∃ sector : Mu3KSectorChoice,
      sector.HRows = mu3H88Row ∧
      ∀ x y, y.val ∈ sector.HRows x.val →
        (K x y ↔ y.val ∈ sector.TRows x.val) := by
  by_cases hfirst : K 0 0 <;> by_cases hsecond : K 4 4
  · refine ⟨.c88AllTf, rfl, ?_⟩
    intro x y hxy
    have hs := mu3H88_K_status_iff_representative K hstatus x y hxy
    simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows] at hxy ⊢
    refine ⟨fun _ => hxy, fun _ => ?_⟩
    by_cases hx : x.val < 4
    · apply hs.mp
      simpa [hx] using hfirst
    · apply hs.mp
      simpa [hx] using hsecond
  · refine ⟨.c88FirstTf, rfl, ?_⟩
    intro x y hxy
    have hs := mu3H88_K_status_iff_representative K hstatus x y hxy
    by_cases hx : x.val < 4
    · simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
        mu3H88FirstTfRows, if_pos hx]
      exact ⟨fun _ => hxy, fun _ => hs.mp (by simpa [hx] using hfirst)⟩
    · simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
        mu3H88FirstTfRows, if_neg hx, Finset.notMem_empty, iff_false]
      exact fun hkxy => hsecond (by simpa [hx] using hs.mpr hkxy)
  · refine ⟨.c88SecondTf, rfl, ?_⟩
    intro x y hxy
    have hs := mu3H88_K_status_iff_representative K hstatus x y hxy
    by_cases hx : x.val < 4
    · simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
        mu3H88SecondTfRows, if_pos hx, Finset.notMem_empty, iff_false]
      exact fun hkxy => hfirst (by simpa [hx] using hs.mpr hkxy)
    · simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
        mu3H88SecondTfRows, if_neg hx]
      exact ⟨fun _ => hxy, fun _ => hs.mp (by simpa [hx] using hsecond)⟩
  · refine ⟨.c88AllTriangle, rfl, ?_⟩
    intro x y hxy
    have hs := mu3H88_K_status_iff_representative K hstatus x y hxy
    simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
      mu3EmptyRows, Finset.notMem_empty, iff_false]
    intro hkxy
    by_cases hx : x.val < 4
    · exact hfirst (by simpa [hx] using hs.mpr hkxy)
    · exact hsecond (by simpa [hx] using hs.mpr hkxy)

theorem mu3H106_K_status_iff_representative
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hstatus : RelationEdgeStatusComponentwise (mu3HRel mu3H106Row) K)
    (x y : Fin 8) (hxy : mu3HRel mu3H106Row x y) :
    K (if x.val < 5 then 0 else 5) (if x.val < 5 then 0 else 5) ↔ K x y := by
  have hrep : mu3HRel mu3H106Row
      (if x.val < 5 then 0 else 5) (if x.val < 5 then 0 else 5) := by
    fin_cases x <;> decide
  exact hstatus hrep hxy
    (mu3H106Rel_reachable_representative x)

theorem exists_mu3KSectorChoice_H106
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hstatus : RelationEdgeStatusComponentwise (mu3HRel mu3H106Row) K) :
    ∃ sector : Mu3KSectorChoice,
      sector.HRows = mu3H106Row ∧
      ∀ x y, y.val ∈ sector.HRows x.val →
        (K x y ↔ y.val ∈ sector.TRows x.val) := by
  by_cases hten : K 0 0 <;> by_cases hsix : K 5 5
  · refine ⟨.c106AllTf, rfl, ?_⟩
    intro x y hxy
    have hs := mu3H106_K_status_iff_representative K hstatus x y hxy
    simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows] at hxy ⊢
    refine ⟨fun _ => hxy, fun _ => ?_⟩
    by_cases hx : x.val < 5
    · apply hs.mp
      simpa [hx] using hten
    · apply hs.mp
      simpa [hx] using hsix
  · refine ⟨.c106TenTf, rfl, ?_⟩
    intro x y hxy
    have hs := mu3H106_K_status_iff_representative K hstatus x y hxy
    by_cases hx : x.val < 5
    · simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
        mu3H106TenTfRows, if_pos hx]
      exact ⟨fun _ => hxy, fun _ => hs.mp (by simpa [hx] using hten)⟩
    · simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
        mu3H106TenTfRows, if_neg hx, Finset.notMem_empty, iff_false]
      exact fun hkxy => hsix (by simpa [hx] using hs.mpr hkxy)
  · refine ⟨.c106SixTf, rfl, ?_⟩
    intro x y hxy
    have hs := mu3H106_K_status_iff_representative K hstatus x y hxy
    by_cases hx : x.val < 5
    · simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
        mu3H106SixTfRows, if_pos hx, Finset.notMem_empty, iff_false]
      exact fun hkxy => hten (by simpa [hx] using hs.mpr hkxy)
    · simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
        mu3H106SixTfRows, if_neg hx]
      exact ⟨fun _ => hxy, fun _ => hs.mp (by simpa [hx] using hsix)⟩
  · refine ⟨.c106AllTriangle, rfl, ?_⟩
    intro x y hxy
    have hs := mu3H106_K_status_iff_representative K hstatus x y hxy
    simp only [Mu3KSectorChoice.HRows, Mu3KSectorChoice.TRows,
      mu3EmptyRows, Finset.notMem_empty, iff_false]
    intro hkxy
    by_cases hx : x.val < 5
    · exact hten (by simpa [hx] using hs.mpr hkxy)
    · exact hsix (by simpa [hx] using hs.mpr hkxy)

theorem exists_mu3KSectorSelection_H16_of_coordinates
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcycle : RelationFactorCycleCompatible H K)
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H16Row x.val) :
    Nonempty (Mu3KSectorSelection row column H K) := by
  have hHeq : mu3NormalizeRelation row column H = mu3HRel mu3H16Row := by
    funext x y
    exact propext (hHcoord x y)
  have hstatus := (hcycle.edgeStatusComponentwise H K).normalize row column
  rw [hHeq] at hstatus
  obtain ⟨sector, hsectorH, hedge⟩ :=
    exists_mu3KSectorChoice_H16 (mu3NormalizeRelation row column K) hstatus
  refine ⟨{
    sector := sector
    H_coordinate := ?_
    edge_iff := hedge }⟩
  intro x y
  rw [hsectorH]
  exact hHcoord x y

theorem exists_mu3KSectorSelection_H88_of_coordinates
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcycle : RelationFactorCycleCompatible H K)
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H88Row x.val) :
    Nonempty (Mu3KSectorSelection row column H K) := by
  have hHeq : mu3NormalizeRelation row column H = mu3HRel mu3H88Row := by
    funext x y
    exact propext (hHcoord x y)
  have hstatus := (hcycle.edgeStatusComponentwise H K).normalize row column
  rw [hHeq] at hstatus
  obtain ⟨sector, hsectorH, hedge⟩ :=
    exists_mu3KSectorChoice_H88 (mu3NormalizeRelation row column K) hstatus
  refine ⟨{
    sector := sector
    H_coordinate := ?_
    edge_iff := hedge }⟩
  intro x y
  rw [hsectorH]
  exact hHcoord x y

theorem exists_mu3KSectorSelection_H106_of_coordinates
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hcycle : RelationFactorCycleCompatible H K)
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H106Row x.val) :
    Nonempty (Mu3KSectorSelection row column H K) := by
  have hHeq : mu3NormalizeRelation row column H = mu3HRel mu3H106Row := by
    funext x y
    exact propext (hHcoord x y)
  have hstatus := (hcycle.edgeStatusComponentwise H K).normalize row column
  rw [hHeq] at hstatus
  obtain ⟨sector, hsectorH, hedge⟩ :=
    exists_mu3KSectorChoice_H106 (mu3NormalizeRelation row column K) hstatus
  refine ⟨{
    sector := sector
    H_coordinate := ?_
    edge_iff := hedge }⟩
  intro x y
  rw [hsectorH]
  exact hHcoord x y

end Erdos85

#print axioms Erdos85.RelationFactorCycleCompatible.edge_status_eq_of_reachable
#print axioms Erdos85.RelationEdgeStatusComponentwise.normalize
#print axioms Erdos85.mu3H16Rel_reachable_zero
#print axioms Erdos85.mu3H88Rel_reachable_representative
#print axioms Erdos85.mu3H106Rel_reachable_representative
#print axioms Erdos85.exists_mu3KSectorChoice_H16
#print axioms Erdos85.exists_mu3KSectorChoice_H88
#print axioms Erdos85.exists_mu3KSectorChoice_H106
#print axioms Erdos85.exists_mu3KSectorSelection_H16_of_coordinates
#print axioms Erdos85.exists_mu3KSectorSelection_H88_of_coordinates
#print axioms Erdos85.exists_mu3KSectorSelection_H106_of_coordinates

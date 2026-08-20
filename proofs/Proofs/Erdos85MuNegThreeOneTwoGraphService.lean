import Proofs.Erdos85MuNegThreeOneTwoGraphAlgebra
import Proofs.Erdos85SizeTwoMuNegThreeSelfCellOneTwoShape

/-!
# Owner service for the `mu=-3`, `(k,r)=(1,2)` graph endpoint

The diagonal-five shore shape has no within-shore exterior owners.  Hence
the general size-two owner tiling law stays inside the 64 cross owners.  This
file supplies the admissibility and service adapters for the checked CNF.

Node: outline F.3, canonical negative switch endpoint `(-3,1,2)`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- Structural membership law for the normalized cross-owner hit table. -/
theorem mem_muNegThreeHitPairs_iff (a b : Nat) :
    (a, b) ∈ muNegThreeHitPairs ↔
      a < 64 ∧ b < 64 ∧ a < b ∧ muNegThreeAdm a b = true := by
  unfold muNegThreeHitPairs
  constructor
  · intro h
    simp only [List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨a', ha', b', ⟨⟨hb', hab, hadm⟩, heq⟩⟩ := h
    rw [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨ha', hb', hab, hadm⟩
  · rintro ⟨ha, hb, hab, hadm⟩
    simp only [List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨a, ha, b, ⟨⟨hb, hab, hadm⟩, rfl⟩⟩

private theorem muNegThreeOffsetOne_iff_zmod
    {x y : Nat} (hx : x < 8) (hy : y < 8)
    : muNegThreeOffsetOne x y = true ↔
    (y : ZMod 8) = (x : ZMod 8) - 1 ∨
      (y : ZMod 8) = (x : ZMod 8) + 1 := by
  interval_cases x <;> interval_cases y <;> decide

/-- An endpoint of one realized cross owner cannot be ambient-adjacent to
an endpoint of an owner-vertex-adjacent partner. -/
theorem muNegThree_no_cross_endpoint_edge
    (hfree : ¬ containsC4 V G)
    (u v : ZMod 8 → c.supp)
    {a b : Nat} {ta tb : V}
    (hta : MuNegThreeOwnerVertex G c u v a ta)
    (htb : MuNegThreeOwnerVertex G c u v b tb)
    (hadj : G.Adj ta tb)
    {x y : V}
    (hx : x = (muNegThreeOwnerEndpoints G c u v a).1 ∨
      x = (muNegThreeOwnerEndpoints G c u v a).2)
    (hy : y = (muNegThreeOwnerEndpoints G c u v b).1 ∨
      y = (muNegThreeOwnerEndpoints G c u v b).2) :
    ¬ G.Adj x y := by
  intro hxy
  have htax : G.Adj ta x := by
    rcases hx with rfl | rfl
    · exact hta.2.1.symm
    · exact hta.2.2.symm
  have htby : G.Adj tb y := by
    rcases hy with rfl | rfl
    · exact htb.2.1.symm
    · exact htb.2.2.symm
  have hne : ta ≠ y := by
    intro h
    apply hta.1
    rw [h]
    rcases hy with rfl | rfl
    · exact (u _).2
    · exact (v _).2
  have heq := commonServer_unique G hfree hne
    htax hxy.symm hadj htby.symm
  apply htb.1
  rw [← heq]
  rcases hx with rfl | rfl
  · exact (u _).2
  · exact (v _).2

/-- Adjacent realized cross owners satisfy the generator's admissibility
predicate: their row endpoints and column endpoints are both nonconsecutive.
-/
theorem muNegThreeAdm_of_ownerVertices_adj
    (hfree : ¬ containsC4 V G)
    (u v : ZMod 8 → c.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {a b : Nat} (ha : a < 64) (hb : b < 64) (hab : a ≠ b)
    {ta tb : V}
    (hta : MuNegThreeOwnerVertex G c u v a ta)
    (htb : MuNegThreeOwnerVertex G c u v b tb)
    (hadj : G.Adj ta tb) :
    muNegThreeAdm a b = true := by
  have hra : muNegThreeCellRow a < 8 := by
    simp [muNegThreeCellRow]
    omega
  have hrb : muNegThreeCellRow b < 8 := by
    simp [muNegThreeCellRow]
    omega
  have hca : muNegThreeCellCol a < 8 := by
    exact Nat.mod_lt _ (by omega)
  have hcb : muNegThreeCellCol b < 8 := by
    exact Nat.mod_lt _ (by omega)
  have hrow : muNegThreeOffsetOne (muNegThreeCellRow a)
      (muNegThreeCellRow b) = false := by
    apply Bool.eq_false_iff.mpr
    intro hoff
    obtain hminus | hplus :=
      (muNegThreeOffsetOne_iff_zmod hra hrb).mp hoff
    · exact muNegThree_no_cross_endpoint_edge G c hfree u v hta htb hadj
        (Or.inl rfl) (Or.inl rfl) (by
          change G.Adj (u (muNegThreeCellRow a : ZMod 8)).1
            (u (muNegThreeCellRow b : ZMod 8)).1
          rw [← G.induce_adj]
          rw [← (G.induce c.supp).mem_neighborFinset, hu]
          simp [hminus])
    · exact muNegThree_no_cross_endpoint_edge G c hfree u v hta htb hadj
        (Or.inl rfl) (Or.inl rfl) (by
          change G.Adj (u (muNegThreeCellRow a : ZMod 8)).1
            (u (muNegThreeCellRow b : ZMod 8)).1
          rw [← G.induce_adj]
          rw [← (G.induce c.supp).mem_neighborFinset, hu]
          simp [hplus])
  have hcol : muNegThreeOffsetOne (muNegThreeCellCol a)
      (muNegThreeCellCol b) = false := by
    apply Bool.eq_false_iff.mpr
    intro hoff
    obtain hminus | hplus :=
      (muNegThreeOffsetOne_iff_zmod hca hcb).mp hoff
    · exact muNegThree_no_cross_endpoint_edge G c hfree u v hta htb hadj
        (Or.inr rfl) (Or.inr rfl) (by
          change G.Adj (v (muNegThreeCellCol a : ZMod 8)).1
            (v (muNegThreeCellCol b : ZMod 8)).1
          rw [← G.induce_adj]
          rw [← (G.induce c.supp).mem_neighborFinset, hv]
          simp [hminus])
    · exact muNegThree_no_cross_endpoint_edge G c hfree u v hta htb hadj
        (Or.inr rfl) (Or.inr rfl) (by
          change G.Adj (v (muNegThreeCellCol a : ZMod 8)).1
            (v (muNegThreeCellCol b : ZMod 8)).1
          rw [← G.induce_adj]
          rw [← (G.induce c.supp).mem_neighborFinset, hv]
          simp [hplus])
  simp [muNegThreeAdm, hab, hrow, hcol]

/-- Adjacent realized cross owners give one of the generated normalized hit
keys, independently of their input order. -/
theorem mem_muNegThreeHitPairs_of_ownerVertices_adj
    (hfree : ¬ containsC4 V G)
    (u v : ZMod 8 → c.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    {a b : Nat} (ha : a < 64) (hb : b < 64) (hab : a ≠ b)
    {ta tb : V}
    (hta : MuNegThreeOwnerVertex G c u v a ta)
    (htb : MuNegThreeOwnerVertex G c u v b tb)
    (hadj : G.Adj ta tb) :
    (min a b, max a b) ∈ muNegThreeHitPairs := by
  rw [mem_muNegThreeHitPairs_iff]
  have hadm := muNegThreeAdm_of_ownerVertices_adj G c hfree u v hu hv
    ha hb hab hta htb hadj
  rcases Nat.lt_or_gt_of_ne hab with hablt | hbalt
  · simpa [Nat.min_eq_left (Nat.le_of_lt hablt),
      Nat.max_eq_right (Nat.le_of_lt hablt)] using
        (show a < 64 ∧ b < 64 ∧ a < b ∧ muNegThreeAdm a b = true from
          ⟨ha, hb, hablt, hadm⟩)
  · have hadm' := muNegThreeAdm_of_ownerVertices_adj G c hfree u v hu hv
      hb ha hab.symm htb hta hadj.symm
    simpa [Nat.min_eq_right (Nat.le_of_lt hbalt),
      Nat.max_eq_left (Nat.le_of_lt hbalt)] using
        (show b < 64 ∧ a < 64 ∧ b < a ∧ muNegThreeAdm b a = true from
          ⟨hb, ha, hbalt, hadm'⟩)

/-- Every active cross cell has its unique exterior owner vertex.  Distinct
internal shores rule out an internal common neighbor of the endpoints. -/
theorem muNegThreeOwnerVertex_of_active
    (hfree : ¬ containsC4 V G)
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp)
    {a : Nat} (ha : a < 64)
    (hactive : muNegThreeOwnerActive
      (muNegThreeCrossDefectRel G c u v) a = true) :
    ∃ t : V, MuNegThreeOwnerVertex G c u v a t := by
  rw [muNegThreeOwnerActive_graph_iff] at hactive
  let i : ZMod 8 := muNegThreeCellRow a
  let j : ZMod 8 := muNegThreeCellCol a
  have hui : u i ∈ ca.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hvj : v j ∈ cb.supp := by
    rw [← hvrange]
    exact ⟨j, rfl⟩
  obtain ⟨t, htout, hut, hvt, _huniq⟩ :=
    nonDefect_ownerVertex_exterior G hfree c
      (muNegThreeOwnerEndpoints_ne G c ca cb hcab u v hurange hvrange a)
      hactive (by
        intro z hzc hz
        let zc : c.supp := ⟨z, hzc⟩
        have huz : (G.induce c.supp).Adj (u i) zc := hz.1
        have hvz : (G.induce c.supp).Adj (v j) zc := hz.2
        have huca : (G.induce c.supp).connectedComponentMk (u i) = ca :=
          (ConnectedComponent.mem_supp_iff ca (u i)).mp hui
        have hvcb : (G.induce c.supp).connectedComponentMk (v j) = cb :=
          (ConnectedComponent.mem_supp_iff cb (v j)).mp hvj
        have hzCa : zc ∈ ca.supp :=
          (ConnectedComponent.mem_supp_iff ca zc).mpr
            ((ConnectedComponent.connectedComponentMk_eq_of_adj huz).symm.trans
              huca)
        have hzCb : zc ∈ cb.supp :=
          (ConnectedComponent.mem_supp_iff cb zc).mpr
            ((ConnectedComponent.connectedComponentMk_eq_of_adj hvz).symm.trans
              hvcb)
        exact hcab (ConnectedComponent.eq_of_common_vertex hzCa hzCb))
  exact ⟨t, htout, hut, hvt⟩

private theorem muNegThree_sameShore_not_adj_of_not_offset
    (w : ZMod 8 → c.supp)
    (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)})
    {x y : Nat} (hx : x < 8) (hy : y < 8)
    (hoff : muNegThreeOffsetOne x y = false) :
    ¬ G.Adj (w (x : ZMod 8)).1 (w (y : ZMod 8)).1 := by
  intro hadj
  have hadjH : (G.induce c.supp).Adj
      (w (x : ZMod 8)) (w (y : ZMod 8)) := hadj
  have hmem := ((G.induce c.supp).mem_neighborFinset _ _).mpr hadjH
  rw [hw] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hcoords : (y : ZMod 8) = (x : ZMod 8) - 1 ∨
      (y : ZMod 8) = (x : ZMod 8) + 1 := by
    rcases hmem with h | h
    · exact Or.inl (hwinj h)
    · exact Or.inr (hwinj h)
  have hone : muNegThreeOffsetOne x y = true :=
    (muNegThreeOffsetOne_iff_zmod hx hy).mpr hcoords
  rw [hoff] at hone
  contradiction

private theorem muNegThree_crossShore_not_adj
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp)
    (i j : ZMod 8) : ¬ G.Adj (u i).1 (v j).1 := by
  intro hadj
  have hui : u i ∈ ca.supp := by rw [← hurange]; exact ⟨i, rfl⟩
  have hvj : v j ∈ cb.supp := by rw [← hvrange]; exact ⟨j, rfl⟩
  have huca : (G.induce c.supp).connectedComponentMk (u i) = ca :=
    (ConnectedComponent.mem_supp_iff ca (u i)).mp hui
  have hvcb : (G.induce c.supp).connectedComponentMk (v j) = cb :=
    (ConnectedComponent.mem_supp_iff cb (v j)).mp hvj
  have huv : (G.induce c.supp).connectedComponentMk (u i) =
      (G.induce c.supp).connectedComponentMk (v j) :=
    ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  exact hcab (huca.symm.trans (huv.trans hvcb))

/-- Tiling classification for a row target: the unique server is exterior,
has one endpoint on each shore, and therefore realizes another cross owner. -/
theorem muNegThree_row_server_classification
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (huout : ∀ z, z ∉ c.supp → ∃! i : ZMod 8, G.Adj (u i).1 z)
    (hvout : ∀ z, z ∉ c.supp → ∃! j : ZMod 8, G.Adj (v j).1 z)
    {a : Nat} (ha : a < 64) {ta : V}
    (hta : MuNegThreeOwnerVertex G c u v a ta)
    {t : Nat} (ht : t < 8)
    (hoff : muNegThreeOffsetOne (muNegThreeCellRow a) t = false) :
    ∃ b, b < 64 ∧ b ≠ a ∧ muNegThreeCellRow b = t ∧
      (min a b, max a b) ∈ muNegThreeHitPairs ∧
      muNegThreeOwnerHitRel G c u v (min a b) (max a b) = true := by
  have htaComp : (secondOrderDefectGraph G).connectedComponentMk ta ≠ c := by
    intro h
    exact hta.1 ((ConnectedComponent.mem_supp_iff c ta).mpr h)
  have hutComp : (secondOrderDefectGraph G).connectedComponentMk
      (u (t : ZMod 8)).1 = c :=
    (ConnectedComponent.mem_supp_iff c (u (t : ZMod 8)).1).mp (u _).2
  obtain ⟨z, ⟨htaz, hzut⟩, _hzuniq⟩ :=
    binarySquare_regular_sizeTwoPart_exteriorOwner_unique_server
      G hfree (by omega) hreg hcard c hsize htaComp hutComp
  have hzout : z ∉ c.supp := by
    intro hzc
    have hzmem := sizeTwoPart_server_mem_tile_of_internal G c htaz hzc
    have hpair := sizeTwoPart_tile_eq_pair G hfree (by omega : 3 ≤ 8)
      hreg hcard c hsize
      (muNegThreeOwnerEndpoints_ne G c ca cb hcab u v hurange hvrange a)
      (u (muNegThreeCellRow a : ZMod 8)).2
      (v (muNegThreeCellCol a : ZMod 8)).2
      hta.2.1.symm hta.2.2.symm
    rw [hpair] at hzmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with hz | hz
    · have hz' : z = (u (muNegThreeCellRow a : ZMod 8)).1 := hz
      rw [hz'] at hzut
      exact muNegThree_sameShore_not_adj_of_not_offset G c u huinj hu
        (by simp [muNegThreeCellRow]; omega) ht hoff hzut
    · have hz' : z = (v (muNegThreeCellCol a : ZMod 8)).1 := hz
      rw [hz'] at hzut
      exact muNegThree_crossShore_not_adj G c ca cb hcab u v
        hurange hvrange _ _ hzut.symm
  obtain ⟨i, hiz, hiuniq⟩ := huout z hzout
  obtain ⟨j, hjz, _hjuniq⟩ := hvout z hzout
  have hit : i = (t : ZMod 8) := (hiuniq _ hzut.symm).symm
  let b : Nat := t * 8 + j.val
  have hb : b < 64 := by
    dsimp [b]
    have := j.val_lt
    omega
  have hbrow : muNegThreeCellRow b = t := by
    change (t * 8 + j.val) / 8 = t
    rw [Nat.mul_comm t 8, Nat.mul_add_div (by omega)]
    simp [Nat.div_eq_of_lt j.val_lt]
  have hbcol : muNegThreeCellCol b = j.val := by
    change (t * 8 + j.val) % 8 = j.val
    rw [Nat.mul_comm t 8, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt j.val_lt
  have htb : MuNegThreeOwnerVertex G c u v b z := by
    refine ⟨hzout, ?_, ?_⟩
    · simp only [muNegThreeOwnerEndpoints, hbrow]
      rw [← hit]
      exact hiz
    · simp only [muNegThreeOwnerEndpoints, hbcol,
        ZMod.natCast_zmod_val]
      exact hjz
  have hba : b ≠ a := by
    intro h
    have htb' : MuNegThreeOwnerVertex G c u v a z := h ▸ htb
    have hzt := muNegThreeOwnerVertex_unique G c hfree ca cb hcab u v
      hurange hvrange a htb' hta
    rw [hzt] at htaz
    exact G.irrefl htaz
  have hkey := mem_muNegThreeHitPairs_of_ownerVertices_adj G c hfree u v
    hu hv ha hb hba.symm hta htb htaz
  refine ⟨b, hb, hba, hbrow, hkey, ?_⟩
  rw [muNegThreeOwnerHitRel_eq_true]
  rcases Nat.le_total a b with hab | hba'
  · rw [Nat.min_eq_left hab, Nat.max_eq_right hab]
    exact ⟨ta, z, hta, htb, htaz⟩
  · rw [Nat.min_eq_right hba', Nat.max_eq_left hba']
    exact ⟨z, ta, htb, hta, htaz.symm⟩

/-- Column-symmetric tiling classification. -/
theorem muNegThree_column_server_classification
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (huout : ∀ z, z ∉ c.supp → ∃! i : ZMod 8, G.Adj (u i).1 z)
    (hvout : ∀ z, z ∉ c.supp → ∃! j : ZMod 8, G.Adj (v j).1 z)
    {a : Nat} (ha : a < 64) {ta : V}
    (hta : MuNegThreeOwnerVertex G c u v a ta)
    {t : Nat} (ht : t < 8)
    (hoff : muNegThreeOffsetOne (muNegThreeCellCol a) t = false) :
    ∃ b, b < 64 ∧ b ≠ a ∧ muNegThreeCellCol b = t ∧
      (min a b, max a b) ∈ muNegThreeHitPairs ∧
      muNegThreeOwnerHitRel G c u v (min a b) (max a b) = true := by
  have htaComp : (secondOrderDefectGraph G).connectedComponentMk ta ≠ c := by
    intro h
    exact hta.1 ((ConnectedComponent.mem_supp_iff c ta).mpr h)
  have hvtComp : (secondOrderDefectGraph G).connectedComponentMk
      (v (t : ZMod 8)).1 = c :=
    (ConnectedComponent.mem_supp_iff c (v (t : ZMod 8)).1).mp (v _).2
  obtain ⟨z, ⟨htaz, hzvt⟩, _hzuniq⟩ :=
    binarySquare_regular_sizeTwoPart_exteriorOwner_unique_server
      G hfree (by omega) hreg hcard c hsize htaComp hvtComp
  have hzout : z ∉ c.supp := by
    intro hzc
    have hzmem := sizeTwoPart_server_mem_tile_of_internal G c htaz hzc
    have hpair := sizeTwoPart_tile_eq_pair G hfree (by omega : 3 ≤ 8)
      hreg hcard c hsize
      (muNegThreeOwnerEndpoints_ne G c ca cb hcab u v hurange hvrange a)
      (u (muNegThreeCellRow a : ZMod 8)).2
      (v (muNegThreeCellCol a : ZMod 8)).2
      hta.2.1.symm hta.2.2.symm
    rw [hpair] at hzmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with hz | hz
    · have hz' : z = (u (muNegThreeCellRow a : ZMod 8)).1 := hz
      rw [hz'] at hzvt
      exact muNegThree_crossShore_not_adj G c ca cb hcab u v
        hurange hvrange _ _ hzvt
    · have hz' : z = (v (muNegThreeCellCol a : ZMod 8)).1 := hz
      rw [hz'] at hzvt
      exact muNegThree_sameShore_not_adj_of_not_offset G c v hvinj hv
        (Nat.mod_lt _ (by omega)) ht hoff hzvt
  obtain ⟨i, hiz, _hiuniq⟩ := huout z hzout
  obtain ⟨j, hjz, hjuniq⟩ := hvout z hzout
  have hjt : j = (t : ZMod 8) := (hjuniq _ hzvt.symm).symm
  let b : Nat := i.val * 8 + t
  have hb : b < 64 := by
    dsimp [b]
    have := i.val_lt
    omega
  have hbrow : muNegThreeCellRow b = i.val := by
    change (i.val * 8 + t) / 8 = i.val
    rw [Nat.mul_comm i.val 8, Nat.mul_add_div (by omega)]
    simp [Nat.div_eq_of_lt ht]
  have hbcol : muNegThreeCellCol b = t := by
    change (i.val * 8 + t) % 8 = t
    rw [Nat.mul_comm i.val 8, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt ht
  have htb : MuNegThreeOwnerVertex G c u v b z := by
    refine ⟨hzout, ?_, ?_⟩
    · simp only [muNegThreeOwnerEndpoints, hbrow,
        ZMod.natCast_zmod_val]
      exact hiz
    · simp only [muNegThreeOwnerEndpoints, hbcol]
      rw [← hjt]
      exact hjz
  have hba : b ≠ a := by
    intro h
    have htb' : MuNegThreeOwnerVertex G c u v a z := h ▸ htb
    have hzt := muNegThreeOwnerVertex_unique G c hfree ca cb hcab u v
      hurange hvrange a htb' hta
    rw [hzt] at htaz
    exact G.irrefl htaz
  have hkey := mem_muNegThreeHitPairs_of_ownerVertices_adj G c hfree u v
    hu hv ha hb hba.symm hta htb htaz
  refine ⟨b, hb, hba, hbcol, hkey, ?_⟩
  rw [muNegThreeOwnerHitRel_eq_true]
  rcases Nat.le_total a b with hab | hba'
  · rw [Nat.min_eq_left hab, Nat.max_eq_right hab]
    exact ⟨ta, z, hta, htb, htaz⟩
  · rw [Nat.min_eq_right hba', Nat.max_eq_left hba']
    exact ⟨z, ta, htb, hta, htaz.symm⟩

end

end Erdos85

#print axioms Erdos85.mem_muNegThreeHitPairs_of_ownerVertices_adj

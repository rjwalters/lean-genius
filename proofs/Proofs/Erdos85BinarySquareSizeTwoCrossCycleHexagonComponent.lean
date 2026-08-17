import Proofs.Erdos85BinarySquareSizeTwoCrossCycleClosedHexagon
import Proofs.Erdos85BinarySquareSizeTwoCrossBipartiteCycles

/-! # Closed cross hexagons are connected components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A set closed under taking graph neighbors contains the whole connected
component of each of its vertices. -/
theorem connectedComponentMk_supp_subset_of_neighbor_closed
    {W : Type*} (H : SimpleGraph W) {S : Set W} {v : W}
    (hv : v ∈ S) (hclosed : ∀ u ∈ S, H.neighborSet u ⊆ S) :
    (H.connectedComponentMk v).supp ⊆ S := by
  have walk_end_mem : ∀ {u w : W} (p : H.Walk u w), u ∈ S → w ∈ S := by
    intro u w p
    induction p with
    | nil => exact fun hu => hu
    | @cons u t w hut p ih =>
        intro hu
        exact ih (hclosed u hu hut)
  intro w hw
  have hr : H.Reachable v w :=
    ConnectedComponent.exact
      ((ConnectedComponent.mem_supp_iff (H.connectedComponentMk v) w).mp hw).symm
  exact hr.elim fun p => walk_end_mem p hv

/-- Every triangle in a restricted owner factor supplies an actual
six-vertex connected component of the associated cross graph. -/
theorem binarySquare_regular_twoSizeTwoParts_ownerTriangle_exists_crossComponent_order_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2)
    (x y z : source.supp) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (htri : (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).Adj y z ∧
      (restrictedComponentOwnerGraph G source target).Adj z x) :
    ∃ e : (componentCrossBipartiteGraph G source target).ConnectedComponent,
      e.supp.ncard = 6 := by
  classical
  let H := componentCrossBipartiteGraph G source target
  obtain ⟨a, b, c, hab, hbc, hca, hx, hy, hz, ha, hb, hc⟩ :=
    (binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_iff_closedHexagon
      G hfree hq hreg hcard source target hsource htarget x y z
      hxy hyz hzx).mp htri
  let T : Finset (source.supp ⊕ target.supp) :=
    {Sum.inl x, Sum.inr a, Sum.inl y, Sum.inr b, Sum.inl z, Sum.inr c}
  have hclosed : ∀ u ∈ (T : Set (source.supp ⊕ target.supp)),
      H.neighborSet u ⊆ (T : Set (source.supp ⊕ target.supp)) := by
    intro u hu v huv
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hu ⊢
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · cases v with
      | inl w => simp [H, componentCrossBipartiteGraph] at huv
      | inr w =>
          have hw : w ∈ componentCrossNeighborFinset G target x :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩
          rw [hx] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> simp
    · cases v with
      | inl w =>
          have hwa : G.Adj w.1 a.1 := huv
          have hw : w ∈ componentCrossNeighborFinset G source a :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwa.symm⟩
          rw [ha] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> simp
      | inr w => simp [H, componentCrossBipartiteGraph] at huv
    · cases v with
      | inl w => simp [H, componentCrossBipartiteGraph] at huv
      | inr w =>
          have hw : w ∈ componentCrossNeighborFinset G target y :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩
          rw [hy] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> simp
    · cases v with
      | inl w =>
          have hwb : G.Adj w.1 b.1 := huv
          have hw : w ∈ componentCrossNeighborFinset G source b :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwb.symm⟩
          rw [hb] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> simp
      | inr w => simp [H, componentCrossBipartiteGraph] at huv
    · cases v with
      | inl w => simp [H, componentCrossBipartiteGraph] at huv
      | inr w =>
          have hw : w ∈ componentCrossNeighborFinset G target z :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩
          rw [hz] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> simp
    · cases v with
      | inl w =>
          have hwc : G.Adj w.1 c.1 := huv
          have hw : w ∈ componentCrossNeighborFinset G source c :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwc.symm⟩
          rw [hc] at hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl <;> simp
      | inr w => simp [H, componentCrossBipartiteGraph] at huv
  let e := H.connectedComponentMk (Sum.inl x)
  have hsub : e.supp ⊆ (T : Set (source.supp ⊕ target.supp)) :=
    connectedComponentMk_supp_subset_of_neighbor_closed H (by simp [T]) hclosed
  have hxa : H.Adj (Sum.inl x) (Sum.inr a) := by
    have : a ∈ componentCrossNeighborFinset G target x := by rw [hx]; simp
    exact (Finset.mem_filter.mp this).2
  have hay : H.Adj (Sum.inr a) (Sum.inl y) := by
    have : y ∈ componentCrossNeighborFinset G source a := by rw [ha]; simp
    have h := (Finset.mem_filter.mp this).2
    exact h.symm
  have hyb : H.Adj (Sum.inl y) (Sum.inr b) := by
    have : b ∈ componentCrossNeighborFinset G target y := by rw [hy]; simp
    exact (Finset.mem_filter.mp this).2
  have hbz : H.Adj (Sum.inr b) (Sum.inl z) := by
    have : z ∈ componentCrossNeighborFinset G source b := by rw [hb]; simp
    exact (Finset.mem_filter.mp this).2.symm
  have hzc : H.Adj (Sum.inl z) (Sum.inr c) := by
    have : c ∈ componentCrossNeighborFinset G target z := by rw [hz]; simp
    exact (Finset.mem_filter.mp this).2
  have hTsub : (T : Set (source.supp ⊕ target.supp)) ⊆ e.supp := by
    intro v hv
    simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ConnectedComponent.connectedComponentMk_mem
    · exact (ConnectedComponent.mem_supp_iff e _).mpr
        (ConnectedComponent.connectedComponentMk_eq_of_adj hxa).symm
    · exact (ConnectedComponent.mem_supp_iff e _).mpr
        ((ConnectedComponent.connectedComponentMk_eq_of_adj hay).symm.trans
          (ConnectedComponent.connectedComponentMk_eq_of_adj hxa).symm)
    · exact (ConnectedComponent.mem_supp_iff e _).mpr
        ((ConnectedComponent.connectedComponentMk_eq_of_adj hyb).symm.trans
          ((ConnectedComponent.connectedComponentMk_eq_of_adj hay).symm.trans
            (ConnectedComponent.connectedComponentMk_eq_of_adj hxa).symm))
    · exact (ConnectedComponent.mem_supp_iff e _).mpr
        ((ConnectedComponent.connectedComponentMk_eq_of_adj hbz).symm.trans
          ((ConnectedComponent.connectedComponentMk_eq_of_adj hyb).symm.trans
            ((ConnectedComponent.connectedComponentMk_eq_of_adj hay).symm.trans
              (ConnectedComponent.connectedComponentMk_eq_of_adj hxa).symm)))
    · exact (ConnectedComponent.mem_supp_iff e _).mpr
        ((ConnectedComponent.connectedComponentMk_eq_of_adj hzc).symm.trans
          ((ConnectedComponent.connectedComponentMk_eq_of_adj hbz).symm.trans
            ((ConnectedComponent.connectedComponentMk_eq_of_adj hyb).symm.trans
              ((ConnectedComponent.connectedComponentMk_eq_of_adj hay).symm.trans
                (ConnectedComponent.connectedComponentMk_eq_of_adj hxa).symm))))
  refine ⟨e, ?_⟩
  have heq : e.supp = (T : Set (source.supp ⊕ target.supp)) :=
    Set.Subset.antisymm hsub hTsub
  rw [heq, Set.ncard_coe_finset]
  simp only [T]
  rw [Finset.card_insert_of_notMem (by
      intro hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h | h
      · cases h
      · exact hxy (Sum.inl.inj h)
      · cases h
      · exact hzx (Sum.inl.inj h).symm
      · cases h),
    Finset.card_insert_of_notMem (by
      intro hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h
      · cases h
      · exact hab (Sum.inr.inj h)
      · cases h
      · exact hca (Sum.inr.inj h).symm),
    Finset.card_insert_of_notMem (by simp [hyz]),
    Finset.card_insert_of_notMem (by simp [hbc]),
    Finset.card_insert_of_notMem (by simp)]
  simp

end

end Erdos85

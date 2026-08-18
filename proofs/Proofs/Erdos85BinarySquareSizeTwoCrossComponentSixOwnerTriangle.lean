import Proofs.Erdos85BinarySquareSizeTwoCrossOwnerComponentSize

/-! # Six-vertex cross components give owner triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Any two distinct vertices in a three-vertex component of a two-regular
graph are adjacent. -/
theorem twoRegular_component_order_three_adj_local
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (hdeg : ∀ v, F.degree v = 2)
    (a : F.ConnectedComponent) (ha : a.supp.ncard = 3)
    {x y : W} (hx : x ∈ a.supp) (hy : y ∈ a.supp) (hxy : x ≠ y) :
    F.Adj x y := by
  classical
  let S := a.supp.toFinite.toFinset
  have hxS : x ∈ S := by simpa [S] using hx
  have hyS : y ∈ S := by simpa [S] using hy
  have hNsub : F.neighborFinset x ⊆ S.erase x := by
    intro z hz
    have hxz : F.Adj x z := (F.mem_neighborFinset x z).mp hz
    have hzSupp : z ∈ a.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      calc
        F.connectedComponentMk z = F.connectedComponentMk x :=
          (ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm
        _ = a := (ConnectedComponent.mem_supp_iff a x).mp hx
    exact Finset.mem_erase.mpr
      ⟨(F.ne_of_adj hxz).symm, by simpa [S] using hzSupp⟩
  have hNcard : (F.neighborFinset x).card = 2 := by
    rw [F.card_neighborFinset_eq_degree, hdeg]
  have hScard : S.card = 3 := by
    simpa [S] using
      (Set.ncard_eq_toFinset_card a.supp a.supp.toFinite).symm.trans ha
  have hEraseCard : (S.erase x).card = 2 := by
    rw [Finset.card_erase_of_mem hxS, hScard]
  have heq : F.neighborFinset x = S.erase x := by
    apply Finset.eq_of_subset_of_card_le hNsub
    rw [hNcard, hEraseCard]
  apply (F.mem_neighborFinset x y).mp
  rw [heq]
  exact Finset.mem_erase.mpr ⟨hxy.symm, hyS⟩

/-- A three-vertex component of a two-regular graph contains a triangle. -/
theorem twoRegular_component_order_three_exists_triangle
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (hdeg : ∀ v, F.degree v = 2)
    (a : F.ConnectedComponent) (ha : a.supp.ncard = 3) :
    ∃ x y z : W,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      x ∈ a.supp ∧ y ∈ a.supp ∧ z ∈ a.supp ∧
      F.Adj x y ∧ F.Adj y z ∧ F.Adj z x := by
  classical
  let S := a.supp.toFinite.toFinset
  have hcard : S.card = 3 := by
    simpa [S] using
      (Set.ncard_eq_toFinset_card a.supp a.supp.toFinite).symm.trans ha
  obtain ⟨x, y, z, hxy, hxz, hyz, hset⟩ := Finset.card_eq_three.mp hcard
  have hxS : x ∈ S := by rw [hset]; simp
  have hyS : y ∈ S := by rw [hset]; simp
  have hzS : z ∈ S := by rw [hset]; simp
  have hx : x ∈ a.supp := by
    simpa [S] using hxS
  have hy : y ∈ a.supp := by
    simpa [S] using hyS
  have hz : z ∈ a.supp := by
    simpa [S] using hzS
  refine ⟨x, y, z, hxy, hyz, hxz.symm, hx, hy, hz, ?_, ?_, ?_⟩
  · exact twoRegular_component_order_three_adj_local F hdeg a ha hx hy hxy
  · exact twoRegular_component_order_three_adj_local F hdeg a ha hy hz hyz
  · exact twoRegular_component_order_three_adj_local F hdeg a ha hz hx hxz.symm

/-- Conversely to the closed-hexagon construction, every order-six cross
component corresponds to a triangle in the restricted owner factor. -/
theorem binarySquare_regular_twoSizeTwoParts_crossComponent_order_six_exists_ownerTriangle
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
    (e : (componentCrossBipartiteGraph G source target).ConnectedComponent)
    (he : e.supp.ncard = 6) :
    ∃ x y z : source.supp,
      x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).Adj y z ∧
      (restrictedComponentOwnerGraph G source target).Adj z x ∧
      (componentCrossBipartiteGraph G source target).connectedComponentMk
        (Sum.inl x) = e := by
  let F := restrictedComponentOwnerGraph G source target
  let E := binarySquare_regular_twoSizeTwoParts_restrictedOwnerComponentEquivCross
    G hfree hq hreg hcard source target hsource
  let a : F.ConnectedComponent := E.symm e
  have hmap : restrictedOwnerComponentToCross G hfree source target a = e := by
    exact E.apply_symm_apply e
  have hdouble :=
    binarySquare_regular_twoSizeTwoParts_crossComponent_ncard_eq_two_mul_owner
      G hfree hq hreg hcard source target hsource htarget a
  rw [hmap, he] at hdouble
  have ha : a.supp.ncard = 3 := by omega
  have hdeg : ∀ x, F.degree x = 2 :=
    binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree hq hreg hcard source target hsource htarget
  obtain ⟨x, y, z, hxy, hyz, hzx, hx, _hy, _hz, hxyAdj, hyzAdj, hzxAdj⟩ :=
    twoRegular_component_order_three_exists_triangle F hdeg a ha
  refine ⟨x, y, z, hxy, hyz, hzx, hxyAdj, hyzAdj, hzxAdj, ?_⟩
  have hxa : F.connectedComponentMk x = a :=
    (ConnectedComponent.mem_supp_iff a x).mp hx
  rw [← hmap, ← hxa]
  rfl

end

end Erdos85

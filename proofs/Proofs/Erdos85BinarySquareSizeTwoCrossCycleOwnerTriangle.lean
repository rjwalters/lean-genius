import Proofs.Erdos85BinarySquareSizeTwoCrossBlockNoRectangle

/-! # Alternating six-cycles and owner-factor triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Three distinct source rows form a triangle in a restricted owner factor
exactly when their three pairwise intersections are witnessed by three
distinct target vertices.  These six vertices are the alternating hexagon in
the corresponding cross block. -/
theorem binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_iff_hexagon
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
    (x y z : source.supp) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x) :
    ((restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).Adj y z ∧
      (restrictedComponentOwnerGraph G source target).Adj z x) ↔
      ∃ a b c : target.supp,
        a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
        a ∈ (componentCrossNeighborFinset G target x ∩
          componentCrossNeighborFinset G target y) ∧
        b ∈ (componentCrossNeighborFinset G target y ∩
          componentCrossNeighborFinset G target z) ∧
        c ∈ (componentCrossNeighborFinset G target z ∩
          componentCrossNeighborFinset G target x) := by
  have hright : ∀ w : target.supp,
      (componentCrossNeighborFinset G source w).card = 2 :=
    (binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
      G hfree hq hreg hcard source target hsource htarget).2.2
  constructor
  · rintro ⟨hxyAdj, hyzAdj, hzxAdj⟩
    obtain ⟨a, ha⟩ :=
      (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target x y).mp hxyAdj |>.2
    obtain ⟨b, hb⟩ :=
      (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target y z).mp hyzAdj |>.2
    obtain ⟨c, hc⟩ :=
      (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target z x).mp hzxAdj |>.2
    have hab : a ≠ b := by
      intro hab
      subst b
      have hxmem : x ∈ componentCrossNeighborFinset G source a := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2.symm⟩
      have hymem : y ∈ componentCrossNeighborFinset G source a := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2.symm⟩
      have hzmem : z ∈ componentCrossNeighborFinset G source a := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2.symm⟩
      have hthree : 3 ≤ (componentCrossNeighborFinset G source a).card := by
        have hsub : ({x, y, z} : Finset source.supp) ⊆
            componentCrossNeighborFinset G source a := by
          intro w hw
          simp only [Finset.mem_insert, Finset.mem_singleton] at hw
          rcases hw with rfl | rfl | rfl
          · exact hxmem
          · exact hymem
          · exact hzmem
        have := Finset.card_le_card hsub
        simpa [hxy, hyz, hzx, Ne.symm hxy, Ne.symm hyz, Ne.symm hzx] using this
      rw [hright a] at hthree
      omega
    have hbc : b ≠ c := by
      intro hbc
      subst c
      have hymem : y ∈ componentCrossNeighborFinset G source b :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2.symm⟩
      have hzmem : z ∈ componentCrossNeighborFinset G source b :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2.symm⟩
      have hxmem : x ∈ componentCrossNeighborFinset G source b :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp hc).2).2.symm⟩
      have hsub : ({x, y, z} : Finset source.supp) ⊆
          componentCrossNeighborFinset G source b := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hxmem
        · exact hymem
        · exact hzmem
      have hthree : 3 ≤ (componentCrossNeighborFinset G source b).card := by
        have := Finset.card_le_card hsub
        simpa [hxy, hyz, hzx, Ne.symm hxy, Ne.symm hyz, Ne.symm hzx] using this
      rw [hright b] at hthree
      omega
    have hca : c ≠ a := by
      intro hca
      subst c
      have hxmem : x ∈ componentCrossNeighborFinset G source a :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2.symm⟩
      have hymem : y ∈ componentCrossNeighborFinset G source a :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2.symm⟩
      have hzmem : z ∈ componentCrossNeighborFinset G source a :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).2.symm⟩
      have hsub : ({x, y, z} : Finset source.supp) ⊆
          componentCrossNeighborFinset G source a := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hxmem
        · exact hymem
        · exact hzmem
      have hthree : 3 ≤ (componentCrossNeighborFinset G source a).card := by
        have := Finset.card_le_card hsub
        simpa [hxy, hyz, hzx, Ne.symm hxy, Ne.symm hyz, Ne.symm hzx] using this
      rw [hright a] at hthree
      omega
    exact ⟨a, b, c, hab, hbc, hca, ha, hb, hc⟩
  · rintro ⟨a, b, c, _hab, _hbc, _hca, ha, hb, hc⟩
    constructor
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target x y).mpr ⟨hxy, ⟨a, ha⟩⟩
    constructor
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target y z).mpr ⟨hyz, ⟨b, hb⟩⟩
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target z x).mpr ⟨hzx, ⟨c, hc⟩⟩

end

end Erdos85

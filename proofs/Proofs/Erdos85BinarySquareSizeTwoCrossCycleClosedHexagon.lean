import Proofs.Erdos85BinarySquareSizeTwoCrossCycleInducedHexagon

/-! # Owner triangles give neighbor-closed cross hexagons -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem finset_eq_pair_of_card_two_of_mem
    {α : Type*} [DecidableEq α] {s : Finset α} {u v : α}
    (hcard : s.card = 2) (hu : u ∈ s) (hv : v ∈ s) (huv : u ≠ v) :
    s = {u, v} := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp hcard
  rw [hs] at hu hv ⊢
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  aesop

/-- A triangle in a restricted owner factor is equivalent to a closed
alternating hexagon: every one of its six vertices has exactly the two
displayed neighbors. -/
theorem binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_iff_closedHexagon
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
        componentCrossNeighborFinset G target x = {a, c} ∧
        componentCrossNeighborFinset G target y = {a, b} ∧
        componentCrossNeighborFinset G target z = {b, c} ∧
        componentCrossNeighborFinset G source a = {x, y} ∧
        componentCrossNeighborFinset G source b = {y, z} ∧
        componentCrossNeighborFinset G source c = {z, x} := by
  obtain ⟨_htranspose, hleft, hright⟩ :=
    binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
      G hfree hq hreg hcard source target hsource htarget
  have reverse_mem {u : source.supp} {w : target.supp}
      (huw : w ∈ componentCrossNeighborFinset G target u) :
      u ∈ componentCrossNeighborFinset G source w := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp huw).2.symm⟩
  constructor
  · intro htri
    obtain ⟨a, b, c, hab, hbc, hca, ha, hb, hc⟩ :=
      (binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_iff_hexagon
        G hfree hq hreg hcard source target hsource htarget x y z
        hxy hyz hzx).mp htri
    have haData := Finset.mem_inter.mp ha
    have hbData := Finset.mem_inter.mp hb
    have hcData := Finset.mem_inter.mp hc
    refine ⟨a, b, c, hab, hbc, hca, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact finset_eq_pair_of_card_two_of_mem (hleft x)
        haData.1 hcData.2 hca.symm
    · exact finset_eq_pair_of_card_two_of_mem (hleft y)
        haData.2 hbData.1 hab
    · exact finset_eq_pair_of_card_two_of_mem (hleft z)
        hbData.2 hcData.1 hbc
    · exact finset_eq_pair_of_card_two_of_mem (hright a)
        (reverse_mem haData.1) (reverse_mem haData.2) hxy
    · exact finset_eq_pair_of_card_two_of_mem (hright b)
        (reverse_mem hbData.1) (reverse_mem hbData.2) hyz
    · exact finset_eq_pair_of_card_two_of_mem (hright c)
        (reverse_mem hcData.1) (reverse_mem hcData.2) hzx
  · rintro ⟨a, b, c, _hab, _hbc, _hca, hx, hy, hz, _ha, _hb, _hc⟩
    have hax : a ∈ componentCrossNeighborFinset G target x := by
      rw [hx]
      simp
    have hay : a ∈ componentCrossNeighborFinset G target y := by
      rw [hy]
      simp
    have hby : b ∈ componentCrossNeighborFinset G target y := by
      rw [hy]
      simp
    have hbz : b ∈ componentCrossNeighborFinset G target z := by
      rw [hz]
      simp
    have hcz : c ∈ componentCrossNeighborFinset G target z := by
      rw [hz]
      simp
    have hcx : c ∈ componentCrossNeighborFinset G target x := by
      rw [hx]
      simp
    constructor
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target x y).mpr
          ⟨hxy, ⟨a, Finset.mem_inter.mpr ⟨hax, hay⟩⟩⟩
    constructor
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target y z).mpr
          ⟨hyz, ⟨b, Finset.mem_inter.mpr ⟨hby, hbz⟩⟩⟩
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G source target z x).mpr
          ⟨hzx, ⟨c, Finset.mem_inter.mpr ⟨hcz, hcx⟩⟩⟩

end

end Erdos85

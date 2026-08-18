import Proofs.Erdos85BinarySquareSizeTwoOwnerEdgeSubdivision
import Proofs.Erdos85BinarySquareSizeTwoCrossCycleInducedHexagon

/-! # Transporting owner triangles across a size-two cross block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A triangle in the owner factor on one side of a size-two cross block
induces a triangle in the reverse owner factor.  The two triangles are the
opposite halves of an induced alternating hexagon. -/
theorem binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_transport
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
    ∃ a b c : target.supp,
      a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
      (restrictedComponentOwnerGraph G target source).Adj a b ∧
      (restrictedComponentOwnerGraph G target source).Adj b c ∧
      (restrictedComponentOwnerGraph G target source).Adj c a ∧
      ¬ G.Adj x.1 b.1 ∧ ¬ G.Adj y.1 c.1 ∧ ¬ G.Adj z.1 a.1 := by
  obtain ⟨a, b, c, hab, hbc, hca, ha, hb, hc⟩ :=
    (binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_iff_hexagon
      G hfree hq hreg hcard source target hsource htarget
        x y z hxy hyz hzx).mp htri
  have reverse_mem {u : source.supp} {w : target.supp}
      (huw : w ∈ componentCrossNeighborFinset G target u) :
      u ∈ componentCrossNeighborFinset G source w := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp huw).2.symm⟩
  have habAdj : (restrictedComponentOwnerGraph G target source).Adj a b := by
    apply (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
      G target source a b).mpr
    refine ⟨hab, ⟨y, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
    · exact reverse_mem (Finset.mem_inter.mp ha).2
    · exact reverse_mem (Finset.mem_inter.mp hb).1
  have hbcAdj : (restrictedComponentOwnerGraph G target source).Adj b c := by
    apply (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
      G target source b c).mpr
    refine ⟨hbc, ⟨z, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
    · exact reverse_mem (Finset.mem_inter.mp hb).2
    · exact reverse_mem (Finset.mem_inter.mp hc).1
  have hcaAdj : (restrictedComponentOwnerGraph G target source).Adj c a := by
    apply (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
      G target source c a).mpr
    refine ⟨hca, ⟨x, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩⟩
    · exact reverse_mem (Finset.mem_inter.mp hc).2
    · exact reverse_mem (Finset.mem_inter.mp ha).1
  have hchords :=
    binarySquare_regular_twoSizeTwoParts_hexagon_has_no_cross_chords
      G hfree hq hreg hcard source target hsource htarget
        x y z hxy hyz hzx a b c ha hb hc
  exact ⟨a, b, c, hab, hbc, hca, habAdj, hbcAdj, hcaAdj, hchords⟩

/-- Existence of a restricted-owner triangle is symmetric across a normalized
size-two cross block. -/
theorem binarySquare_regular_twoSizeTwoParts_restrictedOwner_hasTriangle_iff
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
    (htarget : target.supp.ncard = q * 2) :
    (∃ x y z : source.supp, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
      (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).Adj y z ∧
      (restrictedComponentOwnerGraph G source target).Adj z x) ↔
    (∃ a b c : target.supp, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧
      (restrictedComponentOwnerGraph G target source).Adj a b ∧
      (restrictedComponentOwnerGraph G target source).Adj b c ∧
      (restrictedComponentOwnerGraph G target source).Adj c a) := by
  constructor
  · rintro ⟨x, y, z, hxy, hyz, hzx, htri⟩
    obtain ⟨a, b, c, hab, hbc, hca, habAdj, hbcAdj, hcaAdj, _⟩ :=
      binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_transport
        G hfree hq hreg hcard source target hsource htarget
          x y z hxy hyz hzx htri
    exact ⟨a, b, c, hab, hbc, hca, habAdj, hbcAdj, hcaAdj⟩
  · rintro ⟨a, b, c, hab, hbc, hca, htri⟩
    obtain ⟨x, y, z, hxy, hyz, hzx, hxyAdj, hyzAdj, hzxAdj, _⟩ :=
      binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_transport
        G hfree hq hreg hcard target source htarget hsource
          a b c hab hbc hca htri
    exact ⟨x, y, z, hxy, hyz, hzx, hxyAdj, hyzAdj, hzxAdj⟩

end

end Erdos85

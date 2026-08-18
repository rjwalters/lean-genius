import Proofs.Erdos85BinarySquareSizeTwoOwnerEdgeSubdivision
import Proofs.Erdos85BinarySquareSizeTwoCrossCycleInducedHexagon

/-! # Canonical transport of owner triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The ordered triple `(a,b,c)` subdivides the three ordered edges
`(x,y)`, `(y,z)`, `(z,x)` of an owner triangle. -/
def ownerTriangleTransportRel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y z : source.supp) (p : target.supp × (target.supp × target.supp)) : Prop :=
  G.Adj x.1 p.1.1 ∧ G.Adj y.1 p.1.1 ∧
  G.Adj y.1 p.2.1.1 ∧ G.Adj z.1 p.2.1.1 ∧
  G.Adj z.1 p.2.2.1 ∧ G.Adj x.1 p.2.2.1

/-- Every ordered owner triangle has a unique ordered triple of cross-block
subdivision vertices. -/
theorem restrictedOwner_triangle_existsUnique_transport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y z : source.supp)
    (htri : (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).Adj y z ∧
      (restrictedComponentOwnerGraph G source target).Adj z x) :
    ∃! p : target.supp × (target.supp × target.supp),
      ownerTriangleTransportRel G source target x y z p := by
  obtain ⟨_hxy, a, ha, haUnique⟩ :=
    (restrictedOwner_adj_iff_existsUnique_cross_twoPath
      G hfree source target x y).mp htri.1
  obtain ⟨_hyz, b, hb, hbUnique⟩ :=
    (restrictedOwner_adj_iff_existsUnique_cross_twoPath
      G hfree source target y z).mp htri.2.1
  obtain ⟨_hzx, c, hc, hcUnique⟩ :=
    (restrictedOwner_adj_iff_existsUnique_cross_twoPath
      G hfree source target z x).mp htri.2.2
  refine ⟨(a, (b, c)), ?_, ?_⟩
  · exact ⟨ha.1, ha.2, hb.1, hb.2, hc.1, hc.2⟩
  · rintro ⟨a', b', c'⟩ hp
    have ha' :
        (componentCrossBipartiteGraph G source target).Adj
            (Sum.inl x) (Sum.inr a') ∧
          (componentCrossBipartiteGraph G source target).Adj
            (Sum.inr a') (Sum.inl y) := ⟨hp.1, hp.2.1⟩
    have hb' :
        (componentCrossBipartiteGraph G source target).Adj
            (Sum.inl y) (Sum.inr b') ∧
          (componentCrossBipartiteGraph G source target).Adj
            (Sum.inr b') (Sum.inl z) := ⟨hp.2.2.1, hp.2.2.2.1⟩
    have hc' :
        (componentCrossBipartiteGraph G source target).Adj
            (Sum.inl z) (Sum.inr c') ∧
          (componentCrossBipartiteGraph G source target).Adj
            (Sum.inr c') (Sum.inl x) := ⟨hp.2.2.2.2.1, hp.2.2.2.2.2⟩
    have haa : a' = a := haUnique a' ha'
    have hbb : b' = b := hbUnique b' hb'
    have hcc : c' = c := hcUnique c' hc'
    subst a'
    subst b'
    subst c'
    rfl

/-- Reversing an alternating hexagon transports `(a,b,c)` back to the
cyclically ordered source triple `(y,z,x)`. -/
theorem ownerTriangleTransportRel_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (x y z : source.supp) (a b c : target.supp)
    (h : ownerTriangleTransportRel G source target x y z (a, (b, c))) :
    ownerTriangleTransportRel G target source a b c (y, (z, x)) := by
  rcases h with ⟨hxa, hay, hyb, hbz, hzc, hcx⟩
  exact ⟨hay.symm, hyb.symm, hbz.symm, hzc.symm, hcx.symm, hxa.symm⟩

/-- Canonical transport is involutive up to the forced cyclic rotation: the
unique reverse subdivision triple is exactly `(y,z,x)`. -/
theorem restrictedOwner_triangle_transport_reverse_unique
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
    (x y z : source.supp)
    (htri : (restrictedComponentOwnerGraph G source target).Adj x y ∧
      (restrictedComponentOwnerGraph G source target).Adj y z ∧
      (restrictedComponentOwnerGraph G source target).Adj z x) :
    ∃ a b c : target.supp,
      ownerTriangleTransportRel G source target x y z (a, (b, c)) ∧
      (∀ p : source.supp × (source.supp × source.supp),
        ownerTriangleTransportRel G target source a b c p ↔
          p = (y, (z, x))) := by
  have hxy : x ≠ y := htri.1.ne
  have hyz : y ≠ z := htri.2.1.ne
  have hzx : z ≠ x := htri.2.2.ne
  obtain ⟨a, b, c, hab, hbc, hca, ha, hb, hc⟩ :=
    (binarySquare_regular_twoSizeTwoParts_restrictedOwner_triangle_iff_hexagon
      G hfree hq hreg hcard source target hsource htarget
        x y z hxy hyz hzx).mp htri
  have reverse_mem {u : source.supp} {w : target.supp}
      (huw : w ∈ componentCrossNeighborFinset G target u) :
      u ∈ componentCrossNeighborFinset G source w := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp huw).2.symm⟩
  have hp : ownerTriangleTransportRel G source target x y z (a, (b, c)) :=
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hc).2).2⟩
  have hrevTri :
      (restrictedComponentOwnerGraph G target source).Adj a b ∧
      (restrictedComponentOwnerGraph G target source).Adj b c ∧
      (restrictedComponentOwnerGraph G target source).Adj c a := by
    constructor
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G target source a b).2 ⟨hab, ⟨y, Finset.mem_inter.mpr
          ⟨reverse_mem (Finset.mem_inter.mp ha).2,
            reverse_mem (Finset.mem_inter.mp hb).1⟩⟩⟩
    constructor
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G target source b c).2 ⟨hbc, ⟨z, Finset.mem_inter.mpr
          ⟨reverse_mem (Finset.mem_inter.mp hb).2,
            reverse_mem (Finset.mem_inter.mp hc).1⟩⟩⟩
    · exact (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
        G target source c a).2 ⟨hca, ⟨x, Finset.mem_inter.mpr
          ⟨reverse_mem (Finset.mem_inter.mp hc).2,
            reverse_mem (Finset.mem_inter.mp ha).1⟩⟩⟩
  obtain ⟨r, hr, hrUnique⟩ :=
    restrictedOwner_triangle_existsUnique_transport
      G hfree target source a b c hrevTri
  have hyzx := ownerTriangleTransportRel_reverse
    G source target x y z a b c hp
  refine ⟨a, b, c, hp, fun p => ?_⟩
  constructor
  · intro hp'
    exact (hrUnique p hp').trans (hrUnique (y, (z, x)) hyzx).symm
  · rintro rfl
    exact hyzx

end

end Erdos85

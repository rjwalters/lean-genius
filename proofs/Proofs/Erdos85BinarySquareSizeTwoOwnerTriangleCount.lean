import Proofs.Erdos85BinarySquareSizeTwoOwnerTriangleBijection

/-! # Equality of owner-triangle counts across size-two cross blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Finite type of ordered triangles in one restricted owner factor. -/
def restrictedOwnerOrientedTriangles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :=
  {p : source.supp × (source.supp × source.supp) //
    (restrictedComponentOwnerGraph G source owner).Adj p.1 p.2.1 ∧
    (restrictedComponentOwnerGraph G source owner).Adj p.2.1 p.2.2 ∧
    (restrictedComponentOwnerGraph G source owner).Adj p.2.2 p.1}

noncomputable instance restrictedOwnerOrientedTriangles.instFintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (source owner : (secondOrderDefectGraph G).ConnectedComponent) :
    Fintype (restrictedOwnerOrientedTriangles G source owner) := by
  classical
  unfold restrictedOwnerOrientedTriangles
  infer_instance

/-- The canonical transport relation has a unique target which is itself an
ordered triangle in the reverse owner factor. -/
theorem restrictedOwner_orientedTriangle_existsUnique_targetTriangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2)
    (s : restrictedOwnerOrientedTriangles G source target) :
    ∃! t : restrictedOwnerOrientedTriangles G target source,
      ownerTriangleTransportRel G source target
        s.1.1 s.1.2.1 s.1.2.2 t.1 := by
  rcases s with ⟨⟨x, y, z⟩, htri⟩
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
  have habAdj : (restrictedComponentOwnerGraph G target source).Adj a b :=
    (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
      G target source a b).2 ⟨hab, ⟨y, Finset.mem_inter.mpr
        ⟨reverse_mem (Finset.mem_inter.mp ha).2,
          reverse_mem (Finset.mem_inter.mp hb).1⟩⟩⟩
  have hbcAdj : (restrictedComponentOwnerGraph G target source).Adj b c :=
    (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
      G target source b c).2 ⟨hbc, ⟨z, Finset.mem_inter.mpr
        ⟨reverse_mem (Finset.mem_inter.mp hb).2,
          reverse_mem (Finset.mem_inter.mp hc).1⟩⟩⟩
  have hcaAdj : (restrictedComponentOwnerGraph G target source).Adj c a :=
    (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty
      G target source c a).2 ⟨hca, ⟨x, Finset.mem_inter.mpr
        ⟨reverse_mem (Finset.mem_inter.mp hc).2,
          reverse_mem (Finset.mem_inter.mp ha).1⟩⟩⟩
  let t : restrictedOwnerOrientedTriangles G target source :=
    ⟨(a, (b, c)), habAdj, hbcAdj, hcaAdj⟩
  have htRel : ownerTriangleTransportRel G source target x y z t.1 :=
    ⟨(Finset.mem_filter.mp (Finset.mem_inter.mp ha).1).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp ha).2).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hb).1).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hb).2).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hc).1).2,
      (Finset.mem_filter.mp (Finset.mem_inter.mp hc).2).2⟩
  obtain ⟨p, hp, hpUnique⟩ :=
    restrictedOwner_triangle_existsUnique_transport
      G hfree source target x y z htri
  refine ⟨t, htRel, ?_⟩
  intro u hu
  apply Subtype.ext
  exact (hpUnique u.1 hu).trans (hpUnique t.1 htRel).symm

/-- Canonical map from ordered source triangles to ordered target triangles. -/
def restrictedOwnerOrientedTriangleTransport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2) :
    restrictedOwnerOrientedTriangles G source target →
      restrictedOwnerOrientedTriangles G target source := fun s =>
  Classical.choose (restrictedOwner_orientedTriangle_existsUnique_targetTriangle
    G hfree hq hreg hcard source target hsource htarget s)

/-- Canonical triangle transport is injective. The reverse hexagon relation
recovers the source triple up to the fixed cyclic rotation. -/
theorem restrictedOwnerOrientedTriangleTransport_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2) :
    Function.Injective (restrictedOwnerOrientedTriangleTransport
      G hfree hq hreg hcard source target hsource htarget) := by
  rintro ⟨⟨x, y, z⟩, hs⟩ ⟨⟨x', y', z'⟩, ht⟩ heq
  let F := restrictedOwnerOrientedTriangleTransport
    G hfree hq hreg hcard source target hsource htarget
  have hsRel : ownerTriangleTransportRel G source target x y z
      (F ⟨(x, (y, z)), hs⟩).1 :=
    (Classical.choose_spec
      (restrictedOwner_orientedTriangle_existsUnique_targetTriangle
        G hfree hq hreg hcard source target hsource htarget
          ⟨(x, (y, z)), hs⟩)).1
  have htRel : ownerTriangleTransportRel G source target x' y' z'
      (F ⟨(x', (y', z')), ht⟩).1 :=
    (Classical.choose_spec
      (restrictedOwner_orientedTriangle_existsUnique_targetTriangle
        G hfree hq hreg hcard source target hsource htarget
          ⟨(x', (y', z')), ht⟩)).1
  have hsRev := ownerTriangleTransportRel_reverse G source target x y z
    (F ⟨(x, (y, z)), hs⟩).1.1 (F ⟨(x, (y, z)), hs⟩).1.2.1
      (F ⟨(x, (y, z)), hs⟩).1.2.2 hsRel
  have htRev := ownerTriangleTransportRel_reverse G source target x' y' z'
    (F ⟨(x', (y', z')), ht⟩).1.1 (F ⟨(x', (y', z')), ht⟩).1.2.1
      (F ⟨(x', (y', z')), ht⟩).1.2.2 htRel
  have heqVal : (F ⟨(x, (y, z)), hs⟩).1 =
      (F ⟨(x', (y', z')), ht⟩).1 := congrArg Subtype.val heq
  rw [heqVal] at hsRev
  let u := F ⟨(x', (y', z')), ht⟩
  obtain ⟨r, hr, hrUnique⟩ :=
    restrictedOwner_triangle_existsUnique_transport G hfree target source
      u.1.1 u.1.2.1 u.1.2.2 u.2
  have hrot : (y, (z, x)) = (y', (z', x')) :=
    (hrUnique (y, (z, x)) hsRev).trans
      (hrUnique (y', (z', x')) htRev).symm
  injection hrot with hy hrest
  injection hrest with hz hx
  subst y'
  subst z'
  subst x'
  rfl

/-- The two restricted owner factors have exactly the same number of ordered
triangles. -/
theorem binarySquare_regular_twoSizeTwoParts_orientedTriangle_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2) :
    Fintype.card (restrictedOwnerOrientedTriangles G source target) =
      Fintype.card (restrictedOwnerOrientedTriangles G target source) := by
  apply Nat.le_antisymm
  · exact Fintype.card_le_of_injective
      (restrictedOwnerOrientedTriangleTransport
        G hfree hq hreg hcard source target hsource htarget)
      (restrictedOwnerOrientedTriangleTransport_injective
        G hfree hq hreg hcard source target hsource htarget)
  · exact Fintype.card_le_of_injective
      (restrictedOwnerOrientedTriangleTransport
        G hfree hq hreg hcard target source htarget hsource)
      (restrictedOwnerOrientedTriangleTransport_injective
        G hfree hq hreg hcard target source htarget hsource)

end

end Erdos85

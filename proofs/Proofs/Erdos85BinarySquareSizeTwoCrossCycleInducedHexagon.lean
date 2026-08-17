import Proofs.Erdos85BinarySquareSizeTwoCrossCycleOwnerTriangle

/-! # Owner triangles give induced alternating hexagons -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem eq_left_or_eq_right_of_mem_card_two
    {α : Type*} [DecidableEq α] {s : Finset α} {x y z : α}
    (hcard : s.card = 2) (hy : y ∈ s) (hz : z ∈ s) (hyz : y ≠ z)
    (hx : x ∈ s) : x = y ∨ x = z := by
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hcard
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy hz hx
  aesop

/-- The alternating hexagon supplied by an owner-factor triangle has none of
the three possible cross-chords.  Together with bipartiteness, it is an
induced `C₆` in the component cross graph. -/
theorem binarySquare_regular_twoSizeTwoParts_hexagon_has_no_cross_chords
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
    (a b c : target.supp)
    (ha : a ∈ componentCrossNeighborFinset G target x ∩
      componentCrossNeighborFinset G target y)
    (hb : b ∈ componentCrossNeighborFinset G target y ∩
      componentCrossNeighborFinset G target z)
    (hc : c ∈ componentCrossNeighborFinset G target z ∩
      componentCrossNeighborFinset G target x) :
    ¬ G.Adj x.1 b.1 ∧ ¬ G.Adj y.1 c.1 ∧ ¬ G.Adj z.1 a.1 := by
  have hright : ∀ w : target.supp,
      (componentCrossNeighborFinset G source w).card = 2 :=
    (binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
      G hfree hq hreg hcard source target hsource htarget).2.2
  have reverse_mem {u : source.supp} {w : target.supp}
      (huw : w ∈ componentCrossNeighborFinset G target u) :
      u ∈ componentCrossNeighborFinset G source w := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp huw).2.symm⟩
  have hax : x ∈ componentCrossNeighborFinset G source a :=
    reverse_mem (Finset.mem_inter.mp ha).1
  have hay : y ∈ componentCrossNeighborFinset G source a :=
    reverse_mem (Finset.mem_inter.mp ha).2
  have hby : y ∈ componentCrossNeighborFinset G source b :=
    reverse_mem (Finset.mem_inter.mp hb).1
  have hbz : z ∈ componentCrossNeighborFinset G source b :=
    reverse_mem (Finset.mem_inter.mp hb).2
  have hcz : z ∈ componentCrossNeighborFinset G source c :=
    reverse_mem (Finset.mem_inter.mp hc).1
  have hcx : x ∈ componentCrossNeighborFinset G source c :=
    reverse_mem (Finset.mem_inter.mp hc).2
  constructor
  · intro hxb
    have hxbmem : x ∈ componentCrossNeighborFinset G source b :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb.symm⟩
    rcases eq_left_or_eq_right_of_mem_card_two (hright b) hby hbz hyz hxbmem with
      h | h
    · exact hxy h
    · exact hzx h.symm
  constructor
  · intro hyc
    have hycmem : y ∈ componentCrossNeighborFinset G source c :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyc.symm⟩
    rcases eq_left_or_eq_right_of_mem_card_two (hright c) hcz hcx hzx hycmem with
      h | h
    · exact hyz h
    · exact hxy h.symm
  · intro hza
    have hzamem : z ∈ componentCrossNeighborFinset G source a :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza.symm⟩
    rcases eq_left_or_eq_right_of_mem_card_two (hright a) hax hay hxy hzamem with
      h | h
    · exact hzx h
    · exact hyz h.symm

end

end Erdos85

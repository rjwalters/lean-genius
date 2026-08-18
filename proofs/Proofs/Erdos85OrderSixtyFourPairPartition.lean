import Proofs.Erdos85OrderSixtyFourExteriorPairGraph

/-! # The defect/internal/exterior partition on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For two distinct vertices in a set `s`, failure of defect adjacency is
exactly the existence of a common ambient neighbor.  Splitting that witness
at the cut `s` says that it is either an internal common neighbor or an edge
of the exterior-pair graph. -/
theorem not_secondOrderDefectAdj_iff_internalCommon_or_exteriorPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : Set V)
    [DecidablePred (· ∈ s)] (u v : s) (huv : u ≠ v) :
    ¬ (secondOrderDefectGraph G).Adj u.1 v.1 ↔
      (∃ z : s, (G.induce s).Adj u z ∧ (G.induce s).Adj v z) ∨
        (exteriorPairGraph G s).Adj u v := by
  classical
  have huvval : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  have hcommon := card_common_eq_if_secondOrderDefect
    G hfree u.1 v.1 huvval
  constructor
  · intro hD
    have hnotmem : v.1 ∉ (secondOrderDefectGraph G).neighborFinset u.1 := by
      intro hm
      exact hD (((secondOrderDefectGraph G).mem_neighborFinset u.1 v.1).mp hm)
    have hcard : (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card = 1 := by
      calc
        _ = if v.1 ∈ (secondOrderDefectGraph G).neighborFinset u.1
              then 0 else 1 := hcommon
        _ = 1 := if_neg hnotmem
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega :
      0 < (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card)
    have hzu : G.Adj u.1 z :=
      (G.mem_neighborFinset u.1 z).mp (Finset.mem_inter.mp hz).1
    have hzv : G.Adj v.1 z :=
      (G.mem_neighborFinset v.1 z).mp (Finset.mem_inter.mp hz).2
    by_cases hzs : z ∈ s
    · left
      exact ⟨⟨z, hzs⟩, hzu, hzv⟩
    · right
      exact ⟨huv, z, hzs, hzu, hzv⟩
  · rintro (⟨z, huz, hvz⟩ | hR) hD
    · have hmem : z.1 ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 :=
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset u.1 z.1).mpr huz,
          (G.mem_neighborFinset v.1 z.1).mpr hvz⟩
      have hpos : 0 < (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card :=
        Finset.card_pos.mpr ⟨z.1, hmem⟩
      have hmemD : v.1 ∈ (secondOrderDefectGraph G).neighborFinset u.1 :=
        ((secondOrderDefectGraph G).mem_neighborFinset u.1 v.1).mpr hD
      have hzero : (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card = 0 := by
        calc
          _ = if v.1 ∈ (secondOrderDefectGraph G).neighborFinset u.1
                then 0 else 1 := hcommon
          _ = 0 := if_pos hmemD
      omega
    · obtain ⟨_huv, z, _hzout, huz, hvz⟩ := hR
      have hmem : z ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 :=
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset u.1 z).mpr huz,
          (G.mem_neighborFinset v.1 z).mpr hvz⟩
      have hpos : 0 < (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card :=
        Finset.card_pos.mpr ⟨z, hmem⟩
      have hmemD : v.1 ∈ (secondOrderDefectGraph G).neighborFinset u.1 :=
        ((secondOrderDefectGraph G).mem_neighborFinset u.1 v.1).mpr hD
      have hzero : (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card = 0 := by
        calc
          _ = if v.1 ∈ (secondOrderDefectGraph G).neighborFinset u.1
                then 0 else 1 := hcommon
          _ = 0 := if_pos hmemD
      omega

/-- Internal and exterior common-neighbor pairs are disjoint in a C4-free
ambient graph. -/
theorem not_internalCommon_and_exteriorPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : Set V)
    [DecidablePred (· ∈ s)] (u v : s) (huv : u ≠ v) :
    ¬ ((∃ z : s, (G.induce s).Adj u z ∧ (G.induce s).Adj v z) ∧
      (exteriorPairGraph G s).Adj u v) := by
  rintro ⟨⟨z, huz, hvz⟩, _huv, w, hwout, huw, hvw⟩
  have hzmem : z.1 ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset u.1 z.1).mpr huz,
      (G.mem_neighborFinset v.1 z.1).mpr hvz⟩
  have hwmem : w ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 :=
    Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset u.1 w).mpr huw,
      (G.mem_neighborFinset v.1 w).mpr hvw⟩
  have hzw : z.1 ≠ w := by
    intro h
    exact hwout (h ▸ z.2)
  have htwo : 2 ≤ (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card := by
    have hsub : ({z.1, w} : Finset V) ⊆
        G.neighborFinset u.1 ∩ G.neighborFinset v.1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzmem
      · exact hwmem
    have hc := Finset.card_le_card hsub
    simpa [hzw] using hc
  have hone := (not_containsC4_iff_forall_common_le_one G).mp hfree
    u.1 v.1 (fun h ↦ huv (Subtype.ext h))
  omega

/-- Every distinct pair belongs to exactly one of the three relations:
defect adjacency, an internal common-neighbor pair, or an exterior-pair
edge.  This is the pointwise form of `D + A² + R = J + I`. -/
theorem defect_internal_exterior_pair_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (s : Set V)
    [DecidablePred (· ∈ s)] (u v : s) (huv : u ≠ v) :
    let I := ∃ z : s, (G.induce s).Adj u z ∧ (G.induce s).Adj v z
    let E := (exteriorPairGraph G s).Adj u v
    ((secondOrderDefectGraph G).Adj u.1 v.1 ∨ I ∨ E) ∧
      ¬ ((secondOrderDefectGraph G).Adj u.1 v.1 ∧ I) ∧
      ¬ ((secondOrderDefectGraph G).Adj u.1 v.1 ∧ E) ∧
      ¬ (I ∧ E) := by
  dsimp only
  have hiff := not_secondOrderDefectAdj_iff_internalCommon_or_exteriorPair
    G hfree s u v huv
  have hIE := not_internalCommon_and_exteriorPair G hfree s u v huv
  constructor
  · by_cases hD : (secondOrderDefectGraph G).Adj u.1 v.1
    · exact Or.inl hD
    · exact Or.inr (hiff.mp hD)
  constructor
  · rintro ⟨hD, hI⟩
    exact (hiff.not.mp (not_not_intro hD)) (Or.inl hI)
  constructor
  · rintro ⟨hD, hE⟩
    exact (hiff.not.mp (not_not_intro hD)) (Or.inr hE)
  · exact hIE

end

end Erdos85

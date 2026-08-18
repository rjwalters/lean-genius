import Proofs.Erdos85BinarySquareSizeTwoStarPerfectMatching

/-! # Overlap law for selector-star perfect matchings -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The set of target-coordinate selector edges obtained from the ambient
vertices in the selector star at `u`. -/
def sizeTwoSelectorStarMatchingEdgeSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (u : c.supp) :
    Set (Finset V) :=
  Set.range fun x : sizeTwoSelectorStarIndex G c u =>
    componentNeighborFinset G (secondOrderDefectGraph G) d x.1

/-- **Orthogonal-double-cover overlap law.**  For two size-two coordinates
`c,d`, the perfect matchings of `d` indexed by distinct points `u,v` of `c`
share a target edge exactly when `u,v` are a nonedge of the defect block
`D[c]` (equivalently, an edge of its selector complement). -/
theorem binarySquare_regular_twoSizeTwoParts_starMatching_inter_nonempty_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (u v : c.supp) (huv : u ≠ v) :
    (sizeTwoSelectorStarMatchingEdgeSet G c d u ∩
      sizeTwoSelectorStarMatchingEdgeSet G c d v).Nonempty ↔
      ¬(secondOrderDefectGraph G).Adj u.1 v.1 := by
  let D := secondOrderDefectGraph G
  have huvVal : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  constructor
  · rintro ⟨p, hpU, hpV⟩
    obtain ⟨x, hx⟩ := hpU
    obtain ⟨y, hy⟩ := hpV
    change componentNeighborFinset G D d x.1 = p at hx
    change componentNeighborFinset G D d y.1 = p at hy
    have htarget :
        componentNeighborFinset G D d x.1 =
          componentNeighborFinset G D d y.1 := hx.trans hy.symm
    have hxy : x.1 = y.1 :=
      binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective
        G hfree hq hreg hcard d hd htarget
    have huMem : u.1 ∈ componentNeighborFinset G D c x.1 := x.2
    have hvMem : v.1 ∈ componentNeighborFinset G D c x.1 := by
      simpa [hxy] using y.2
    have hselCard : (componentNeighborFinset G D c x.1).card = 2 :=
      binarySquare_regular_sizeTwoPart_selector_card
        G hfree hq hreg hcard c hc x.1
    have hpair : componentNeighborFinset G D c x.1 = {u.1, v.1} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact huMem
        · exact hvMem
      · rw [hselCard]
        simp [huvVal]
    exact (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
      G hfree hq hreg hcard c hc u v huv).mp ⟨x.1, hpair⟩
  · intro hnotD
    obtain ⟨x, hx⟩ :=
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard c hc u v huv).mpr hnotD
    have huMem : u.1 ∈ componentNeighborFinset G D c x := by
      rw [hx]
      simp [huvVal]
    have hvMem : v.1 ∈ componentNeighborFinset G D c x := by
      rw [hx]
      simp
    let xu : sizeTwoSelectorStarIndex G c u := ⟨x, huMem⟩
    let xv : sizeTwoSelectorStarIndex G c v := ⟨x, hvMem⟩
    refine ⟨componentNeighborFinset G D d x, ?_, ?_⟩
    · exact ⟨xu, rfl⟩
    · exact ⟨xv, rfl⟩

end

end Erdos85

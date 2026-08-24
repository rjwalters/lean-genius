import Proofs.Erdos85PureEndpointExteriorNearParallelDesign
import Proofs.Erdos85PureEndpointHalfOccupancyDefectCenters
import Proofs.Erdos85PureEndpointDefectBoundary

/-!
# Averaging forces an exterior parallel class

The exterior has as many vertices as there are oriented full-center defect
incidences.  Thus its average number of full-center defect neighbors is one.
The forced row with at least two holes consequently forces a zero-hole row,
whose owner blocks form a perfect matching of the full centers.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- Symmetry of bipartite incidence sums in an undirected graph. -/
theorem sum_neighbor_inter_card_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A B : Finset V) :
    (∑ a ∈ A, (H.neighborFinset a ∩ B).card) =
      ∑ b ∈ B, (H.neighborFinset b ∩ A).card := by
  classical
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := A) (t := B) H.Adj
  calc
    (∑ a ∈ A, (H.neighborFinset a ∩ B).card) =
        ∑ a ∈ A, (B.bipartiteAbove H.Adj a).card := by
      apply sum_congr rfl
      intro a _ha
      congr 1
      ext b
      simp [Finset.bipartiteAbove, SimpleGraph.mem_neighborFinset, and_comm]
    _ = ∑ b ∈ B, (A.bipartiteBelow H.Adj b).card := h
    _ = ∑ b ∈ B, (H.neighborFinset b ∩ A).card := by
      apply sum_congr rfl
      intro b _hb
      congr 1
      ext a
      simp [Finset.bipartiteBelow, SimpleGraph.mem_neighborFinset,
        H.adj_comm, and_comm]

/-- A nonnegative integer-valued function of average one which takes a value
at least two must vanish somewhere. -/
theorem exists_eq_zero_of_sum_eq_card_of_two_le
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    {x : α} (hx : x ∈ s) (hTwo : 2 ≤ f x)
    (hsum : ∑ y ∈ s, f y = s.card) :
    ∃ y ∈ s, f y = 0 := by
  classical
  by_contra h
  push_neg at h
  have hpos : ∀ y ∈ s, 1 ≤ f y := by
    intro y hy
    exact Nat.one_le_iff_ne_zero.mpr (h y hy)
  have hrest : (s.erase x).card ≤ ∑ y ∈ s.erase x, f y := by
    calc
      (s.erase x).card = ∑ _y ∈ s.erase x, 1 := by simp
      _ ≤ ∑ y ∈ s.erase x, f y :=
        sum_le_sum fun y hy => hpos y (mem_of_mem_erase hy)
  have herase := s.sum_erase_add f hx
  have hcardErase := card_erase_of_mem hx
  omega

/-- A preconnected pure endpoint contains an exterior vertex whose `m` shore
neighbors have pairwise-disjoint two-element owner sets partitioning all of
`F`: a genuine parallel class. -/
theorem c4Free_binarySquare_pureEndpoint_exists_exterior_parallelClass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let owner := fun y => G.neighborFinset y ∩ F
    ∃ w ∉ F,
      let B := G.neighborFinset w ∩ S
      let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
      B.card = m ∧ K.card = 0 ∧
      (((B : Finset V) : Set V).PairwiseDisjoint owner) ∧
      B.biUnion owner = F ∧
      ∀ y ∈ B, (owner y).card = 2 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := Fᶜ
  let D := secondOrderDefectGraph G
  let holes : V → ℕ := fun w => (D.neighborFinset w ∩ F).card
  have hWcard : W.card = q * (q - 1) := by
    rw [card_compl, show F.card = q by simpa [F] using hCcard, hcard]
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hboundary := (c4Free_binarySquare_pureEndpoint_defectBoundary_eq
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2
  have hsum : (∑ w ∈ W, holes w) = W.card := by
    have hsym := sum_neighbor_inter_card_comm D W F
    change (∑ w ∈ W, holes w) = _ at hsym
    rw [hsym]
    have : (∑ i ∈ F, (D.neighborFinset i ∩ W).card) = q * (q - 1) := by
      simpa [F, W, D] using hboundary
    rw [this, hWcard]
  obtain ⟨w₂, hw₂Half, hw₂Two⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_two_defectCenters
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hw₂NotF : w₂ ∉ F := by
    intro hw₂F
    have hw₂q := (mem_fullLineCenters G S q w₂).mp hw₂F
    rw [hw₂Half, hqm] at hw₂q
    omega
  have hw₂W : w₂ ∈ W := by simpa [W] using hw₂NotF
  have hTwo : 2 ≤ holes w₂ := by simpa [holes, D, F] using hw₂Two
  obtain ⟨w, hwW, hwZero⟩ :=
    exists_eq_zero_of_sum_eq_card_of_two_le W holes hw₂W hTwo hsum
  have hwNotF : w ∉ F := by simpa [W] using hwW
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri w hwNotF
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  have hprivateZero : (G.neighborFinset w ∩ R₁).card = 0 := by
    have := hdesign.2.1
    change holes w = (G.neighborFinset w ∩ R₁).card at this
    rw [hwZero] at this
    exact this.symm
  refine ⟨w, hwNotF, hdesign.1, ?_, hdesign.2.2.1, ?_, ?_⟩
  · simpa [holes, D, F] using hwZero
  · have hnear := hdesign.2.2.2
    have hKempty : D.neighborFinset w ∩ F = ∅ := by
      apply card_eq_zero.mp
      simpa [holes] using hwZero
    rw [hKempty, sdiff_empty] at hnear
    simpa [F, owner, D] using hnear
  · intro y hy
    have hprofile :=
      (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri).1
    rcases (hprofile y).mp (mem_inter.mp hy).2 with hOne | hTwo
    · have hyR₁ : y ∈ R₁ := mem_filter.mpr
        ⟨(mem_inter.mp hy).2, by simpa [owner, F] using hOne⟩
      have : y ∈ G.neighborFinset w ∩ R₁ :=
        mem_inter.mpr ⟨(mem_inter.mp hy).1, hyR₁⟩
      rw [card_eq_zero.mp hprivateZero] at this
      simp at this
    · simpa [owner, F] using hTwo

end

end Erdos85

#print axioms Erdos85.sum_neighbor_inter_card_comm
#print axioms Erdos85.exists_eq_zero_of_sum_eq_card_of_two_le
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_exterior_parallelClass

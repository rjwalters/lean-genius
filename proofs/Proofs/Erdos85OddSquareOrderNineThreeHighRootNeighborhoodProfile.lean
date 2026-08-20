import Proofs.Erdos85OddSquareOrderNineThreeHighSupportGeometry

/-! # Fixed-high neighborhood profiles at q = 9

Node: B.3 / GAP B-CLASSIFY.  Double counting incidences between a high
root's neighborhood and the high sector gives a pointwise bin census.  At
three highs this yields the `2+8` pair profile or the `1+9` triple profile.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The five low-incidence bins partition the neighborhood of every q=9
high root.  Their weighted sum is `10 + (h-1)`: ten from the root itself and
one common witness with each other high root. -/
theorem squareOrderNine_highRoot_neighborhood_bin_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    {a : V} (ha : a ∈ squareOrderHighVertices G 9) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G
    (∑ j ∈ Finset.range 5, (G.neighborFinset a ∩ B j).card) = 10 ∧
      (∑ j ∈ Finset.range 5, j * (G.neighborFinset a ∩ B j).card) =
        10 + (H.card - 1) := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let k := squareOrderHighIncidenceCount G 9
  let S := G.neighborFinset a
  have ha10 : G.degree a = 10 := (Finset.mem_filter.mp ha).2
  have hneighborLow {x : V} (hx : x ∈ S) : G.degree x = 9 := by
    rcases hp.degree_dichotomy x with hlo | hhi
    · exact hlo
    · have hxH : x ∈ H := Finset.mem_filter.mpr ⟨by simp, hhi⟩
      have hax : G.Adj a x := (G.mem_neighborFinset a x).mp hx
      exact (hp.high_independent ha hxH hax).elim
  have hklt {x : V} (hx : x ∈ S) : k x < 5 := by
    have h := hp.low_incidence_bound (hneighborLow hx)
    change 2 * k x ≤ 9 at h
    omega
  have hnotHigh {x : V} (hx : x ∈ S) : x ∉ H := by
    intro hxH
    exact hp.high_independent ha hxH ((G.mem_neighborFinset a x).mp hx)
  have hfiber (j : ℕ) :
      {x ∈ S | k x = j} =
        S ∩ squareOrderNineLowIncidenceBin G j := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hxS, hkx⟩
      exact ⟨hxS, Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨by simp, hnotHigh hxS⟩, hkx⟩⟩
    · rintro ⟨hxS, hxB⟩
      exact ⟨hxS, (Finset.mem_filter.mp hxB).2⟩
  have hmaps : (S : Set V).MapsTo k (Finset.range 5) := by
    intro x hx
    exact Finset.mem_range.mpr (hklt hx)
  have hcardS : S.card = 10 := by
    rw [G.card_neighborFinset_eq_degree, ha10]
  have hweighted : (∑ x ∈ S, k x) = 10 + (H.card - 1) := by
    have hswap := sum_card_neighborFinset_inter_comm G S H
    change (∑ x ∈ S, k x) =
      ∑ b ∈ H, (G.neighborFinset b ∩ S).card at hswap
    rw [hswap]
    rw [← Finset.sum_erase_add _ _ ha]
    have hother :
        (∑ b ∈ H.erase a, (G.neighborFinset b ∩ S).card) =
          (H.erase a).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro b hb
      have hbH : b ∈ H := (Finset.mem_erase.mp hb).2
      have hba : b ≠ a := (Finset.mem_erase.mp hb).1
      have hone := squareOrder_card_common_highRoot_eq_one
        G hfree (by norm_num) hmin hcard ha10 (Ne.symm hba)
      simpa [S, Finset.inter_comm] using hone
    rw [hother, Finset.card_erase_of_mem ha]
    have hself : (G.neighborFinset a ∩ S).card = 10 := by
      simp [S, hcardS]
    rw [hself]
    change H.card - 1 + 10 = 10 + (H.card - 1)
    omega
  constructor
  · calc
      (∑ j ∈ Finset.range 5,
          (G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G j).card) =
          ∑ j ∈ Finset.range 5, #{x ∈ S | k x = j} := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hfiber]
      _ = S.card := (Finset.card_eq_sum_card_fiberwise hmaps).symm
      _ = 10 := hcardS
  · calc
      (∑ j ∈ Finset.range 5,
          j * (G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G j).card) =
          ∑ j ∈ Finset.range 5, ∑ x ∈ {x ∈ S | k x = j}, j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hfiber]
        change j * #(S ∩ squareOrderNineLowIncidenceBin G j) = _
        simp [Nat.mul_comm]
      _ = ∑ x ∈ S, k x := by
        simpa using (Finset.sum_fiberwise_of_maps_to' hmaps
          (fun j : ℕ => j))
      _ = 10 + (H.card - 1) := hweighted

/-- In the first h=3 profile, each high root has exactly eight bin-one and
two bin-two neighbors. -/
theorem squareOrderNine_threeHigh_firstProfile_highRoot_neighbor_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a : V} (ha : a ∈ squareOrderHighVertices G 9) :
    (G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 1).card = 8 ∧
      (G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 2).card = 2 := by
  have hledger := squareOrderNine_highRoot_neighborhood_bin_ledger
    G hfree hmin hcard hp ha
  dsimp only at hledger
  rw [hhigh] at hledger
  have hzero :
      (G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 0).card = 0 := by
    rw [Finset.card_eq_zero]
    ext x
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hax hxB
    have haK : a ∈ G.neighborFinset x ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x a).mpr
          ((G.adj_comm a x).mp ((G.mem_neighborFinset a x).mp hax)), ha⟩
    have hkpos : 0 < squareOrderHighIncidenceCount G 9 x := by
      unfold squareOrderHighIncidenceCount
      exact Finset.card_pos.mpr ⟨a, haK⟩
    have hkzero := (Finset.mem_filter.mp hxB).2
    omega
  have hb3 : squareOrderNineLowIncidenceBin G 3 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 3) (by omega), hc3]
  have hb4 : squareOrderNineLowIncidenceBin G 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  norm_num [Finset.sum_range_succ] at hledger
  rw [hzero, hb3, hb4] at hledger
  norm_num at hledger
  omega

/-- In the second h=3 profile, each high root has exactly nine bin-one and
one bin-three neighbor. -/
theorem squareOrderNine_threeHigh_secondProfile_highRoot_neighbor_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a : V} (ha : a ∈ squareOrderHighVertices G 9) :
    (G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 1).card = 9 ∧
      (G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 3).card = 1 := by
  have hledger := squareOrderNine_highRoot_neighborhood_bin_ledger
    G hfree hmin hcard hp ha
  dsimp only at hledger
  rw [hhigh] at hledger
  have hzero :
      (G.neighborFinset a ∩ squareOrderNineLowIncidenceBin G 0).card = 0 := by
    rw [Finset.card_eq_zero]
    ext x
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hax hxB
    have haK : a ∈ G.neighborFinset x ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x a).mpr
          ((G.adj_comm a x).mp ((G.mem_neighborFinset a x).mp hax)), ha⟩
    have hkpos : 0 < squareOrderHighIncidenceCount G 9 x := by
      unfold squareOrderHighIncidenceCount
      exact Finset.card_pos.mpr ⟨a, haK⟩
    have hkzero := (Finset.mem_filter.mp hxB).2
    omega
  have hb2 : squareOrderNineLowIncidenceBin G 2 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 2) (by omega), hc2]
  have hb4 : squareOrderNineLowIncidenceBin G 4 = ∅ := by
    rw [← Finset.card_eq_zero,
      squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
        G hp (i := 4) (by omega), hc4]
  norm_num [Finset.sum_range_succ] at hledger
  rw [hzero, hb2, hb4] at hledger
  norm_num at hledger
  omega

end


end Erdos85

#print axioms Erdos85.squareOrderNine_highRoot_neighborhood_bin_ledger
#print axioms
  Erdos85.squareOrderNine_threeHigh_firstProfile_highRoot_neighbor_split
#print axioms
  Erdos85.squareOrderNine_threeHigh_secondProfile_highRoot_neighbor_split

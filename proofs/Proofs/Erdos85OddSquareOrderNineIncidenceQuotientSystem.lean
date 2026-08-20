import Proofs.Erdos85OddSquareOrderNineIncidenceQuotientSymmetry

/-! # The finite q = 9 incidence-quotient system

Node: B.3 / GAP B-CLASSIFY.  The five low-incidence bins exhaust every
defect neighborhood.  Consequently the raw pointwise ledgers become two
explicit equations in the symmetric inter-bin edge counts.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At q=9, the defect neighbors of a low vertex are partitioned by the five
low-incidence bins.  The first identity counts neighbors and the second sums
their high-incidence weights. -/
theorem squareOrderNine_defectNeighbor_bin_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (x : V) :
    let D := secondOrderDefectGraph G
    let k := squareOrderHighIncidenceCount G 9
    (∑ j ∈ Finset.range 5,
        (D.neighborFinset x ∩ squareOrderNineLowIncidenceBin G j).card) =
        D.degree x ∧
      (∑ j ∈ Finset.range 5,
        j * (D.neighborFinset x ∩ squareOrderNineLowIncidenceBin G j).card) =
        ∑ y ∈ D.neighborFinset x, k y := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G 9
  let S := D.neighborFinset x
  have hneighborLow {y : V} (hy : y ∈ S) : G.degree y = 9 := by
    rcases hp.degree_dichotomy y with hylo | hyhi
    · exact hylo
    · have hyDzero : D.degree y = 0 :=
        (squareOrder_degree_succ_highRoot_structure
          G hfree (by norm_num) hmin hcard hyhi).1
      have hyDempty : D.neighborFinset y = ∅ := by
        rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hyDzero]
      have hyx : x ∈ D.neighborFinset y := by
        simpa [S, SimpleGraph.mem_neighborFinset, D.adj_comm] using hy
      rw [hyDempty] at hyx
      exact (Finset.notMem_empty x hyx).elim
  have hklt {y : V} (hy : y ∈ S) : k y < 5 := by
    have hbound := hp.low_incidence_bound (hneighborLow hy)
    change 2 * k y ≤ 9 at hbound
    omega
  have hfiber (j : ℕ) :
      {y ∈ S | k y = j} =
        S ∩ squareOrderNineLowIncidenceBin G j := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_inter]
    constructor
    · rintro ⟨hyS, hky⟩
      refine ⟨hyS, ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨by simp, ?_⟩, hky⟩
      intro hyH
      have hyhigh : G.degree y = 10 := (Finset.mem_filter.mp hyH).2
      have hylow : G.degree y = 9 := hneighborLow hyS
      omega
    · rintro ⟨hyS, hyB⟩
      exact ⟨hyS, (Finset.mem_filter.mp hyB).2⟩
  have hmaps : (S : Set V).MapsTo k (Finset.range 5) := by
    intro y hy
    exact Finset.mem_range.mpr (hklt hy)
  constructor
  · calc
      (∑ j ∈ Finset.range 5,
          (D.neighborFinset x ∩ squareOrderNineLowIncidenceBin G j).card) =
          ∑ j ∈ Finset.range 5, #{y ∈ S | k y = j} := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hfiber]
      _ = S.card := (Finset.card_eq_sum_card_fiberwise hmaps).symm
      _ = D.degree x := D.card_neighborFinset_eq_degree x
  · calc
      (∑ j ∈ Finset.range 5,
          j * (D.neighborFinset x ∩ squareOrderNineLowIncidenceBin G j).card) =
          ∑ j ∈ Finset.range 5, ∑ y ∈ {y ∈ S | k y = j}, j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hfiber]
        change j * #(S ∩ squareOrderNineLowIncidenceBin G j) = _
        simp [Nat.mul_comm]
      _ = ∑ y ∈ S, k y := by
        simpa using (Finset.sum_fiberwise_of_maps_to' hmaps
          (fun j : ℕ => j))

/-- The complete five-bin quotient row equations.  Together with
`squareOrderNineDefectBinEdgeCount_comm`, these form a symmetric finite
integer feasibility system for each scalar incidence profile. -/
theorem squareOrderNine_lowIncidenceBin_finite_quotient_system
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (i : ℕ) :
    let H := squareOrderHighVertices G 9
    let B := squareOrderNineLowIncidenceBin G i
    (∑ j ∈ Finset.range 5, squareOrderNineDefectBinEdgeCount G i j) =
        (8 - i) * B.card ∧
      (∑ j ∈ Finset.range 5,
        j * squareOrderNineDefectBinEdgeCount G i j) =
        (H.card - i) * B.card := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G 9
  let B := squareOrderNineLowIncidenceBin G i
  have hledger := squareOrderNine_lowIncidenceBin_quotient_ledger
    G hfree hmin hcover hcard i
  dsimp only at hledger
  have hpartition (x : V) (_hx : x ∈ B) :=
    squareOrderNine_defectNeighbor_bin_partition G hfree hmin hcard hp x
  dsimp only at hpartition
  constructor
  · rw [← hledger.1]
    simp only [squareOrderNineDefectBinEdgeCount]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    exact (hpartition x hx).1
  · rw [← hledger.2]
    simp only [squareOrderNineDefectBinEdgeCount]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    exact (hpartition x hx).2

end

end Erdos85

#print axioms Erdos85.squareOrderNine_defectNeighbor_bin_partition
#print axioms Erdos85.squareOrderNine_lowIncidenceBin_finite_quotient_system

import Proofs.Erdos85SquareOrderHighIncidence
import Proofs.Erdos85DegreeExcessStratification

/-!
# The square-order defect degree-square moment

At square order, a low vertex with high-incidence `k` has defect degree
`d - 1 - k`, while every high vertex is isolated in the defect graph.
Combining this pointwise identity with the first two incidence moments gives
an exact defect degree-square moment.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_sum_defectDegree_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let H := squareOrderHighVertices G d
    let D := secondOrderDefectGraph G
    let h := H.card
    (∑ x : V, ((D.degree x : ℤ) ^ 2)) =
      ((d * d - h : Nat) : ℤ) * ((d - 1 : Nat) : ℤ) ^ 2 -
        2 * ((d - 1 : Nat) : ℤ) * ((d + 1 : Nat) : ℤ) * h +
        h * (h + d) := by
  classical
  let H := squareOrderHighVertices G d
  let L := (Finset.univ : Finset V) \ H
  let D := secondOrderDefectGraph G
  let k : V → Nat := fun x => (G.neighborFinset x ∩ H).card
  dsimp only
  have hfirstAll : (∑ x : V, k x) = (d + 1) * H.card := by
    simpa [H, k] using squareOrder_sum_highNeighborCount_eq G d
  have hsecondAll : (∑ x : V, k x * k x) = H.card * (H.card + d) := by
    simpa [H, k, pow_two] using
      squareOrder_sum_highNeighborCount_sq_eq
        G hfree hd hmin hcover hcard
  have hkzero : ∀ x ∈ H, k x = 0 := by
    intro x hx
    exact squareOrder_highNeighborCount_eq_zero_of_high G hcover hx
  have hfirstSplit := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp) (f := k)
  have hsecondSplit := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp) (f := fun x => k x * k x)
  have hfirstLow : (∑ x ∈ L, k x) = (d + 1) * H.card := by
    rw [Finset.sum_eq_zero hkzero, add_zero] at hfirstSplit
    simpa [L] using hfirstSplit.trans hfirstAll
  have hsecondLow : (∑ x ∈ L, k x * k x) = H.card * (H.card + d) := by
    have hz : (∑ x ∈ H, k x * k x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hkzero x hx]
    rw [hz, add_zero] at hsecondSplit
    simpa [L] using hsecondSplit.trans hsecondAll
  have hLcard : L.card = d * d - H.card := by
    dsimp [L]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp
  have hneighborExcess : ∀ x : V,
      neighborDegreeExcess G d x = k x := by
    intro x
    rw [neighborDegreeExcess_eq_sum_neighborFinset]
    have hterm : ∀ y ∈ G.neighborFinset x,
        G.degree y - d = if G.degree y = d + 1 then 1 else 0 := by
      intro y _hy
      rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
          G hfree hd hmin hcover hcard y with hy | hy <;> simp [hy]
    calc
      (∑ y ∈ G.neighborFinset x, (G.degree y - d)) =
          ∑ y ∈ G.neighborFinset x,
            if G.degree y = d + 1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        exact hterm
      _ = ((G.neighborFinset x).filter
          fun y => G.degree y = d + 1).card := by
        rw [Finset.card_filter]
      _ = k x := by
        congr 1
        ext y
        simp [H, squareOrderHighVertices, and_comm]
  have hpointLow : ∀ x ∈ L, (D.degree x : ℤ) = (d - 1 : Nat) - k x := by
    intro x hx
    have hxnot : x ∉ H := (Finset.mem_sdiff.mp hx).2
    have hxdegree : G.degree x = d := by
      rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
          G hfree hd hmin hcover hcard x with hxlow | hxhigh
      · exact hxlow
      · exact (hxnot (Finset.mem_filter.mpr ⟨by simp, hxhigh⟩)).elim
    have hcardBudget :
        Fintype.card V = d * (d - 1) + 1 + (d - 1) := by
      rw [hcard]
      have hd1 : 1 ≤ d := by omega
      calc
        d * d = d * ((d - 1) + 1) := by rw [Nat.sub_add_cancel hd1]
        _ = d * (d - 1) + d := by simp [Nat.mul_add]
        _ = d * (d - 1) + 1 + (d - 1) := by omega
    have hbudget :=
      secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
        G hfree (d := d) (q := d - 1) (by omega) hmin hcardBudget x
    rw [hxdegree] at hbudget
    simp only [Nat.sub_self, zero_mul, add_zero, hneighborExcess] at hbudget
    have hk : k x ≤ d - 1 := by
      have : k x ≤ d - 1 := by omega
      exact this
    rw [← Nat.cast_sub hk]
    congr 1
    have : D.degree x = d - 1 - k x := by
      exact Nat.eq_sub_of_add_eq hbudget
    exact this
  have hpointHigh : ∀ x ∈ H, D.degree x = 0 := by
    intro x hx
    exact (squareOrder_degree_succ_highRoot_structure
      G hfree hd hmin hcard (Finset.mem_filter.mp hx).2).1
  rw [← Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp)
    (f := fun x => ((D.degree x : ℤ) ^ 2))]
  have hhigh : (∑ x ∈ H, ((D.degree x : ℤ) ^ 2)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    simp [hpointHigh x hx]
  rw [hhigh, add_zero]
  calc
    (∑ x ∈ L, ((D.degree x : ℤ) ^ 2)) =
        ∑ x ∈ L, (((d - 1 : Nat) : ℤ) - k x) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hpointLow x hx]
    _ = (L.card : ℤ) * ((d - 1 : Nat) : ℤ) ^ 2 -
          2 * ((d - 1 : Nat) : ℤ) * (∑ x ∈ L, k x) +
          ∑ x ∈ L, (k x * k x : Nat) := by
      push_cast
      simp_rw [sub_sq]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      simp_rw [← Finset.mul_sum]
      ring_nf
    _ = ((d * d - H.card : Nat) : ℤ) * ((d - 1 : Nat) : ℤ) ^ 2 -
          2 * ((d - 1 : Nat) : ℤ) * ((d + 1 : Nat) : ℤ) * H.card +
          H.card * (H.card + d) := by
      rw [hLcard, hfirstLow, hsecondLow]
      push_cast
      ring_nf

end

end Erdos85

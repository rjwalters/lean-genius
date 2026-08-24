import Proofs.Erdos85FinalDyadicExceptionalProfile
import Proofs.Erdos85BinarySquareRegularParity

/-!
# Quantized defect-cut degrees at the final dyadic scale

The sparse adjacency equation has a global companion in the defect graph.
For nonzero displacement strictly below half the degree, that equation leaves
only two possible defect-cut degrees on either shore.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- A signed sum over a finite set is twice the positive part minus its
cardinality. -/
theorem sum_cutSign_over_finset
    {V : Type*} [DecidableEq V] (U S : Finset V) :
    ∑ x ∈ U, (if x ∈ S then (1 : ℤ) else -1) =
      2 * ((U ∩ S).card : ℤ) - U.card := by
  have hpoint (x : V) :
      (if x ∈ S then (1 : ℤ) else -1) =
        2 * (if x ∈ S then (1 : ℤ) else 0) - 1 := by
    by_cases hx : x ∈ S <;> simp [hx]
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp
  ring

/-- Positive-side arithmetic: divisibility of `2(a+r)` by `2h`, with
`0<r<h` and `a<2h`, leaves `a=h-r` or `a=2h-r`. -/
theorem twoLevel_positiveCut_of_dvd
    {h r a : ℕ} (hh : 0 < h) (hr : 0 < r) (hrh : r < h)
    (ha : a < 2 * h) (hdvd : 2 * h ∣ 2 * (a + r)) :
    a = h - r ∨ a = 2 * h - r := by
  obtain ⟨k, hk⟩ := hdvd
  have hk' : h * k = a + r := by nlinarith
  have hsumPos : 0 < a + r := by omega
  have hkPos : 0 < k := by
    by_contra h
    have : k = 0 := Nat.eq_zero_of_not_pos h
    simp [this] at hk'
    omega
  have hsumLt : a + r < 3 * h := by nlinarith
  have hkLt : k < 3 := by
    apply (Nat.mul_lt_mul_left hh).mp
    nlinarith
  have : k = 1 ∨ k = 2 := by omega
  rcases this with rfl | rfl <;> omega

/-- Negative-side arithmetic: if `2a = 2r - 2ht` over the integers, then
the cut degree is `r` or `h+r`. -/
theorem twoLevel_negativeCut_of_intEquation
    {h r a : ℕ} (hr : 0 < r) (hrh : r < h)
    (ha : a < 2 * h) (t : ℤ)
    (heq : 2 * (a : ℤ) = 2 * r - 2 * h * t) :
    a = r ∨ a = h + r := by
  have hlin : (a : ℤ) = r - h * t := by nlinarith
  by_cases har : a ≤ r
  · have htNonneg : 0 ≤ t := by
      by_contra ht
      have : t ≤ -1 := by omega
      nlinarith
    have htLe : t ≤ 0 := by
      by_contra ht
      have : 1 ≤ t := by omega
      nlinarith
    left
    have : t = 0 := by omega
    simp [this] at hlin
    exact_mod_cast hlin
  · have hra : r < a := by omega
    have htNeg : t < 0 := by
      by_contra ht
      have : 0 ≤ t := by omega
      nlinarith
    have htLower : -2 < t := by
      by_contra ht
      have : t ≤ -2 := by omega
      nlinarith
    have : t = -1 := by omega
    right
    rw [this] at hlin
    norm_num at hlin
    have haeq : a = r + h := by exact_mod_cast hlin
    omega

/-- Final-scale companion-defect equation specialized to canonical exceptional
signs and displacement `2r`. -/
theorem finalDyadic_companionDefect_apply_of_displacement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ}
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (v : V) :
    ∑ w ∈ (secondOrderDefectGraph G).neighborFinset v,
        (if w ∈ S then (1 : ℤ) else -1) =
      ((q : ℤ) - 1) * (if v ∈ S then (1 : ℤ) else -1) + 2 * r -
        (q : ℤ) * ∑ w ∈ G.neighborFinset v,
          exceptionalOccupancySign G S q w := by
  have hd : 2 * (S.card : ℤ) - (q * q : ℕ) = 2 * (r : ℤ) := by
    rw [← hcard]
    exact hdisp
  simpa [exceptionalOccupancySign] using
    binarySquare_trichotomy_companionDefect_apply
      G hfree (by rw [hqa]; positivity) hreg hcard S (r : ℤ) hd
      (finalDyadic_occupancy_trichotomy G hqa hreg S hdiv) v

/-- On the positive shore, the defect-cut degree is one of two values. -/
theorem finalDyadic_positiveShore_defectCutDegree_twoLevel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (v : V) (hv : v ∈ S) :
    ((secondOrderDefectGraph G).neighborFinset v \ S).card = 2 ^ j - r ∨
      ((secondOrderDefectGraph G).neighborFinset v \ S).card = q - r := by
  let D := secondOrderDefectGraph G
  let N := D.neighborFinset v
  let a := (N \ S).card
  let t : ℤ := ∑ w ∈ G.neighborFinset v,
    exceptionalOccupancySign G S q w
  have hDcard : N.card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree hq hreg hcard]
  have hpartition := Finset.card_inter_add_card_sdiff N S
  have hsigned := sum_cutSign_over_finset N S
  have hcomp := finalDyadic_companionDefect_apply_of_displacement
    G hfree hqa hreg hcard S hdiv hdisp v
  simp only [if_pos hv, mul_one] at hcomp
  have heq : (q : ℤ) * t = 2 * (a + r : ℕ) := by
    change (N ∩ S).card + a = N.card at hpartition
    rw [hDcard] at hpartition
    have hqsubZ : ((q - 1 : ℕ) : ℤ) = q - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hpartZ := congrArg (fun n : ℕ => (n : ℤ)) hpartition
    push_cast at hpartZ
    rw [hqsubZ] at hpartZ
    rw [hsigned, hDcard, hqsubZ] at hcomp
    change 2 * ((N ∩ S).card : ℤ) - (q - 1) =
      (q - 1) + 2 * r - q * t at hcomp
    push_cast
    nlinarith
  have ht : 0 ≤ t := by
    have hqpos : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
    nlinarith
  have htcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht
  have hdvd : 2 * 2 ^ j ∣ 2 * (a + r) := by
    refine ⟨t.toNat, ?_⟩
    rw [← hqa]
    have heqNat : q * t.toNat = 2 * (a + r) := by
      rw [← htcast] at heq
      exact_mod_cast heq
    exact heqNat.symm
  have ha : a < 2 * 2 ^ j := by
    have hasub : a ≤ N.card :=
      Finset.card_le_card Finset.sdiff_subset
    rw [hDcard, hqa] at hasub
    omega
  change a = 2 ^ j - r ∨ a = q - r
  rw [hqa]
  exact twoLevel_positiveCut_of_dvd
    (by positivity) hr hrhalf ha hdvd

/-- On the negative shore, the defect-cut degree is the complementary pair
of values. -/
theorem finalDyadic_negativeShore_defectCutDegree_twoLevel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 3 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (v : V) (hv : v ∉ S) :
    ((secondOrderDefectGraph G).neighborFinset v ∩ S).card = r ∨
      ((secondOrderDefectGraph G).neighborFinset v ∩ S).card = 2 ^ j + r := by
  let D := secondOrderDefectGraph G
  let N := D.neighborFinset v
  let a := (N ∩ S).card
  let t : ℤ := ∑ w ∈ G.neighborFinset v,
    exceptionalOccupancySign G S q w
  have hDcard : N.card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree hq hreg hcard]
  have hsigned := sum_cutSign_over_finset N S
  have hcomp := finalDyadic_companionDefect_apply_of_displacement
    G hfree hqa hreg hcard S hdiv hdisp v
  simp only [if_neg hv, mul_neg, mul_one] at hcomp
  have heqQ : 2 * (a : ℤ) = 2 * r - q * t := by
    have hqsubZ : ((q - 1 : ℕ) : ℤ) = q - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hsigned, hDcard, hqsubZ] at hcomp
    change 2 * (a : ℤ) - (q - 1) =
      -(q - 1) + 2 * r - q * t at hcomp
    nlinarith
  have heq : 2 * (a : ℤ) = 2 * r - 2 * (2 ^ j : ℕ) * t := by
    rw [hqa] at heqQ
    exact heqQ
  have ha : a < 2 * 2 ^ j := by
    have hasub : a ≤ N.card :=
      Finset.card_le_card Finset.inter_subset_left
    rw [hDcard, hqa] at hasub
    omega
  change a = r ∨ a = 2 ^ j + r
  exact twoLevel_negativeCut_of_intEquation
    hr hrhalf ha t heq

end


end Erdos85

#print axioms Erdos85.sum_cutSign_over_finset
#print axioms Erdos85.twoLevel_positiveCut_of_dvd
#print axioms Erdos85.twoLevel_negativeCut_of_intEquation
#print axioms Erdos85.finalDyadic_companionDefect_apply_of_displacement
#print axioms Erdos85.finalDyadic_positiveShore_defectCutDegree_twoLevel
#print axioms Erdos85.finalDyadic_negativeShore_defectCutDegree_twoLevel

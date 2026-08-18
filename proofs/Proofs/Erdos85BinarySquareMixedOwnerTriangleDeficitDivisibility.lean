import Proofs.Erdos85BinarySquareMixedOwnerTriangleDeficitNonnegative

/-!
# Uniform binary divisibility of the mixed-owner triangle deficit

The Goodman baseline in the binary square-order cubic congruence is itself a
multiple of the full congruence modulus.  Cancelling the remaining factor six
therefore quantizes the literal mixed-owner deficit at every binary order.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For `q = 2^k`, the literal mixed-owner triangle deficit is a multiple of
`q^2 / 2 = 2^(2k-1)`. -/
theorem binarySquare_regular_two_pow_pred_dvd_mixedOwnerTriangleDeficit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = (2 ^ k) * m c)
    (hsum : ∑ c, m c = 2 ^ k) :
    ((2 : ℤ) ^ (2 * k - 1)) ∣ binarySquareMixedOwnerTriangleDeficit G := by
  let q : ℤ := (2 : ℤ) ^ k
  let p : ℤ := (2 : ℤ) ^ (2 * k - 1)
  let δ : ℤ := binarySquareMixedOwnerTriangleDeficit G
  let B : ℤ := q ^ 2 * ((q ^ 2 - 1) * (q ^ 2 - 2) - 3 * (q - 1) * (q ^ 2 - q))
  have hq4 : 4 ≤ 2 ^ k := by
    calc
      4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hbaseline :
      (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) *
            (((2 ^ k) * (2 ^ k) : ℕ) - 1) *
            (((2 ^ k) * (2 ^ k) : ℕ) - 2) -
          3 * (((2 ^ k) * (2 ^ k) : ℕ) : ℤ) *
            ((2 ^ k) - 1 : ℕ) *
            (((2 ^ k) * (2 ^ k) : ℕ) - 1 - ((2 ^ k) - 1 : ℕ)) = B := by
    have hcq : (((2 ^ k : ℕ) : ℤ)) = q := by simp [q]
    have hcqq : ((((2 ^ k) * (2 ^ k) : ℕ) : ℤ)) = q ^ 2 := by
      rw [Nat.cast_mul, hcq]
      ring
    have hcq1 : ((((2 ^ k) - 1 : ℕ) : ℤ)) = q - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ k), hcq]
      norm_num
    rw [hcqq, hcq1]
    simp only [B]
    ring
  have hpq : q ^ 2 = 2 * p := by
    simp only [q, p, pow_two, ← pow_add]
    rw [show k + k = (2 * k - 1) + 1 by omega, pow_succ]
    ring
  have hthree : (3 : ℤ) ∣ q ^ 2 - 1 := by
    have hgeom : (4 : ℤ) - 1 ∣ (4 : ℤ) ^ k - 1 :=
      sub_one_dvd_pow_sub_one 4 k
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul] at hgeom
    simpa [q, ← pow_mul, mul_comm] using hgeom
  obtain ⟨t, ht⟩ := hthree
  have hB : (6 * p) ∣ B := by
    refine ⟨t * (q ^ 2 - 2) - (q - 1) * (q ^ 2 - q), ?_⟩
    simp only [B]
    rw [ht, hpq]
    ring
  have hcong :=
    binarySquare_regular_six_mul_two_pow_pred_dvd_goodman_sub_mixedOwnerDeficit
      G hfree hk hreg hcard m hm hsum
  rw [hbaseline] at hcong
  change (6 * p) ∣ B - 6 * δ at hcong
  have hsix : (6 * p) ∣ 6 * δ := by
    obtain ⟨w, hw⟩ := dvd_sub hB hcong
    refine ⟨w, ?_⟩
    rw [← hw]
    ring
  obtain ⟨z, hz⟩ := hsix
  refine ⟨z, ?_⟩
  change δ = p * z
  change 6 * δ = (6 * p) * z at hz
  nlinarith

/-- Uniform rigidity below the first positive quantum: if the mixed-owner
triangle deficit is smaller than `q^2 / 2`, it vanishes. -/
theorem binarySquare_regular_mixedOwnerTriangleDeficit_eq_zero_of_lt_two_pow_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = (2 ^ k) * m c)
    (hsum : ∑ c, m c = 2 ^ k)
    (hlt : binarySquareMixedOwnerTriangleDeficit G <
      (2 : ℤ) ^ (2 * k - 1)) :
    binarySquareMixedOwnerTriangleDeficit G = 0 := by
  have hnonneg := binarySquareMixedOwnerTriangleDeficit_nonneg G hfree
    (by
      have : 4 ≤ 2 ^ k := by
        calc
          4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [hcard]
      nlinarith)
  obtain ⟨z, hz⟩ :=
    binarySquare_regular_two_pow_pred_dvd_mixedOwnerTriangleDeficit
      G hfree hk hreg hcard m hm hsum
  have hp : (0 : ℤ) < 2 ^ (2 * k - 1) := by positivity
  by_contra hne
  have hδpos : 0 < binarySquareMixedOwnerTriangleDeficit G :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hzpos : 0 < z := by
    apply pos_of_mul_pos_left (b := (2 : ℤ) ^ (2 * k - 1))
    · rw [mul_comm, ← hz]
      exact hδpos
    · exact hp.le
  have hone : (1 : ℤ) ≤ z := by omega
  have hquantum_le :
      (2 : ℤ) ^ (2 * k - 1) ≤ binarySquareMixedOwnerTriangleDeficit G := by
    rw [hz]
    simpa using mul_le_mul_of_nonneg_left hone hp.le
  omega

/-- Uniform gap theorem: the mixed-owner deficit is either zero or at least
the first positive quantum `q^2 / 2`. -/
theorem binarySquare_regular_mixedOwnerTriangleDeficit_eq_zero_or_two_pow_pred_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : 2 ≤ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = (2 ^ k) * m c)
    (hsum : ∑ c, m c = 2 ^ k) :
    binarySquareMixedOwnerTriangleDeficit G = 0 ∨
      (2 : ℤ) ^ (2 * k - 1) ≤ binarySquareMixedOwnerTriangleDeficit G := by
  by_cases hzero : binarySquareMixedOwnerTriangleDeficit G = 0
  · exact Or.inl hzero
  · right
    by_contra hnotle
    have hlt : binarySquareMixedOwnerTriangleDeficit G <
        (2 : ℤ) ^ (2 * k - 1) := by omega
    exact hzero
      (binarySquare_regular_mixedOwnerTriangleDeficit_eq_zero_of_lt_two_pow_pred
        G hfree hk hreg hcard m hm hsum hlt)

end

end Erdos85

#print axioms
  Erdos85.binarySquare_regular_two_pow_pred_dvd_mixedOwnerTriangleDeficit
#print axioms
  Erdos85.binarySquare_regular_mixedOwnerTriangleDeficit_eq_zero_of_lt_two_pow_pred
#print axioms
  Erdos85.binarySquare_regular_mixedOwnerTriangleDeficit_eq_zero_or_two_pow_pred_le

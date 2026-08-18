import Proofs.Erdos85BinarySquareCenteredOwnerTriangleDivisibility

/-!
# Binary-family triangle divisibility

For `q = 2^k`, the cubic owner/defect law loses only the single factor two
contained in `6`.  Thus the combined triangle count is divisible by
`2^(2k-1)`, uniformly in the binary exponent.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Elementary two-primary cancellation used by the graph theorem. -/
theorem two_pow_two_mul_pred_dvd_of_sq_dvd_six_mul
    {k : ℕ} (hk : 1 ≤ k) {T : ℤ}
    (h : ((2 : ℤ) ^ k) ^ 2 ∣ 6 * T) :
    (2 : ℤ) ^ (2 * k - 1) ∣ T := by
  let p : ℤ := (2 : ℤ) ^ (2 * k - 1)
  have hp : ((2 : ℤ) ^ k) ^ 2 = 2 * p := by
    dsimp [p]
    rw [pow_two, ← pow_add]
    have he : k + k = (2 * k - 1) + 1 := by omega
    rw [he, pow_succ]
    ring
  obtain ⟨z, hz⟩ := h
  have hthree : p ∣ 3 * T := by
    refine ⟨z, ?_⟩
    rw [hp] at hz
    ring_nf at hz ⊢
    nlinarith
  have hcop : IsCoprime p (3 : ℤ) := by
    dsimp [p]
    exact (show IsCoprime (2 : ℤ) 3 by norm_num).pow_left
  exact hcop.dvd_of_dvd_mul_left hthree

/-- **Uniform binary combined-triangle divisibility.**  For `q=2^k`, the
sum of defect and owner triangle-minor counts is divisible by `2^(2k-1)`. -/
theorem binarySquare_regular_two_pow_pred_dvd_sum_owner_defect_triangleMinorCounts
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
    (2 : ℤ) ^ (2 * k - 1) ∣
      ((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card : ℤ) +
        ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
          ((adjacencyTriangleMinorFinset
            (componentOwnerGraph G (secondOrderDefectGraph G) c)).card : ℤ) := by
  let T : ℤ :=
    ((adjacencyTriangleMinorFinset (secondOrderDefectGraph G)).card : ℤ) +
      ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
        ((adjacencyTriangleMinorFinset
          (componentOwnerGraph G (secondOrderDefectGraph G) c)).card : ℤ)
  have hq : 3 ≤ 2 ^ k := by
    have : 4 ≤ 2 ^ k := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have hdvd : (((2 ^ k : ℕ) : ℤ) ^ 2) ∣ 6 * T := by
    simpa [T] using
      (binarySquare_regular_sq_dvd_six_mul_sum_owner_defect_triangleMinorCounts
        G hfree hq hreg hcard m hm hsum)
  push_cast at hdvd
  exact two_pow_two_mul_pred_dvd_of_sq_dvd_six_mul (by omega) hdvd

end

end Erdos85

#print axioms Erdos85.two_pow_two_mul_pred_dvd_of_sq_dvd_six_mul
#print axioms
  Erdos85.binarySquare_regular_two_pow_pred_dvd_sum_owner_defect_triangleMinorCounts

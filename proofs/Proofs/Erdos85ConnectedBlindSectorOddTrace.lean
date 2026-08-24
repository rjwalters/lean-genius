import Proofs.Erdos85BinarySquareDyadicSignedTerminal
import Proofs.Erdos85ExcessEigenspace

/-!
# The odd-dyadic blind sector has zero trace

The incidence bottleneck has one exact nonprincipal blind sector, the
defect eigenvalue `mu = -1`.  On that eigenspace the ambient adjacency
operator squares to `q`.  When `q = 2^k` with odd `k`, this scalar is not a
rational square, so the two square-root multiplicities pair and the
restricted adjacency trace vanishes.

This removes the blind sector as a carrier of the required trace in the
odd-exponent `NONBIP-CONNECTED` branch.  It does not eliminate designated
square-in-eigenfield sectors with `mu != -1`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An odd power of two is not a square in the rationals. -/
theorem not_isSquare_twoPow_rat_of_odd (k : ℕ) (hk : Odd k) :
    ¬ IsSquare (((2 ^ k : ℕ) : ℚ)) := by
  obtain ⟨m, rfl⟩ := hk
  intro hsquare
  have hfactor : IsSquare ((((2 ^ m : ℕ) : ℚ)) ^ 2) :=
    IsSquare.sq _
  have htwo : IsSquare (2 : ℚ) := by
    have hquot := hsquare.div hfactor
    have heq :
        (((2 ^ (2 * m + 1) : ℕ) : ℚ) /
          (((2 ^ m : ℕ) : ℚ)) ^ 2) = 2 := by
      norm_num [pow_add, pow_succ]
      rw [show 2 * m = m + m by omega, pow_add]
      field_simp
    rw [heq] at hquot
    exact hquot
  norm_num at htwo

/-- At odd dyadic exponent, the ambient adjacency trace on the exact
`mu=-1` defect eigenspace is zero. -/
theorem binarySquare_oddDyadic_blindSector_trace_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q k : ℕ} (hq : 3 ≤ q)
    (hqpow : q = 2 ^ k) (hk : Odd k)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    let A := G.adjMatrix ℚ
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let hcomm : A * D = D * A :=
      adjMatrix_comm_secondOrderDefect_of_regular_field G hfree hreg
    LinearMap.trace ℚ (defectEigenspace D (-1 : ℚ))
      (defectEigenspaceRestrict A hcomm (-1 : ℚ)) = 0 := by
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = q - 1 :=
    binarySquare_regular_secondOrderDefect_degree_eq
      G hfree hq hreg hcard
  have hDreg' : ∀ x, (secondOrderDefectGraph G).degree x = (q - 3) + 2 := by
    intro x
    rw [hDreg x]
    omega
  apply graph_trace_defectEigenspaceRestrict_eq_zero_of_regular_excess_field
    (K := ℚ) G hfree hreg hDreg'
  · intro hbad
    have hnonneg : (0 : ℚ) ≤ ((q - 3 : ℕ) : ℚ) + 2 := by positivity
    linarith
  · rw [hqpow]
    norm_num
    simpa only [Nat.cast_ofNat, Nat.cast_pow] using
      not_isSquare_twoPow_rat_of_odd k hk

end


end Erdos85

#print axioms Erdos85.not_isSquare_twoPow_rat_of_odd
#print axioms Erdos85.binarySquare_oddDyadic_blindSector_trace_eq_zero

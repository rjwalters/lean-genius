import Mathlib

/-!
# Proper owner colors cannot have the strongly-regular multiplicities

For a normalized defect component of size `q * m`, the shifted owner matrix
`O + mI` has rank exactly `q * m`.  If the owner graph were connected strongly
regular, its bottom eigenvalue `-m` would therefore have multiplicity
`q^2 - q*m`, leaving one nonprincipal eigenvalue `r` with multiplicity
`q*m - 1`.  The zero trace then gives the integer equation excluded below.

This file isolates the arithmetic terminal.  The graph-to-equation bridge is
kept explicit so that it can be connected to the strongly-regular matrix API
without duplicating the already-banked exact-rank theorem.
-/

namespace Erdos85

/-- The trace equation forced by the proposed strongly-regular owner spectrum
is impossible for a proper normalized part `1 < m < q`.

The key congruence is elementary but sharp.  Put `d = q*m - 1` and
`E = q^2 - q*m - q + 1`.  From `d*r = m*E`, multiplication by `m` and
reduction modulo `d` give `d ∣ (m - 1)`, although `0 < m - 1 < d`. -/
theorem false_of_proper_owner_srg_trace_equation
    {q m r : ℤ} (hq : 2 ≤ q) (hm : 2 ≤ m) (hmq : m < q)
    (htrace : (q * m - 1) * r =
      m * (q * q - q * m - q + 1)) : False := by
  let d : ℤ := q * m - 1
  let E : ℤ := q * q - q * m - q + 1
  let t : ℤ := m * r - (q * m - (m * m + m - 1))
  have hd : 0 < d := by
    dsimp [d]
    nlinarith
  have hlower : -d < 1 - m := by
    dsimp [d]
    nlinarith
  have hupper : 1 - m < d := by
    dsimp [d]
    nlinarith
  have hidentity : m * m * E =
      d * (q * m - (m * m + m - 1)) + (1 - m) := by
    dsimp [d, E]
    ring
  have hmultiple : d * t = 1 - m := by
    dsimp [t]
    have hscaled := congrArg (fun z : ℤ => m * z) htrace
    dsimp [d, E] at hscaled hidentity ⊢
    nlinarith
  by_cases ht : t = 0
  · rw [ht, mul_zero] at hmultiple
    nlinarith
  · rcases lt_or_gt_of_ne ht with htneg | htpos
    · have htle : t ≤ -1 := by omega
      have hprod : d * t ≤ d * (-1) :=
        mul_le_mul_of_nonneg_left htle (le_of_lt hd)
      rw [hmultiple] at hprod
      nlinarith
    · have htge : 1 ≤ t := by omega
      have hprod : d * 1 ≤ d * t :=
        mul_le_mul_of_nonneg_left htge (le_of_lt hd)
      rw [hmultiple] at hprod
      nlinarith

#print axioms false_of_proper_owner_srg_trace_equation

end Erdos85

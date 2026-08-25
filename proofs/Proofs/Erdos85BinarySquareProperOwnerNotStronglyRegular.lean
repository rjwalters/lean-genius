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

/-- A matrix form of the same obstruction, tailored to the centered owner
operator.  An idempotent matrix has trace equal to the dimension of its
range.  The proposed strongly-regular owner algebra would instead give rank
`q*m-1` and trace `m*(q-1)`, whose difference is `m-1`.

This lemma leaves the graph-facing work only the construction of the
idempotent centered owner projector. -/
theorem false_of_proper_owner_idempotent_trace_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) {q m : ℕ} (hq : 1 ≤ q) (hm : 2 ≤ m)
    (hidem : P * P = P)
    (hrank : P.rank = q * m - 1)
    (htrace : P.trace = (m * (q - 1) : ℕ)) : False := by
  have hidemLin : IsIdempotentElem P.toLin' := by
    simpa only [IsIdempotentElem, Module.End.mul_eq_comp,
      Matrix.toLin'_mul] using congrArg Matrix.toLin' hidem
  have hprojTrace : LinearMap.trace ℝ (V → ℝ) P.toLin' =
      (Module.finrank ℝ (LinearMap.range P.toLin') : ℝ) :=
    (LinearMap.IsIdempotentElem.isProj_range P.toLin' hidemLin).trace
  have htraceLin : LinearMap.trace ℝ (V → ℝ) P.toLin' =
      (m * (q - 1) : ℕ) := by
    rw [Matrix.trace_toLin'_eq]
    exact htrace
  have hrange : Module.finrank ℝ (LinearMap.range P.toLin') = q * m - 1 := by
    change Module.finrank ℝ (LinearMap.range P.mulVecLin) = q * m - 1
    simpa only [Matrix.rank] using hrank
  rw [htraceLin, hrange] at hprojTrace
  have hnat : m * (q - 1) = q * m - 1 := by
    exact_mod_cast hprojTrace
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm m q] at hnat
  have hmle : m ≤ q * m := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right m hq
  have hone : 1 ≤ q * m := le_trans (by omega : 1 ≤ m) hmle
  omega

#print axioms false_of_proper_owner_srg_trace_equation

#print axioms false_of_proper_owner_idempotent_trace_rank

end Erdos85

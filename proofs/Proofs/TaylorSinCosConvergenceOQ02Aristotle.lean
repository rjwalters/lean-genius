/-
  Aristotle targets for TaylorSinCosConvergenceOQ02
  Partial sum bridge lemmas for Taylor sin/cos convergence.
  See TaylorSinCosConvergenceOQ02.lean for the main formalization.

  The two target sorries connect Taylor partial sums (defined via iteratedDeriv)
  to the alternating series (cosSeries/sinSeries). The proof uses:
  - iteratedDeriv (2k) cos 0 = (-1)^k  (even order: cosine evaluations)
  - iteratedDeriv (2k+1) cos 0 = 0     (odd order: sine zero at 0)
  - iteratedDeriv (2k) sin 0 = 0       (even order: sine zero at 0)
  - iteratedDeriv (2k+1) sin 0 = (-1)^k (odd order: cosine evaluations)

  These helper lemmas are re-exposed here (formerly private in the main file)
  so Aristotle can use them when proving the reindexing targets.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic
import Proofs.TaylorSinCosConvergence
import Proofs.EulerIdentityOQ01OQ01

open Complex Real TaylorSinCosConvergence EulerIdentityOQ01OQ01
open scoped Nat

namespace TaylorSinCosConvergenceOQ02Aristotle

/-- iteratedDeriv (2n) cos 0 = (-1)^n — the even-order derivatives of cosine at 0. -/
theorem iteratedDeriv_cos_even_zero (n : ℕ) :
    iteratedDeriv (2 * n) Real.cos 0 = (-1 : ℝ) ^ n := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := n.even_or_odd
  · have h : iteratedDeriv (4 * m) Real.cos = Real.cos := by
      induction m with
      | zero => exact iteratedDeriv_cos_zero
      | succ k ih =>
        rw [show 4*(k+1) = 4*k+4 from by ring, iteratedDeriv_cos_add_four, ih]
    simp [h, Real.cos_zero, show (-1:ℝ)^(2*m) = 1 from by rw [pow_mul]; norm_num]
  · have h : iteratedDeriv (4*m+2) Real.cos = fun t => -Real.cos t := by
      induction m with
      | zero => exact iteratedDeriv_cos_two
      | succ k ih =>
        rw [show 4*(k+1)+2 = (4*k+2)+4 from by ring, iteratedDeriv_cos_add_four, ih]
    simp [h, Real.cos_zero, show (-1:ℝ)^(2*m+1) = -1 from by rw [pow_succ, pow_mul]; norm_num]

/-- iteratedDeriv (2n+1) cos 0 = 0 — the odd-order derivatives of cosine at 0. -/
theorem iteratedDeriv_cos_odd_zero (n : ℕ) :
    iteratedDeriv (2*n+1) Real.cos 0 = 0 := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := n.even_or_odd
  · have h : iteratedDeriv (4*m+1) Real.cos = fun t => -Real.sin t := by
      induction m with
      | zero => exact iteratedDeriv_cos_one
      | succ k ih =>
        rw [show 4*(k+1)+1 = (4*k+1)+4 from by ring, iteratedDeriv_cos_add_four, ih]
    simp [h, Real.sin_zero]
  · have h : iteratedDeriv (4*m+3) Real.cos = Real.sin := by
      induction m with
      | zero => exact iteratedDeriv_cos_three
      | succ k ih =>
        rw [show 4*(k+1)+3 = (4*k+3)+4 from by ring, iteratedDeriv_cos_add_four, ih]
    simp [h, Real.sin_zero]

/-- iteratedDeriv (2n) sin 0 = 0 — the even-order derivatives of sine at 0. -/
theorem iteratedDeriv_sin_even_zero (n : ℕ) :
    iteratedDeriv (2*n) Real.sin 0 = 0 := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := n.even_or_odd
  · have h : iteratedDeriv (4*m) Real.sin = Real.sin := by
      induction m with
      | zero => exact iteratedDeriv_sin_zero
      | succ k ih =>
        rw [show 4*(k+1) = 4*k+4 from by ring, iteratedDeriv_sin_add_four, ih]
    simp [h, Real.sin_zero]
  · have h : iteratedDeriv (4*m+2) Real.sin = fun t => -Real.sin t := by
      induction m with
      | zero => exact iteratedDeriv_sin_two
      | succ k ih =>
        rw [show 4*(k+1)+2 = (4*k+2)+4 from by ring, iteratedDeriv_sin_add_four, ih]
    simp [h, Real.sin_zero]

/-- iteratedDeriv (2n+1) sin 0 = (-1)^n — the odd-order derivatives of sine at 0. -/
theorem iteratedDeriv_sin_odd_zero (n : ℕ) :
    iteratedDeriv (2*n+1) Real.sin 0 = (-1:ℝ)^n := by
  obtain ⟨m, rfl⟩ | ⟨m, rfl⟩ := n.even_or_odd
  · have h : iteratedDeriv (4*m+1) Real.sin = Real.cos := by
      induction m with
      | zero => exact iteratedDeriv_sin_one
      | succ k ih =>
        rw [show 4*(k+1)+1 = (4*k+1)+4 from by ring, iteratedDeriv_sin_add_four, ih]
    simp [h, Real.cos_zero, show (-1:ℝ)^(2*m) = 1 from by rw [pow_mul]; norm_num]
  · have h : iteratedDeriv (4*m+3) Real.sin = fun t => -Real.cos t := by
      induction m with
      | zero => exact iteratedDeriv_sin_three
      | succ k ih =>
        rw [show 4*(k+1)+3 = (4*k+3)+4 from by ring, iteratedDeriv_sin_add_four, ih]
    simp [h, Real.cos_zero, show (-1:ℝ)^(2*m+1) = -1 from by rw [pow_succ, pow_mul]; norm_num]

/-- cosPartialSum (2n) x = ∑_{k≤n} cosSeries x k.
Bridge: Taylor partial sums = alternating cosine series partial sums.
Uses: even-order derivatives give (-1)^k; odd-order derivatives vanish. -/
theorem cosPartialSum_eq_cosSeries_sum (x : ℝ) (n : ℕ) :
    cosPartialSum (2 * n) x = ∑ k ∈ Finset.range (n + 1), cosSeries x k := by
  sorry

/-- sinPartialSum (2n+1) x = ∑_{k≤n} sinSeries x k.
Bridge: Taylor partial sums = alternating sine series partial sums.
Uses: odd-order derivatives give (-1)^k; even-order derivatives vanish. -/
theorem sinPartialSum_eq_sinSeries_sum (x : ℝ) (n : ℕ) :
    sinPartialSum (2 * n + 1) x = ∑ k ∈ Finset.range (n + 1), sinSeries x k := by
  sorry

end TaylorSinCosConvergenceOQ02Aristotle

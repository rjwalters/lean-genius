import Mathlib.Tactic

/- Aristotle v4.31 drift probe for lean-genius issue #38066 gate (b).
   Three representative statements exercising drift-prone Mathlib API:
   real analysis names, Finset.range induction, factorial/choose identities.
   The test is whether Aristotle-generated proofs elaborate on
   Lean v4.31.0 / Mathlib 9a9483a9. -/

theorem probe_log_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b) = Real.log a + Real.log b := by
  exact Real.log_mul ha.ne' hb.ne'

theorem probe_sum_odd (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

theorem probe_choose_factorial (n k : ℕ) (h : k ≤ n) :
    n.choose k * k.factorial * (n - k).factorial = n.factorial := by
  exact Nat.choose_mul_factorial_mul_factorial h

/-
  Factorial Telescoping Series Converges:  ∑_{k=1}^{∞} k / (k+1)! = 1

  Follow-up (oq-01) to `factorial-telescoping-sum-oq-01`
  (∑_{k=1}^{n} k · k! = (n+1)! − 1).

  Status: VERIFIED (0 sorries, 0 axioms, no native_decide).

  The parent identity is a *finite* statement over ℕ.  Dividing the telescoping
  step by (k+1)! turns it into a genuinely analytic statement: the normalized
  series ∑ k/(k+1)! converges, and its value is exactly 1.

  Statements:
    (1)  term_telescope :  k/(k+1)! = 1/k! − 1/(k+1)!            (over ℝ)
    (2)  sum_Icc        :  ∑_{k=1}^{n} k/(k+1)! = 1 − 1/(n+1)!    (closed form)
    (3)  sum_lt_one     :  every partial sum is strictly below 1
    (4)  tendsto_one    :  the partial sums converge to 1

  Key insight (telescoping in a field):
    Because (k+1)! = (k+1)·k!, we have
        k/(k+1)! = ((k+1) − 1)/(k+1)! = 1/k! − 1/(k+1)!,
    so the sum telescopes to  1/1! − 1/(n+1)! = 1 − 1/(n+1)!.
    Since (n+1)! ≥ n+1 → ∞, the tail 1/(n+1)! → 0 and the series sums to 1.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open Finset Nat Filter Topology

namespace FactorialTelescopingConverges

/-- **Term telescoping (in ℝ).**  `k/(k+1)! = 1/k! − 1/(k+1)!`.

    This is the parent's integer telescoping step `k·k! = (k+1)! − k!` divided
    through by `(k+1)!`; it is what makes the sum collapse over ℝ. -/
theorem term_telescope (k : ℕ) :
    (k : ℝ) / ((k + 1)! : ℝ) = 1 / (k ! : ℝ) - 1 / ((k + 1)! : ℝ) := by
  have h : ((k + 1)! : ℝ) = ((k : ℝ) + 1) * (k ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk : (k ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [h]
  field_simp
  ring

/-- **Closed form for the partial sums.**  `∑_{k=1}^{n} k/(k+1)! = 1 − 1/(n+1)!`. -/
theorem sum_Icc (n : ℕ) :
    ∑ k ∈ Icc 1 n, (k : ℝ) / ((k + 1)! : ℝ) = 1 - 1 / ((n + 1)! : ℝ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih, term_telescope (m + 1)]
    ring

/-- **Partial sums are strictly below the limit.**  Each finite sum is `< 1`,
    because the missing tail `1/(n+1)!` is strictly positive. -/
theorem sum_lt_one (n : ℕ) :
    ∑ k ∈ Icc 1 n, (k : ℝ) / ((k + 1)! : ℝ) < 1 := by
  rw [sum_Icc]
  have : (0 : ℝ) < 1 / ((n + 1)! : ℝ) := by positivity
  linarith

/-- **Convergence to 1.**  The partial sums `∑_{k=1}^{n} k/(k+1)!` tend to `1`,
    i.e. the series `∑_{k≥1} k/(k+1)!` sums to `1`. -/
theorem tendsto_one :
    Tendsto (fun n : ℕ => ∑ k ∈ Icc 1 n, (k : ℝ) / ((k + 1)! : ℝ)) atTop (nhds 1) := by
  have hform :
      (fun n : ℕ => ∑ k ∈ Icc 1 n, (k : ℝ) / ((k + 1)! : ℝ))
        = fun n : ℕ => 1 - 1 / ((n + 1)! : ℝ) := by
    funext n; exact sum_Icc n
  rw [hform]
  have htail : Tendsto (fun n : ℕ => 1 / ((n + 1)! : ℝ)) atTop (nhds 0) := by
    refine squeeze_zero (fun n => by positivity)
      (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.self_le_factorial (n + 1)
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / ((n + 1)! : ℝ)) atTop (nhds (1 - 0)) :=
    Tendsto.sub tendsto_const_nhds htail
  simpa using h1

end FactorialTelescopingConverges

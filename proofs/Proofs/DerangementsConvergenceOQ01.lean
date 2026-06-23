/-
  k Fixed Points: Convergence Rate for Permutation Fixed-Point Probabilities
  Open Question: derangements-convergence-oq-01

  For a uniformly random permutation of Fin n, let X_n = number of fixed points.
  The probability of exactly k fixed points is:

    P(X_n = k) = C(n,k) · D(n-k) / n! = (1/k!) · (D(n-k)/(n-k)!)

  Since D(m)/m! → e⁻¹ (Mathlib: numDerangements_tendsto_inv_e), we get:

    P(X_{n+k} = k) → e⁻¹/k!  as n → ∞

  This is the Poisson(1) mass function: P(Pois(1) = k) = e⁻¹/k!.

  We also prove the rate bound: |P(X_n = k) - e⁻¹/k!| ≤ 1/(k!·(n-k+1)!).
  This requires the alternating series bound |D(n)/n! - e⁻¹| ≤ 1/(n+1)!, which
  is proved by sorry (it is the content of DerangementsConvergence.lean, which
  has pre-existing Mathlib syntax issues preventing import).

  ## Main Results

  - `probKFixed_eq` (PROVED): P(X_n = k) = (1/k!) · (D(n-k)/(n-k)!)
  - `probKFixed_succ_eq` (PROVED): P(X_{n+k} = k) = (1/k!) · D(n)/n!
  - `derangements_rate` (SORRY): |D(n)/n! - e⁻¹| ≤ 1/(n+1)! [alternating series est]
  - `kFixed_convergence_rate` (PROVED modulo sorry): |P(X_n = k) - e⁻¹/k!| ≤ 1/(k!·(n-k+1)!)
  - `kFixed_tendsto` (PROVED): P(X_{n+k} = k) → e⁻¹/k! as n → ∞

  ## Note on derangements_rate

  The sorry states the alternating series bound for D(n)/n!. The mathematical proof is:
  D(n)/n! = ∑_{k=0}^n (-1)^k/k! (partial sum of exp(-1) Taylor series).
  By the alternating series estimation theorem: |D(n)/n! - e⁻¹| = |tail| ≤ 1/(n+1)!.
  This was proved in DerangementsConvergence.lean but that file has pre-existing
  Mathlib API issues (∑ k in vs ∑ k ∈ syntax) preventing compilation.
-/

import Proofs.DerangementsConvergence
import Proofs.DerangementsOQ02
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Tactic

open Nat Real Filter Topology

namespace KFixedConvergence

-- ============================================================
-- §1. PROBABILITY OF EXACTLY k FIXED POINTS
-- ============================================================

/-- P(X_n = k) = S(n,k)/n! where S(n,k) = C(n,k)·D(n-k) counts permutations
    of Fin n with exactly k fixed points. -/
noncomputable def probKFixed (n k : ℕ) : ℝ :=
  (n.choose k * numDerangements (n - k) : ℕ) / (n.factorial : ℝ)

-- ============================================================
-- §2. ALGEBRAIC IDENTITIES
-- ============================================================

/-- Key algebraic identity: P(X_n = k) = (1/k!) · (D(n-k)/(n-k)!) for k ≤ n.
    Proof: C(n,k)·D(n-k)/n! = [n!/(k!·(n-k)!)]·D(n-k)/n! = D(n-k)/(k!·(n-k)!) -/
lemma probKFixed_eq (n k : ℕ) (hk : k ≤ n) :
    probKFixed n k = 1 / (k.factorial : ℝ) *
      ((numDerangements (n - k) : ℝ) / ((n - k).factorial : ℝ)) := by
  unfold probKFixed
  have hk_ne : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk_ne : ((n - k).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have hn_ne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hchoose : (n.choose k : ℝ) * k.factorial * (n - k).factorial = n.factorial :=
    by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  push_cast
  field_simp [hk_ne, hnk_ne, hn_ne]
  linear_combination (numDerangements (n - k) : ℝ) * hchoose

/-- Reparametrized: P(X_{n+k} = k) = (1/k!) · (D(n)/n!). -/
lemma probKFixed_succ_eq (n k : ℕ) :
    probKFixed (n + k) k = 1 / (k.factorial : ℝ) *
      ((numDerangements n : ℝ) / (n.factorial : ℝ)) := by
  rw [probKFixed_eq (n + k) k (Nat.le_add_left k n)]
  simp [Nat.add_sub_cancel_left]

-- ============================================================
-- §3. RATE BOUND (modulo alternating series sorry)
-- ============================================================

/-- Alternating series bound for derangements: |D(n)/n! - e⁻¹| ≤ 1/(n+1)!
    SORRY: This is the content of DerangementsConvergence.derangements_convergence_rate.
    Mathematical proof: D(n)/n! = ∑_{k=0}^n (-1)^k/k! by numDerangements_sum.
    The alternating series est. gives |partial sum - full sum| ≤ |next term| = 1/(n+1)!. -/
lemma derangements_rate (n : ℕ) :
    |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| ≤
    1 / ((n + 1).factorial : ℝ) :=
  derangements_convergence_rate n

/-- **Convergence rate**: |P(X_n = k) - e⁻¹/k!| ≤ 1/(k!·(n-k+1)!) for k ≤ n.
    Proof: factor out 1/k! and apply derangements_rate to n-k. -/
theorem kFixed_convergence_rate (n k : ℕ) (hk : k ≤ n) :
    |probKFixed n k - rexp (-1) / (k.factorial : ℝ)| ≤
    1 / ((k.factorial : ℝ) * (((n - k) + 1).factorial : ℝ)) := by
  rw [probKFixed_eq n k hk]
  have hk_pos : (0 : ℝ) < k.factorial := Nat.cast_pos.mpr k.factorial_pos
  have hrw : 1 / (k.factorial : ℝ) * ((numDerangements (n - k) : ℝ) / ((n - k).factorial : ℝ)) -
      rexp (-1) / (k.factorial : ℝ) =
      1 / (k.factorial : ℝ) * ((numDerangements (n - k) : ℝ) / ((n - k).factorial : ℝ) - rexp (-1)) := by
    ring
  rw [hrw, abs_mul, abs_of_pos (by positivity)]
  calc 1 / (k.factorial : ℝ) * |(numDerangements (n - k) : ℝ) / ((n - k).factorial : ℝ) - rexp (-1)|
      ≤ 1 / (k.factorial : ℝ) * (1 / (((n - k) + 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (derangements_rate (n - k)) (by positivity)
    _ = 1 / ((k.factorial : ℝ) * (((n - k) + 1).factorial : ℝ)) := by ring

-- ============================================================
-- §4. CONVERGENCE TO POISSON(1) MASS
-- ============================================================

/-- **Main theorem**: P(X_{n+k} = k) → e⁻¹/k! as n → ∞.

    This is the Poisson(1) distribution mass function at k.
    Proof: P(X_{n+k} = k) = (1/k!)·D(n)/n!, and D(n)/n! → e⁻¹ (Mathlib). -/
theorem kFixed_tendsto (k : ℕ) :
    Tendsto (fun n => probKFixed (n + k) k) atTop (nhds (rexp (-1) / (k.factorial : ℝ))) := by
  simp_rw [probKFixed_succ_eq]
  rw [show rexp (-1) / (k.factorial : ℝ) = 1 / (k.factorial : ℝ) * rexp (-1) by ring]
  have hconst : Tendsto (fun _ : ℕ => 1 / (k.factorial : ℝ)) atTop (nhds (1 / k.factorial)) :=
    tendsto_const_nhds
  exact hconst.mul numDerangements_tendsto_inv_e

/-- k=0 case: P(X_n = 0) → e⁻¹ (derangement convergence). -/
theorem kFixed_zero_tendsto :
    Tendsto (fun n => probKFixed n 0) atTop (nhds (rexp (-1))) := by
  have h := kFixed_tendsto 0
  simp only [add_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  exact h

-- ============================================================
-- §5. COMPARISON OF RATES
-- ============================================================

/-- For k ≥ 1, the k-fixed rate is tighter than the derangements rate
    (the k! factor in the denominator helps). -/
theorem kFixed_rate_tighter (n k : ℕ) (hk : k ≤ n) (hk1 : 1 ≤ k) :
    1 / ((k.factorial : ℝ) * (((n - k) + 1).factorial : ℝ)) ≤
    1 / (((n - k) + 1).factorial : ℝ) := by
  apply div_le_div_of_nonneg_left one_pos.le
  · exact Nat.cast_pos.mpr (n - k + 1).factorial_pos
  · have hk_fact : (1 : ℝ) ≤ k.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr k.factorial_ne_zero
    have hnk_fact_pos : (0 : ℝ) < ((n - k + 1).factorial : ℝ) :=
      Nat.cast_pos.mpr (n - k + 1).factorial_pos
    nlinarith [mul_pos (by linarith : (0 : ℝ) < k.factorial) hnk_fact_pos]

end KFixedConvergence

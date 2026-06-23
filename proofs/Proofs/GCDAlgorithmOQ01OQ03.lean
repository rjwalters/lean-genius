import Proofs.GCDAlgorithmOQ01
import Mathlib

/-
# Golden Ratio Fibonacci Identity for GCD Algorithm Bounds

## Research Problem: gcd-algorithm-oq-01-oq-03

### Part I: Removing the 10^20 Restriction (Pure Arithmetic)
Proves fib(5k+2) ≥ 10^k for ALL k using only Fibonacci recurrence,
extending Lamé's 5-digit bound to all b with no restriction.

### Part II: Binet's Formula (Golden Ratio Connection)
Proves the golden ratio Fibonacci identity:
    fib(n) = (φⁿ - ψⁿ) / √5
where φ = (1+√5)/2 and ψ = (1-√5)/2.

This explains WHY the 5-digit bound works: φ⁵ ≈ 11.09 > 10.

## Status
- [x] Part I: Five-step identity, growth bound, generalized Lamé bound
- [x] Part II: Binet's formula, golden ratio properties, φ⁵ > 10
- [x] Nearest integer property: fib(n) is the closest integer to φⁿ/√5
- Axiom count: 0
- Sorry count: 0
-/

namespace GCDAlgorithmOQ01OQ03

open Nat GCDAlgorithmOQ01

/-! ## The Five-Step Fibonacci Identity -/

/-- The five-step Fibonacci identity: fib(n+5) = 5·fib(n+1) + 3·fib(n).
    Derived from four instances of fib(n+2) = fib(n) + fib(n+1). -/
theorem fib_add_five (n : ℕ) : fib (n + 5) = 5 * fib (n + 1) + 3 * fib n := by
  have h2 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
  have h3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := by
    exact fib_add_two
  have h4 : fib (n + 4) = fib (n + 2) + fib (n + 3) := by
    exact fib_add_two
  have h5 : fib (n + 5) = fib (n + 3) + fib (n + 4) := by
    exact fib_add_two
  omega

/-! ## The Multiplicative Growth Step -/

/-- The multiplicative growth: fib(5k+7) ≥ 10·fib(5k+2).
    Uses: fib(5k+7) = 8·fib(5k+2) + 5·fib(5k+1), and
    5·fib(5k+1) ≥ 2·fib(5k+2) since 3·fib(5k+1) ≥ 2·fib(5k). -/
theorem fib_five_step_growth (k : ℕ) : 10 * fib (5 * k + 2) ≤ fib (5 * k + 7) := by
  -- Unfold fib(5k+7) down to fib(5k) and fib(5k+1)
  have h1 : fib (5 * k + 2) = fib (5 * k) + fib (5 * k + 1) := fib_add_two
  have h2 : fib (5 * k + 3) = fib (5 * k + 1) + fib (5 * k + 2) := by
    exact fib_add_two
  have h3 : fib (5 * k + 4) = fib (5 * k + 2) + fib (5 * k + 3) := by
    exact fib_add_two
  have h4 : fib (5 * k + 5) = fib (5 * k + 3) + fib (5 * k + 4) := by
    exact fib_add_two
  have h5 : fib (5 * k + 6) = fib (5 * k + 4) + fib (5 * k + 5) := by
    exact fib_add_two
  have h6 : fib (5 * k + 7) = fib (5 * k + 5) + fib (5 * k + 6) := by
    exact fib_add_two
  -- Monotonicity: fib(5k) ≤ fib(5k+1)
  have hmono : fib (5 * k) ≤ fib (5 * k + 1) := Nat.fib_mono (by omega)
  omega

/-! ## Main Bound: fib(5k+2) ≥ 10^k for All k -/

/-- **fib(5k+2) ≥ 10^k for all k** (no restriction).
    Proved by induction using the multiplicative growth step. -/
theorem fib_ge_pow10_general (k : ℕ) : 10 ^ k ≤ fib (5 * k + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hgrowth := fib_five_step_growth k
    have hindex : 5 * k + 7 = 5 * (k + 1) + 2 := by omega
    calc 10 ^ (k + 1) = 10 * 10 ^ k := by ring
      _ ≤ 10 * fib (5 * k + 2) := Nat.mul_le_mul_left 10 ih
      _ ≤ fib (5 * k + 7) := hgrowth
      _ = fib (5 * (k + 1) + 2) := by rw [hindex]

/-! ## Generalized Lamé 5-Digit Bound -/

/-- **Lamé's 5-Digit Bound (unrestricted)**: For any b > 0,
    euclideanSteps a b ≤ 5 × decimalDigits(b).

    This generalizes the original bound from b < 10^20 to all b. -/
theorem lame_five_digit_bound_general (a b : ℕ) (hb : 0 < b) :
    euclideanSteps a b ≤ 5 * decimalDigits b := by
  unfold decimalDigits
  set d := Nat.log 10 b
  apply lame_step_bound a b hb
  have hb_lt : b < 10 ^ (d + 1) := Nat.lt_pow_succ_log_self (by omega : 1 < 10) b
  have hfib : 10 ^ (d + 1) ≤ fib (5 * (d + 1) + 2) := fib_ge_pow10_general (d + 1)
  omega

-- Verify
example : euclideanSteps 48 18 ≤ 5 * decimalDigits 18 := by native_decide
example : euclideanSteps 1000 373 ≤ 5 * decimalDigits 373 := by native_decide

/-! ## Part II: Binet's Formula (Golden Ratio Connection)

This section proves the golden ratio Fibonacci identity and derives consequences.
While Part I gives a self-contained arithmetic proof, Part II explains the
deeper structure: the golden ratio governs Fibonacci growth, and φ⁵ > 10
is the reason 5 decimal digits correspond to one Euclidean step. -/

end GCDAlgorithmOQ01OQ03

namespace GCDAlgorithmOQ01OQ03.Binet

open GCDAlgorithmOQ01

/-- The golden ratio: φ = (1 + √5)/2 ≈ 1.618... -/
noncomputable def goldenPhi : ℝ := (1 + Real.sqrt 5) / 2

/-- The golden ratio conjugate: ψ = (1 - √5)/2 ≈ -0.618... -/
noncomputable def goldenPsi : ℝ := (1 - Real.sqrt 5) / 2

/-! ### Algebraic Properties of √5, φ, and ψ -/

theorem sqrt5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos_of_pos (by norm_num)

theorem sqrt5_ne_zero : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos

theorem sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 :=
  Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)

theorem sqrt5_gt_two : Real.sqrt 5 > 2 := by
  have h := sqrt5_sq
  nlinarith [sqrt5_pos]

/-- φ - ψ = √5 (the fundamental gap). -/
theorem phi_sub_psi : goldenPhi - goldenPsi = Real.sqrt 5 := by
  unfold goldenPhi goldenPsi; ring

/-- φ + ψ = 1 (Vieta's formula for x² - x - 1 = 0). -/
theorem phi_add_psi : goldenPhi + goldenPsi = 1 := by
  unfold goldenPhi goldenPsi; ring

/-- φ · ψ = -1 (Vieta's formula for x² - x - 1 = 0). -/
theorem phi_mul_psi : goldenPhi * goldenPsi = -1 := by
  unfold goldenPhi goldenPsi
  ring_nf
  rw [Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
  ring

/-- φ² = φ + 1 (defining property of the golden ratio). -/
theorem phi_sq : goldenPhi ^ 2 = goldenPhi + 1 := by
  unfold goldenPhi
  ring_nf
  rw [Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
  ring

/-- ψ² = ψ + 1 (conjugate satisfies the same quadratic). -/
theorem psi_sq : goldenPsi ^ 2 = goldenPsi + 1 := by
  unfold goldenPsi
  ring_nf
  rw [Real.sq_sqrt (show (5 : ℝ) ≥ 0 by norm_num)]
  ring

/-- φ > 0 (the golden ratio is positive). -/
theorem phi_pos : goldenPhi > 0 := by
  unfold goldenPhi
  linarith [sqrt5_pos]

/-! ### Binet's Formula -/

/-- **Binet's formula**: fib(n) = (φⁿ - ψⁿ) / √5.

This is one of the most elegant identities in number theory. It connects
the discrete Fibonacci recurrence to continuous exponential growth via
the golden ratio. The proof uses paired induction with φ² = φ + 1
and ψ² = ψ + 1. -/
private theorem binet_pair (n : ℕ) :
    (Nat.fib n : ℝ) = (goldenPhi ^ n - goldenPsi ^ n) / Real.sqrt 5 ∧
    (Nat.fib (n + 1) : ℝ) = (goldenPhi ^ (n + 1) - goldenPsi ^ (n + 1)) / Real.sqrt 5 := by
  induction n with
  | zero =>
    constructor
    · -- fib(0) = 0 = (1 - 1)/√5
      rw [pow_zero, pow_zero, sub_self, zero_div]; norm_cast
    · -- fib(1) = 1 = (φ - ψ)/√5 = √5/√5
      show (Nat.fib 1 : ℝ) = (goldenPhi ^ 1 - goldenPsi ^ 1) / Real.sqrt 5
      rw [Nat.fib_one, Nat.cast_one, pow_one, pow_one, phi_sub_psi, div_self sqrt5_ne_zero]
  | succ n ih =>
    obtain ⟨ih_n, ih_n1⟩ := ih
    constructor
    · exact ih_n1
    · -- fib(n+2) = fib(n) + fib(n+1), then use IH
      have hfib : (Nat.fib (n + 2) : ℝ) = (Nat.fib n : ℝ) + (Nat.fib (n + 1) : ℝ) := by
        exact_mod_cast Nat.fib_add_two
      rw [show n + 1 + 1 = n + 2 from rfl, hfib, ih_n, ih_n1, ← add_div]
      congr 1
      -- φ^(n+2) - ψ^(n+2) = (φ^n - ψ^n) + (φ^(n+1) - ψ^(n+1))
      have e1 : goldenPhi ^ (n + 2) = goldenPhi ^ n * goldenPhi ^ 2 := by ring
      have e2 : goldenPsi ^ (n + 2) = goldenPsi ^ n * goldenPsi ^ 2 := by ring
      rw [e1, e2, phi_sq, psi_sq]
      ring

theorem binet_formula (n : ℕ) :
    (Nat.fib n : ℝ) = (goldenPhi ^ n - goldenPsi ^ n) / Real.sqrt 5 :=
  (binet_pair n).1

/-! ### Consequences of Binet's Formula -/

/-- |ψ| < 1, so ψⁿ → 0 as n → ∞. -/
theorem abs_psi_lt_one : |goldenPsi| < 1 := by
  have h1 : Real.sqrt 5 > 1 := by linarith [sqrt5_gt_two]
  have hneg : goldenPsi < 0 := by unfold goldenPsi; linarith
  have hgt : goldenPsi > -1 := by
    unfold goldenPsi
    have : Real.sqrt 5 < 3 := by nlinarith [sqrt5_sq, sqrt5_pos]
    linarith
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩

/-- fib(n) is within 1/2 of φⁿ/√5 (nearest integer property). -/
theorem fib_nearest_integer (n : ℕ) :
    |(Nat.fib n : ℝ) - goldenPhi ^ n / Real.sqrt 5| < 1 / 2 := by
  rw [binet_formula]
  have hsimpl : (goldenPhi ^ n - goldenPsi ^ n) / Real.sqrt 5 - goldenPhi ^ n / Real.sqrt 5 =
      -(goldenPsi ^ n) / Real.sqrt 5 := by ring
  rw [hsimpl, neg_div, abs_neg, abs_div, abs_of_pos sqrt5_pos, abs_pow]
  -- Goal: |goldenPsi| ^ n / Real.sqrt 5 < 1 / 2
  have h1 : |goldenPsi| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) (le_of_lt abs_psi_lt_one)
  have h2 := sqrt5_gt_two
  have h3ne : Real.sqrt 5 ≠ 0 := ne_of_gt sqrt5_pos
  -- Clear all denominators, then solve by nlinarith
  field_simp [h3ne]
  nlinarith

/-! ### Why 5 Digits Per Step: φ⁵ > 10 -/

/-- Powers of the golden ratio reduced via φ² = φ + 1. -/
theorem phi_pow3 : goldenPhi ^ 3 = 2 * goldenPhi + 1 := by
  calc goldenPhi ^ 3 = goldenPhi ^ 2 * goldenPhi := by ring
    _ = (goldenPhi + 1) * goldenPhi := by rw [phi_sq]
    _ = goldenPhi ^ 2 + goldenPhi := by ring
    _ = (goldenPhi + 1) + goldenPhi := by rw [phi_sq]
    _ = 2 * goldenPhi + 1 := by ring

theorem phi_pow4 : goldenPhi ^ 4 = 3 * goldenPhi + 2 := by
  calc goldenPhi ^ 4 = goldenPhi ^ 3 * goldenPhi := by ring
    _ = (2 * goldenPhi + 1) * goldenPhi := by rw [phi_pow3]
    _ = 2 * goldenPhi ^ 2 + goldenPhi := by ring
    _ = 2 * (goldenPhi + 1) + goldenPhi := by rw [phi_sq]
    _ = 3 * goldenPhi + 2 := by ring

theorem phi_pow5 : goldenPhi ^ 5 = 5 * goldenPhi + 3 := by
  calc goldenPhi ^ 5 = goldenPhi ^ 4 * goldenPhi := by ring
    _ = (3 * goldenPhi + 2) * goldenPhi := by rw [phi_pow4]
    _ = 3 * goldenPhi ^ 2 + 2 * goldenPhi := by ring
    _ = 3 * (goldenPhi + 1) + 2 * goldenPhi := by rw [phi_sq]
    _ = 5 * goldenPhi + 3 := by ring

/-- **φ⁵ > 10**: The golden ratio explanation for Lamé's 5-digit bound.
    Since fib(n) ≈ φⁿ/√5 and φ⁵ > 10, each group of 5 Fibonacci indices
    multiplies the value by more than 10, consuming one decimal digit. -/
theorem phi_pow5_gt_10 : goldenPhi ^ 5 > 10 := by
  rw [phi_pow5]
  have : goldenPhi > 7 / 5 := by
    unfold goldenPhi
    have hsq := sqrt5_sq
    have hpos := sqrt5_pos
    have : Real.sqrt 5 > 9 / 5 := by nlinarith
    linarith
  linarith

/-! ### Verification Examples -/

example : (Nat.fib 0 : ℝ) = (goldenPhi ^ 0 - goldenPsi ^ 0) / Real.sqrt 5 :=
  binet_formula 0
example : (Nat.fib 1 : ℝ) = (goldenPhi ^ 1 - goldenPsi ^ 1) / Real.sqrt 5 :=
  binet_formula 1
example : (Nat.fib 10 : ℝ) = (goldenPhi ^ 10 - goldenPsi ^ 10) / Real.sqrt 5 :=
  binet_formula 10

end GCDAlgorithmOQ01OQ03.Binet

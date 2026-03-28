/-
  Aristotle targets for Erdős Problem #964
  Routine supporting lemmas for automated proof search.
  See Erdos964Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT Eberhard's theorem or the main density conjecture
  - Known results likely in Mathlib (divisor function properties)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos964Aristotle

open Nat Finset

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Divisor Function Properties
-- ═══════════════════════════════════════════════════════════════════

/-- τ(n) = number of positive divisors of n. -/
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/-- τ(1) = 1. -/
theorem tau_one : tau 1 = 1 := by
  simp [tau, Nat.divisors]

/-- τ(p) = 2 for prime p. -/
theorem tau_prime (p : ℕ) (hp : Nat.Prime p) : tau p = 2 := by
  simp [tau, Nat.divisors_prime hp]

/-- τ(p^k) = k + 1 for prime p. -/
theorem tau_prime_power (p k : ℕ) (hp : Nat.Prime p) :
    tau (p ^ k) = k + 1 := by
  simp [tau, Nat.divisors_prime_pow hp]

/-- τ is multiplicative on coprime arguments. -/
theorem tau_multiplicative (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (h : Nat.Coprime m n) :
    tau (m * n) = tau m * tau n := by
  simp [tau, Nat.Coprime.divisors_mul h]

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Small Computations
-- ═══════════════════════════════════════════════════════════════════

/-- τ(2) = 2. -/
theorem tau_two : tau 2 = 2 := tau_prime 2 Nat.prime_two

/-- τ(3) = 2. -/
theorem tau_three : tau 3 = 2 := tau_prime 3 Nat.prime_three

/-- τ(4) = 3. -/
theorem tau_four : tau 4 = 3 := by native_decide

/-- τ(6) = 4. -/
theorem tau_six : tau 6 = 4 := by native_decide

/-- τ(12) = 6. -/
theorem tau_twelve : tau 12 = 6 := by native_decide

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Density of Rationals
-- ═══════════════════════════════════════════════════════════════════

/-- Rationals are dense in the positive reals. -/
theorem rationals_dense_in_positives :
    ∀ r : ℝ, r > 0 → ∀ ε : ℝ, ε > 0 →
    ∃ p q : ℕ, p ≥ 1 ∧ q ≥ 1 ∧ |((p : ℝ) / q) - r| < ε := by
  intro r hr ε hε
  -- Find q with 1/q < ε via Archimedean property
  obtain ⟨q, hq⟩ := exists_nat_gt (1 / ε)
  have hq_cast : (1 : ℝ) / ε < (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := lt_trans (div_pos one_pos hε) hq_cast
  have hq_ge1 : q ≥ 1 := by omega
  have h1q_lt_ε : (1 : ℝ) / q < ε := by
    rw [div_lt_iff hq_pos]; linarith [mul_comm ε ((q : ℝ)), (div_lt_iff hε).mp hq_cast]
  -- Find p = ⌈r * q⌉₊
  set p := ⌈r * (q : ℝ)⌉₊
  have hrq_pos : r * (q : ℝ) > 0 := mul_pos hr hq_pos
  have hp_pos : 0 < p := Nat.ceil_pos.mpr hrq_pos
  have hp_ge : (p : ℝ) ≥ r * q := Nat.le_ceil _
  have hpq_ge_r : (p : ℝ) / q ≥ r := (le_div_iff hq_pos).mpr (by linarith)
  refine ⟨p, q, by omega, hq_ge1, ?_⟩
  rw [abs_of_nonneg (by linarith)]
  have hp_lt : (p : ℝ) < r * q + 1 := Nat.ceil_lt_add_one (le_of_lt hrq_pos)
  calc (p : ℝ) / q - r = ((p : ℝ) - r * q) / q := by field_simp
    _ < 1 / q := (div_lt_div_right hq_pos).mpr (by linarith)
    _ < ε := h1q_lt_ε

end Erdos964Aristotle

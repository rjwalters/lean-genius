/-
  binomial-theorem-oq-01-oq-01-oq-03:
  "The closed form C(-1/2, k) = (-1)^k · C(2k,k) / 4^k, connecting the
   generalized (Newton) binomial coefficient at α = -1/2 to the central
   binomial coefficients and the Catalan numbers."
  ====================================================

  Verified: all theorems compile against Mathlib (lean v4.26.0) and depend only
  on the foundational axioms `propext`, `Classical.choice`, `Quot.sound`
  (0 sorries, 0 `axiom` declarations, no `native_decide`).

  The parent gallery proof `binomial-theorem-oq-01-oq-01`
  (proofs/Proofs/BinomialTheoremOQ01OQ01.lean) provides:
    * `genBinom α k = (∏ j ∈ range k, (α - j)) / k!`   — the coefficient C(α,k)
    * `ode_recurrence α k : (k+1) · C(α,k+1) = (α-k) · C(α,k)`
    * concrete values of the POSITIVE half-integer coefficients C(1/2,k) at
      small k (k ≤ 3), with the observation that they are eventually nonzero.

  That parent stops at ad-hoc small-k evaluation.  This OQ delivers the general
  UNIFORM closed form for the NEGATIVE half-integer coefficient — the one that
  actually appears in analysis, as the Taylor coefficients of (1+x)^(-1/2) =
  1/√(1+x):

        C(-1/2, k) = (-1)^k · C(2k, k) / 4^k
                   = (-1)^k · centralBinom k / 4^k
                   = (-1)^k · (k+1) · catalan k / 4^k.

  These are the coefficients underlying the generating function of the central
  binomial coefficients, √(1-4x) = 1 - 2 ∑_{k≥1} catalan(k-1) x^k, and the fact
  that ∑ centralBinom k · x^k = 1/√(1-4x).

  Proof strategy: a single induction on k using the parent's `ode_recurrence`
  together with Mathlib's central-binomial recurrence
    `Nat.succ_mul_centralBinom_succ n :
        (n+1) · centralBinom (n+1) = 2·(2n+1) · centralBinom n`.
  The two recurrences have matching ratios:
    C(-1/2, n+1)/C(-1/2, n) = (-1/2 - n)/(n+1) = -(2n+1)/(2(n+1)),
    [(-1)^{n+1} cb_{n+1}/4^{n+1}] / [(-1)^n cb_n/4^n]
        = -cb_{n+1}/(4 cb_n) = -(2n+1)/(2(n+1)),
  so a `linear_combination` of the two recurrences plus the inductive hypothesis
  closes the step exactly.
-/
import Mathlib
import Proofs.BinomialTheoremOQ01OQ01

open Finset Nat

namespace BinomialTheoremOQ01OQ01OQ03

open BinomialTheoremOQ01OQ01

/-! ### The central-binomial recurrence, cast to `ℝ` -/

/-- Mathlib's `Nat.succ_mul_centralBinom_succ`, transported to `ℝ`:
    `(n+1) · centralBinom (n+1) = 2·(2n+1) · centralBinom n`. -/
theorem centralBinom_rec_real (n : ℕ) :
    ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_centralBinom_succ n)
  push_cast at h
  linarith

/-! ### Multiplied-through closed form (division-free) -/

/-- The division-free form of the closed formula:
    `C(-1/2, k) · 4^k = (-1)^k · centralBinom k`.
    Proved by induction on `k`, cancelling the factor `(k+1)` and closing the
    inductive step with a `linear_combination` of the two recurrences. -/
theorem genBinom_negHalf_mul_pow (k : ℕ) :
    genBinom (-1/2 : ℝ) k * 4 ^ k = (-1) ^ k * (Nat.centralBinom k : ℝ) := by
  induction k with
  | zero => simp [genBinom_zero, Nat.centralBinom_zero]
  | succ n ih =>
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hrec := ode_recurrence (-1/2 : ℝ) n
    have hcb := centralBinom_rec_real n
    -- Cancel the common factor (n+1) on both sides, then close by
    -- linear_combination of ode_recurrence, ih, and the central recurrence.
    apply mul_left_cancel₀ hn1
    linear_combination (4 * 4 ^ n) * hrec + (4 * (-1/2 - (n : ℝ))) * ih
      + ((-1 : ℝ) ^ n) * hcb

/-! ### Main closed forms -/

/-- **Main result.** `C(-1/2, k) = (-1)^k · centralBinom k / 4^k`. -/
theorem genBinom_negHalf (k : ℕ) :
    genBinom (-1/2 : ℝ) k = (-1) ^ k * (Nat.centralBinom k : ℝ) / 4 ^ k := by
  rw [eq_div_iff (by positivity : (4 : ℝ) ^ k ≠ 0)]
  exact genBinom_negHalf_mul_pow k

/-- The same, written with the explicit central binomial coefficient
    `C(2k, k)`: `C(-1/2, k) = (-1)^k · C(2k,k) / 4^k`. -/
theorem genBinom_negHalf_choose (k : ℕ) :
    genBinom (-1/2 : ℝ) k = (-1) ^ k * ((2 * k).choose k : ℝ) / 4 ^ k := by
  rw [genBinom_negHalf, Nat.centralBinom_eq_two_mul_choose]

/-- Catalan form: `C(-1/2, k) = (-1)^k · (k+1) · catalan k / 4^k`, using the
    identity `(k+1)·catalan k = centralBinom k`. -/
theorem genBinom_negHalf_catalan (k : ℕ) :
    genBinom (-1/2 : ℝ) k
      = (-1) ^ k * (((k : ℝ) + 1) * (catalan k : ℝ)) / 4 ^ k := by
  rw [genBinom_negHalf]
  have h : ((Nat.centralBinom k : ℝ)) = ((k : ℝ) + 1) * (catalan k : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) (succ_mul_catalan_eq_centralBinom k)
    push_cast at this
    linarith
  rw [h]

/-! ### Sign and nonvanishing -/

/-- The negative half-integer coefficient is strictly alternating in sign:
    it never vanishes.  (Contrast the positive case `C(1/2,k)`, whose parent
    proof establishes nonvanishing only for small `k`.) -/
theorem genBinom_negHalf_ne_zero (k : ℕ) : genBinom (-1/2 : ℝ) k ≠ 0 := by
  rw [genBinom_negHalf]
  have hcb : (Nat.centralBinom k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos k).ne'
  have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
  have hsign : ((-1 : ℝ) ^ k) ≠ 0 := pow_ne_zero k (by norm_num)
  exact div_ne_zero (mul_ne_zero hsign hcb) h4

/-- The absolute value of the coefficient is `centralBinom k / 4^k`, a positive
    rational strictly decreasing to `0` — the Wallis-type decay of the Taylor
    coefficients of `1/√(1+x)`. -/
theorem abs_genBinom_negHalf (k : ℕ) :
    |genBinom (-1/2 : ℝ) k| = (Nat.centralBinom k : ℝ) / 4 ^ k := by
  rw [genBinom_negHalf, abs_div, abs_mul]
  have h4 : |(4 : ℝ) ^ k| = 4 ^ k := abs_of_pos (by positivity)
  have hcb : |(Nat.centralBinom k : ℝ)| = (Nat.centralBinom k : ℝ) := Nat.abs_cast _
  have hsign : |(-1 : ℝ) ^ k| = 1 := by
    rw [abs_pow]; simp
  rw [h4, hcb, hsign, one_mul]

/-! ### Concrete values (sanity checks against the parent's small-`k` data) -/

/-- `C(-1/2, 0) = 1`. -/
theorem genBinom_negHalf_zero : genBinom (-1/2 : ℝ) 0 = 1 := by
  rw [genBinom_negHalf]; norm_num [Nat.centralBinom]

/-- `C(-1/2, 1) = -1/2`. -/
theorem genBinom_negHalf_one : genBinom (-1/2 : ℝ) 1 = -1/2 := by
  rw [genBinom_negHalf]; norm_num [Nat.centralBinom, Nat.choose]

/-- `C(-1/2, 2) = 3/8`. -/
theorem genBinom_negHalf_two : genBinom (-1/2 : ℝ) 2 = 3/8 := by
  rw [genBinom_negHalf]; norm_num [Nat.centralBinom, Nat.choose]

/-- `C(-1/2, 3) = -5/16`. -/
theorem genBinom_negHalf_three : genBinom (-1/2 : ℝ) 3 = -5/16 := by
  rw [genBinom_negHalf]; norm_num [Nat.centralBinom, Nat.choose]

end BinomialTheoremOQ01OQ01OQ03

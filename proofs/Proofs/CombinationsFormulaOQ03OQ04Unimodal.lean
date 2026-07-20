import Proofs.CombinationsFormulaOQ03
import Proofs.CombinationsFormulaOQ03OQ04
import Mathlib

/-
# Coefficient Unimodality of Gaussian q-Binomials — base cases k ≤ 1

## What This Proves
Sylvester's theorem (1878) says the coefficient sequence of the Gaussian binomial
`[n,k]_q ∈ ℤ[q]` is symmetric **and unimodal** (rises weakly to a single peak, then
falls). The companion file `CombinationsFormulaOQ03OQ04` established the *symmetric*
half (palindromy, degree, monicity, nonnegativity, pinned extreme coefficients). The
*unimodal* half is the substantive open content and in general needs sl₂-representation
theory / hard Lefschetz (Proctor 1982) or O'Hara's combinatorial decomposition (1990).

This file provides the missing **unimodality API** Mathlib lacks (there is no
`Unimodal` predicate for integer sequences), together with the first genuine
milestones on the target theorem: unimodality of the coefficient sequence for the
base cases `k = 0` and `k = 1`.

* `IsCoeffUnimodal p` — the coefficient sequence of `p : ℤ[X]` has a peak index below
  which coefficients weakly increase and above which they weakly decrease.
* `isCoeffUnimodal_of_antitone` — a globally non-increasing coefficient sequence is
  unimodal (peak at `0`). The reusable reduction that both base cases use.
* `qNumber_X_coeff` — the coefficient array of `qNumber X n = 1 + X + ⋯ + X^{n-1}` is
  `[j < n]` (all-ones then all-zeros).
* `qBinom_X_coeff_one` — hence the coefficients of `[n,1]_q` are `[j < n]`.
* `qBinom_X_unimodal_zero`, `qBinom_X_unimodal_one` — the coefficient sequences of
  `[n,0]_q = 1` and `[n,1]_q = 1 + X + ⋯ + X^{n-1}` are unimodal.

## Honesty Note
`k ≤ 1` is exactly the *easy* regime: both sequences are flat/monotone, so unimodality
reduces to `isCoeffUnimodal_of_antitone`. The mathematically hard cases `k ≥ 2` — where
the sequence genuinely rises and then falls (e.g. `[4,2]_q = 1,1,2,1,1`,
`[6,2]_q = 1,1,2,2,3,2,2,1,1`) — are **not** proved here and remain the open crux. This
contribution is the unimodality *predicate* + reduction lemmas + the two base cases,
which pin down the target statement and exercise the coefficient-extraction layer.
-/

open Polynomial

namespace QBinomialCoefficients.Unimodal

open QBinomialCoefficients

/-- **Coefficient-sequence unimodality of an integer polynomial.**  `p : ℤ[X]` is
    *coefficient-unimodal* if there is a peak index `m` such that its coefficients
    weakly increase up to `m` and weakly decrease from `m` on:

    `p.coeff 0 ≤ ⋯ ≤ p.coeff m ≥ ⋯ ≥ p.coeff j ≥ ⋯`.

    This is the integer-sequence `Unimodal` predicate Mathlib lacks, specialised to a
    polynomial's coefficient array — the object of Sylvester's symmetric-unimodal
    theorem for `[n,k]_q`. -/
def IsCoeffUnimodal (p : ℤ[X]) : Prop :=
  ∃ m : ℕ,
    (∀ i j : ℕ, i ≤ j → j ≤ m → p.coeff i ≤ p.coeff j) ∧
    (∀ i j : ℕ, m ≤ i → i ≤ j → p.coeff j ≤ p.coeff i)

/-- **A globally non-increasing coefficient sequence is unimodal**, with peak at `0`.
    The rising half is vacuous (only `i = j = 0` satisfies `i ≤ j ≤ 0`) and the falling
    half is the hypothesis.  This is the reduction both base cases `k = 0, 1` use, since
    those coefficient sequences are flat-then-zero. -/
theorem isCoeffUnimodal_of_antitone (p : ℤ[X])
    (h : ∀ i j : ℕ, i ≤ j → p.coeff j ≤ p.coeff i) : IsCoeffUnimodal p := by
  refine ⟨0, ?_, ?_⟩
  · intro i j hij hj0
    have hi0 : i = 0 := Nat.le_zero.1 (le_trans hij hj0)
    have hj0' : j = 0 := Nat.le_zero.1 hj0
    subst hi0; subst hj0'; exact le_refl _
  · intro i j _ hij
    exact h i j hij

/-- **Coefficients of `qNumber X n`.**  The `q`-analogue of `n`,
    `qNumber X n = 1 + X + ⋯ + X^{n-1}`, has coefficient `1` at every index `j < n` and
    `0` otherwise.  Induction on `n` via `qNumber X (n+1) = 1 + X · qNumber X n`. -/
theorem qNumber_X_coeff :
    ∀ (n j : ℕ), (qNumber (X : ℤ[X]) n).coeff j = if j < n then 1 else 0
  | 0, j => by simp [qNumber]
  | n + 1, j => by
      rw [qNumber_succ]
      cases j with
      | zero =>
          simp [coeff_one]
      | succ m =>
          rw [coeff_add, coeff_one]
          simp only [Nat.succ_ne_zero, if_false, zero_add, coeff_X_mul]
          rw [qNumber_X_coeff n m]
          by_cases hmn : m < n
          · simp [hmn, Nat.succ_lt_succ hmn]
          · have : ¬ (m + 1 < n + 1) := by omega
            simp [hmn, this]

/-- **Coefficients of `[n,1]_q`.**  Since `[n,1]_q = qNumber X n`, its coefficient array
    is `[j < n]`: `1` for `j < n`, `0` otherwise. -/
theorem qBinom_X_coeff_one (n j : ℕ) :
    (qBinom (X : ℤ[X]) n 1).coeff j = if j < n then 1 else 0 := by
  rw [qBinom_one_right, qNumber_X_coeff]

/-- **Base case `k = 0`.**  `[n,0]_q = 1`, whose coefficient sequence `1, 0, 0, …` is
    (trivially) unimodal. -/
theorem qBinom_X_unimodal_zero (n : ℕ) :
    IsCoeffUnimodal (qBinom (X : ℤ[X]) n 0) := by
  apply isCoeffUnimodal_of_antitone
  intro i j hij
  -- `(1 : ℤ[X]).coeff t = if t = 0 then 1 else 0`; antitone since `i ≤ j`.
  simp only [qBinom_zero_right, coeff_one]
  split_ifs <;> omega

/-- **Base case `k = 1`.**  `[n,1]_q = 1 + X + ⋯ + X^{n-1}`, whose coefficient sequence
    `1,…,1,0,0,…` is non-increasing, hence unimodal.  Uses the coefficient formula
    `qBinom_X_coeff_one` and the antitone reduction. -/
theorem qBinom_X_unimodal_one (n : ℕ) :
    IsCoeffUnimodal (qBinom (X : ℤ[X]) n 1) := by
  apply isCoeffUnimodal_of_antitone
  intro i j hij
  simp only [qBinom_X_coeff_one]
  split_ifs <;> omega

end QBinomialCoefficients.Unimodal

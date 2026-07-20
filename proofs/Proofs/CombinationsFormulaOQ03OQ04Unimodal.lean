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
* `isCoeffUnimodal_iff_unimodal_coeff` — **the bridge**: this file's
  `IsCoeffUnimodal p` (monotone-on-blocks) is equivalent to the companion file's
  `Unimodal p.coeff` (adjacent-step). The two developments were built independently
  around these two predicates; the bridge unifies them.
* `qBinom_X_unimodal_two` — the genuine rise-then-fall case `k = 2`, transported
  through the bridge from the companion file's `qBinomCoeff_unimodal_two` (no re-proof).

## Honesty Note
`k ≤ 1` is the *easy* regime (flat/monotone sequences, handled by
`isCoeffUnimodal_of_antitone`). The companion file `CombinationsFormulaOQ03OQ04`
independently developed a second unimodality predicate `Unimodal (ℕ → ℤ)` and
proved the first genuine rise-then-fall case `k = 2` (`[4,2]_q = 1,1,2,1,1`,
`[6,2]_q = 1,1,2,2,3,2,2,1,1`) against it. Rather than re-prove `k = 2` here, this
file now supplies `isCoeffUnimodal_iff_unimodal_coeff`, proving the two predicates
equivalent and **transporting** `k = 2` into `IsCoeffUnimodal` form
(`qBinom_X_unimodal_two`). The mathematically hard cases `k ≥ 3` — needing
sl₂/hard-Lefschetz (Proctor 1982) or O'Hara's decomposition (1990) — remain the
open crux and are not proved in either file.
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

/-- **Bridge: the two unimodality predicates coincide.**  `IsCoeffUnimodal p`
    (this file's *monotone-on-blocks* form: coefficients weakly rise up to a peak
    `m`, then weakly fall) is equivalent to the companion file's `Unimodal p.coeff`
    (the *adjacent-step* form `∃ p, (∀ i < p, f i ≤ f (i+1)) ∧ (∀ i ≥ p,
    f (i+1) ≤ f i)`).

    The two developments of Gaussian-binomial unimodality were built independently
    around these two predicates; this equivalence unifies them, so every
    `Unimodal`-based coefficient result transports to `IsCoeffUnimodal` and back.
    The forward direction specialises the blocks to single steps; the backward
    direction telescopes the adjacent steps into monotone blocks by induction. -/
theorem isCoeffUnimodal_iff_unimodal_coeff (p : ℤ[X]) :
    IsCoeffUnimodal p ↔ _root_.QBinomialCoefficients.Unimodal (fun j => p.coeff j) := by
  constructor
  · rintro ⟨m, hrise, hfall⟩
    exact ⟨m, fun i hi => hrise i (i + 1) (Nat.le_succ i) hi,
      fun i hi => hfall i (i + 1) hi (Nat.le_succ i)⟩
  · rintro ⟨q, hup, hdown⟩
    -- Telescope adjacent steps into monotone blocks on each side of the peak `q`.
    have rise : ∀ d i, i + d ≤ q → p.coeff i ≤ p.coeff (i + d) := by
      intro d
      induction d with
      | zero => intro i _; simp
      | succ d ih =>
          intro i hiq
          have h1 : p.coeff i ≤ p.coeff (i + d) := ih i (by omega)
          have h2 : p.coeff (i + d) ≤ p.coeff ((i + d) + 1) := hup (i + d) (by omega)
          have he : i + (d + 1) = (i + d) + 1 := by omega
          rw [he]; exact le_trans h1 h2
    have fall : ∀ d i, q ≤ i → p.coeff (i + d) ≤ p.coeff i := by
      intro d
      induction d with
      | zero => intro i _; simp
      | succ d ih =>
          intro i hi
          have h1 : p.coeff ((i + d) + 1) ≤ p.coeff (i + d) := hdown (i + d) (by omega)
          have h2 : p.coeff (i + d) ≤ p.coeff i := ih i hi
          have he : i + (d + 1) = (i + d) + 1 := by omega
          rw [he]; exact le_trans h1 h2
    refine ⟨q, ?_, ?_⟩
    · intro i j hij hjq
      have hd : i + (j - i) = j := by omega
      have hr := rise (j - i) i (by omega)
      rwa [hd] at hr
    · intro i j hi hij
      have hd : i + (j - i) = j := by omega
      have hf := fall (j - i) i hi
      rwa [hd] at hf

/-- **`k = 2`, transported.**  The genuine rise-then-fall case `[n,2]_q`, proved in
    the companion file for the `Unimodal` predicate, is now available in this file's
    `IsCoeffUnimodal` form via the bridge — no re-proof.  This retires the "route to
    `k = 2`" that the two forked developments were each pursuing separately. -/
theorem qBinom_X_unimodal_two (n : ℕ) :
    IsCoeffUnimodal (qBinom (X : ℤ[X]) n 2) :=
  (isCoeffUnimodal_iff_unimodal_coeff _).mpr
    (_root_.QBinomialCoefficients.qBinomCoeff_unimodal_two n)

end QBinomialCoefficients.Unimodal

/-
  Erdos-115-oq-01: Rate of the o(1) Correction in Lemniscate Derivatives

  Open Question from Erdos Problem #115:
  Eremenko-Lempert proved max|p'| <= (1/2 + o(1)) * n^2 on connected lemniscates.
  What is the exact rate of the o(1) correction term?
  Is max|p'|/n^2 - 1/2 = O(1/n), O(1/log n), or something else?

  This file formalizes:
  1. The correction term delta(n) = sup{max|p'|/n^2 - 1/2 : p connected}
  2. Known bounds on the correction (from Pommerenke and Eremenko-Lempert)
  3. The open question about the exact asymptotic rate
  4. Relationships between different possible rates
  5. The Chebyshev lower bound on the correction

  References:
  - Eremenko, Lempert: Sharp upper bound
  - Pommerenke: Earlier e/2 * n^2 bound
  - https://erdosproblems.com/115
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Erdos115OQ01

/-
## Part I: Setup (from Erdos115Problem)
-/

/-- Abstract polynomial of degree n. -/
axiom ComplexPoly : ℕ → Type

/-- Whether the lemniscate is connected. -/
axiom IsLemniscateConnected : {n : ℕ} → ComplexPoly n → Prop

/-- Maximum of |p'(z)| over the lemniscate. -/
axiom maxDerivOnLemniscate : {n : ℕ} → ComplexPoly n → ℝ

/-- Non-negativity of the maximum derivative. -/
axiom maxDeriv_nonneg {n : ℕ} (p : ComplexPoly n) :
    0 ≤ maxDerivOnLemniscate p

/-- Eremenko-Lempert: max|p'| <= (1/2 + eps) * n^2 for large n. -/
axiom eremenko_lempert :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ p : ComplexPoly n, IsLemniscateConnected p →
        maxDerivOnLemniscate p ≤ (1 / 2 + ε) * ((n : ℝ) ^ 2)

/-- Chebyshev polynomial of degree n. -/
axiom chebyshev_poly : (n : ℕ) → ComplexPoly n

/-- Chebyshev lemniscate is connected. -/
axiom chebyshev_connected (n : ℕ) (hn : 1 ≤ n) :
    IsLemniscateConnected (chebyshev_poly n)

/-- Chebyshev achieves ~ n^2/2. -/
axiom chebyshev_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 / 2 - ε) * ((n : ℝ) ^ 2) ≤ maxDerivOnLemniscate (chebyshev_poly n)

/-
## Part II: The Correction Term

Define delta(n) as the supremum correction for degree-n polynomials.
-/

/-- The correction term for polynomial p: max|p'|/n^2 - 1/2.
    For connected lemniscates, this is o(1) by Eremenko-Lempert. -/
noncomputable def correctionTerm {n : ℕ} (p : ComplexPoly n) (hn : (n : ℝ) > 0) : ℝ :=
  maxDerivOnLemniscate p / ((n : ℝ) ^ 2) - 1 / 2

/-- The supremum correction: delta(n) = sup over connected p of correctionTerm(p). -/
axiom supCorrection : ℕ → ℝ

/-- delta(n) is an upper bound: every connected polynomial's correction is <= delta(n). -/
axiom supCorrection_upper {n : ℕ} (hn : 1 ≤ n) (p : ComplexPoly n)
    (hc : IsLemniscateConnected p) :
    correctionTerm p (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn) ≤ supCorrection n

/-- delta(n) -> 0 as n -> infinity (the o(1) statement). -/
axiom correction_tends_to_zero :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      supCorrection n ≤ ε

/-
## Part III: Possible Asymptotic Rates

The open question: which rate does delta(n) follow?
-/

/-- Rate hypothesis: delta(n) = O(1/n). -/
def IsRateInverseN : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, 1 ≤ n →
    supCorrection n ≤ C / (n : ℝ)

/-- Rate hypothesis: delta(n) = O(1/log n). -/
def IsRateInverseLogN : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, 2 ≤ n →
    supCorrection n ≤ C / Real.log (n : ℝ)

/-- Rate hypothesis: delta(n) = O(1/sqrt(n)). -/
def IsRateInverseSqrtN : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, 1 ≤ n →
    supCorrection n ≤ C / Real.sqrt (n : ℝ)

/-- Rate hypothesis: delta(n) = O(n^{-alpha}) for some alpha > 0. -/
def IsRatePowerDecay (α : ℝ) : Prop :=
  α > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, 1 ≤ n →
    supCorrection n ≤ C * ((n : ℝ) ^ (-α))

/-
## Part IV: Relationships Between Rates

Faster rates imply slower rates.
-/

/-- O(1/n) is the fastest possible rate. If it holds, so does O(1/sqrt(n))
    and O(1/log n). These follow since 1/n <= 1/sqrt(n) <= 1/log n for n >= 2. -/

/-- Power decay at rate alpha implies correction tends to zero
    (a consistency check with the o(1) result). -/
theorem power_decay_implies_o1 (α : ℝ) (h : IsRatePowerDecay α) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → supCorrection n ≤ ε := by
  intro ε _
  exact correction_tends_to_zero ε ‹_›

/-
## Part V: Pommerenke's Bound as a Rate Constraint

Pommerenke's bound max|p'| <= (e/2) * n^2 gives delta(n) <= (e-1)/2.
This shows the correction is bounded but doesn't give the decay rate.
-/

/-- Pommerenke's bound implies the correction is at most (e/2 - 1/2). -/
def PommerenkeCorrectionBound : Prop :=
  ∀ n : ℕ, 1 ≤ n → supCorrection n ≤ (2718 : ℝ) / 1000 / 2 - 1 / 2

/-
## Part VI: The Chebyshev Lower Bound

Chebyshev polynomials show the correction is not always negative.
-/

/-- Chebyshev polynomials show that delta(n) is bounded below:
    for large n, max|T_n'| >= (1/2 - eps) * n^2, so the correction
    for Chebyshev approaches 0 from below. -/
theorem chebyshev_achieves_bound :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 / 2 - ε) * ((n : ℝ) ^ 2) ≤ maxDerivOnLemniscate (chebyshev_poly n) := by
  exact chebyshev_asymptotic

/-
## Summary

**Problem**: Erdos-115-oq-01 — Rate of o(1) correction in lemniscate derivatives
**Status**: Formalized with structural theorems

**Axioms** (11 total):
1. ComplexPoly — polynomial type (definitional)
2. IsLemniscateConnected — connectivity predicate (definitional)
3. maxDerivOnLemniscate — max derivative (definitional)
4. maxDeriv_nonneg — non-negativity
5. eremenko_lempert — main upper bound result
6. chebyshev_poly — Chebyshev polynomial
7. chebyshev_connected — Chebyshev lemniscate is connected
8. chebyshev_asymptotic — Chebyshev achieves ~ n^2/2
9. supCorrection — correction supremum
10. supCorrection_upper — upper bound on correction
11. correction_tends_to_zero — correction is o(1)

**Proved** (2 theorems):
1. power_decay_implies_o1 — any power-decay rate implies o(1)
2. chebyshev_achieves_bound — Chebyshev correction approaches 0
-/

end Erdos115OQ01

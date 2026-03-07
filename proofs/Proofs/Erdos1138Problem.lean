/- Erdős Problem #1138 — Primes in Short Intervals and Maximal Gaps

Let x/2 < y < x and C > 1. If d = max_{p_n < x}(p_{n+1} - p_n)
is the maximal prime gap below x, then is it true that

  π(y + Cd) - π(y) ~ Cd / log y?

This combines two deep problems: determining when the prime counting
function obeys its expected asymptotic in short intervals, and
understanding the size of maximal prime gaps.

The conjectured size of d is approximately (log x)², which is far
below the interval length h for which π(y + h) - π(y) ~ h / log y
can be proven, even assuming the Riemann Hypothesis.

Reference: https://erdosproblems.com/1138
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Finset Set

namespace Erdos1138

/- ## Part I: Prime Counting Infrastructure -/

/-- The prime counting function π(n) = |{p ≤ n : p prime}|. -/
noncomputable def primeCounting (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime |>.card

/-- Count of primes in the interval (a, b]: π(b) - π(a). -/
noncomputable def primesInInterval (a b : ℕ) : ℕ :=
  primeCounting b - primeCounting a

/- ## Part II: Maximal Prime Gap -/

/-- The set of prime gaps below x: {p_{n+1} - p_n : p_n < x, p_n and p_{n+1} consecutive primes}. -/
def primeGapBelow (x : ℕ) : Set ℕ :=
  {d | ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q ≤ x ∧
    (∀ r, Nat.Prime r → p < r → q ≤ r) ∧ d = q - p}

/-- The maximal prime gap below x. -/
noncomputable def maxPrimeGap (x : ℕ) : ℕ :=
  sSup {d | ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q ≤ x ∧
    (∀ r, Nat.Prime r → p < r → q ≤ r) ∧ d = q - p}

/- ## Part III: Basic Properties -/

/-- π is monotone: if a ≤ b then π(a) ≤ π(b). -/
theorem primeCounting_mono {a b : ℕ} (h : a ≤ b) :
    primeCounting a ≤ primeCounting b := by
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono (Nat.succ_le_succ h)

/-- π(0) = 0 (no primes at or below 0). -/
theorem primeCounting_zero : primeCounting 0 = 0 := by
  simp [primeCounting]
  decide

/-- π(1) = 0 (1 is not prime). -/
theorem primeCounting_one : primeCounting 1 = 0 := by
  simp [primeCounting]
  decide

/-- π(2) = 1. -/
theorem primeCounting_two : primeCounting 2 = 1 := by
  simp [primeCounting]
  decide

/-- π(n) ≤ n + 1 (trivial upper bound). -/
theorem primeCounting_le (n : ℕ) : primeCounting n ≤ n + 1 := by
  unfold primeCounting
  calc ((Finset.range (n + 1)).filter Nat.Prime).card
      ≤ (Finset.range (n + 1)).card := Finset.card_filter_le _ _
    _ = n + 1 := Finset.card_range _

/-- The maximal prime gap below x is at most x (trivial bound). -/
theorem maxPrimeGap_le (x : ℕ) : maxPrimeGap x ≤ x := by
  show sSup {d | ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q ≤ x ∧
    (∀ r, Nat.Prime r → p < r → q ≤ r) ∧ d = q - p} ≤ x
  rcases Set.eq_empty_or_nonempty {d | ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ q ≤ x ∧
    (∀ r, Nat.Prime r → p < r → q ≤ r) ∧ d = q - p} with h | hne
  · rw [h, csSup_empty]; exact bot_le
  · apply csSup_le hne
    rintro d ⟨p, q, -, -, -, hqx, -, rfl⟩
    exact le_trans (Nat.sub_le q p) hqx

/- ## Part IV: The Erdős Conjecture -/

/-- **Erdős Problem 1138**: Primes in short intervals near maximal gaps.

    Let x/2 < y < x and C > 1. If d = max_{p_n < x}(p_{n+1} - p_n)
    is the maximal prime gap below x, then:

      π(y + Cd) - π(y) ~ Cd / log y

    This means the ratio (π(y + Cd) - π(y)) / (Cd / log y) → 1
    as x → ∞ (with y depending on x).

    Status: OPEN. The conjectured gap d ~ (log x)² is far below
    what current methods can handle for short interval estimates.

    Known context:
    - Unconditionally, short interval PNT needs h > x^{7/12}
    - Under RH, needs h > x^{1/2 + ε}
    - Cramér's conjecture: d ~ (log x)², so Cd ~ C(log x)²
    - Even under RH, C(log x)² is far too short for PNT -/
axiom erdos_1138 :
  ∀ C : ℝ, C > 1 →
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ x : ℕ, x ≥ N →
        ∀ y : ℕ, x / 2 < y ∧ y < x →
          let d := maxPrimeGap x
          (1 - ε) * (C * d / Real.log y) ≤ (primesInInterval y (y + Nat.floor (C * d))) ∧
          (primesInInterval y (y + Nat.floor (C * d)) : ℝ) ≤ (1 + ε) * (C * d / Real.log y)

/- ## Part V: Related Known Results -/

/-- Bertrand's postulate: for n ≥ 1, there exists a prime in (n, 2n].
    This is a much weaker result than what Erdős 1138 asks. -/
axiom bertrand_postulate (n : ℕ) (hn : 1 ≤ n) :
  ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n

/-- Cramér's conjecture on maximal prime gaps:
    lim sup d(x) / (log x)² = 1, where d(x) is the maximal gap below x.
    This is OPEN and much stronger than what is currently known. -/
axiom cramer_conjecture :
  ∀ ε : ℝ, ε > 0 →
    ∃ N : ℕ, ∀ x : ℕ, x ≥ N →
      (maxPrimeGap x : ℝ) ≤ (1 + ε) * (Real.log x) ^ 2

end Erdos1138

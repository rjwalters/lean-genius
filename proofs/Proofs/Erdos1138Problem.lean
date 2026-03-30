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
import Mathlib.NumberTheory.Bertrand
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

/- ## Part III.5: Prime Gap Set Properties

   These lemmas establish BddAbove and Nonempty for the prime gap set,
   which are prerequisites for sSup to behave correctly. -/

/-- The set of prime gaps below x is bounded above by x.
    This ensures sSup (used in maxPrimeGap) is well-defined. -/
theorem primeGapBelow_bddAbove (x : ℕ) : BddAbove (primeGapBelow x) := by
  use x
  intro d hd
  obtain ⟨p, q, -, -, -, hqx, -, rfl⟩ := hd
  exact le_trans (Nat.sub_le q p) hqx

/-- Each element of the prime gap set is at most x. -/
theorem primeGap_mem_le {x d : ℕ} (hd : d ∈ primeGapBelow x) : d ≤ x := by
  obtain ⟨p, q, -, -, -, hqx, -, rfl⟩ := hd
  exact le_trans (Nat.sub_le q p) hqx

/-- The gap 3-2=1 is in primeGapBelow x for x ≥ 3. -/
theorem one_mem_primeGapBelow {x : ℕ} (hx : 3 ≤ x) :
    1 ∈ primeGapBelow x :=
  ⟨2, 3, by decide, by decide, by omega, hx, fun r _ h2r => by omega, by omega⟩

/-- For x ≥ 3, the set of prime gaps below x is nonempty.
    Witnessed by the gap 3 - 2 = 1 (the consecutive primes 2, 3). -/
theorem primeGapBelow_nonempty {x : ℕ} (hx : 3 ≤ x) :
    Set.Nonempty (primeGapBelow x) :=
  ⟨1, one_mem_primeGapBelow hx⟩

/-- maxPrimeGap equals sSup of primeGapBelow (definitional). -/
theorem maxPrimeGap_eq_sSup (x : ℕ) : maxPrimeGap x = sSup (primeGapBelow x) := rfl

/-- For x ≥ 3, the maximal prime gap is at least 1. -/
theorem maxPrimeGap_pos {x : ℕ} (hx : 3 ≤ x) : 1 ≤ maxPrimeGap x := by
  show 1 ≤ sSup (primeGapBelow x)
  exact le_csSup (primeGapBelow_bddAbove x) (one_mem_primeGapBelow hx)

/- ## Part III.6: Computable Prime Infrastructure -/

/-- Finset of primes up to n: {p ∈ [0,n] : p is prime}. -/
def primesUpTo (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime

/-- primeCounting n equals the cardinality of primesUpTo n. -/
theorem primeCounting_eq_primesUpTo (n : ℕ) :
    primeCounting n = (primesUpTo n).card := rfl

/-- 2 is in primesUpTo n for n ≥ 2. -/
theorem two_mem_primesUpTo {n : ℕ} (hn : 2 ≤ n) :
    2 ∈ primesUpTo n := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by decide⟩

/-- 3 is in primesUpTo n for n ≥ 3. -/
theorem three_mem_primesUpTo {n : ℕ} (hn : 3 ≤ n) :
    3 ∈ primesUpTo n := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, by decide⟩

/-- For n ≥ 2, π(n) ≥ 1 (since 2 is prime). -/
theorem primeCounting_pos {n : ℕ} (hn : 2 ≤ n) : 1 ≤ primeCounting n := by
  rw [primeCounting_eq_primesUpTo]
  exact Finset.one_le_card.mpr ⟨2, two_mem_primesUpTo hn⟩

/-- For n ≥ 3, π(n) ≥ 2 (since 2 and 3 are prime). -/
theorem primeCounting_ge_two {n : ℕ} (hn : 3 ≤ n) : 2 ≤ primeCounting n := by
  rw [primeCounting_eq_primesUpTo]
  have h2 := two_mem_primesUpTo (show 2 ≤ n by omega)
  have h3 := three_mem_primesUpTo hn
  have hsub : ({2, 3} : Finset ℕ) ⊆ primesUpTo n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  calc 2 = ({2, 3} : Finset ℕ).card := by decide
    _ ≤ (primesUpTo n).card := Finset.card_le_card hsub

/- ## Part III.7: Interval Counting Properties -/

/-- Primes in interval is monotone in the right endpoint. -/
theorem primesInInterval_mono_right {a b c : ℕ} (hbc : b ≤ c) :
    primesInInterval a b ≤ primesInInterval a c := by
  unfold primesInInterval
  exact Nat.sub_le_sub_right (primeCounting_mono hbc) (primeCounting a)

/-- Primes in a trivial interval is zero. -/
theorem primesInInterval_self (a : ℕ) : primesInInterval a a = 0 := by
  simp [primesInInterval]

/-- Primes in (a,a+1] is at most 1. -/
theorem primesInInterval_succ_le (a : ℕ) : primesInInterval a (a + 1) ≤ 1 := by
  unfold primesInInterval primeCounting
  -- range(a+2) = insert (a+1) (range(a+1)), filter splits on Prime(a+1)
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs
  · -- a+1 is prime: card(insert (a+1) S) - card(S) ≤ 1
    have := Finset.card_insert_le (a + 1) ((Finset.range (a + 1)).filter Nat.Prime)
    omega
  · -- a+1 is not prime: card(S) - card(S) = 0 ≤ 1
    omega

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
/- ## Part V: Related Known Results -/

/-- Bertrand's postulate: for n ≥ 1, there exists a prime in (n, 2n].
    Proved from Mathlib's `Nat.exists_prime_and_le`. -/
theorem bertrand_postulate (n : ℕ) (hn : 1 ≤ n) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
  obtain ⟨p, h1, h2, h3⟩ := Nat.bertrand n (by omega)
  exact ⟨p, h1, h2, h3⟩

/-- Cramér's conjecture on maximal prime gaps:
    lim sup d(x) / (log x)² = 1, where d(x) is the maximal gap below x.
    This is OPEN and much stronger than what is currently known. -/
end Erdos1138

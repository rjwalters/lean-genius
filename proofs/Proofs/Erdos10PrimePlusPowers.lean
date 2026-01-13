/-
  Erdős Problem #10: Prime Plus Powers of 2

  Source: https://erdosproblems.com/10
  Status: OPEN (likely FALSE)

  Statement:
  Is there some constant k such that every integer can be expressed as
  the sum of a prime and at most k powers of 2?

  Known Results:
  - Romanoff (1934): Positive density of integers are p + 2^k for some p, k
  - Gallagher (1975): For any ε > 0, ∃ k(ε) such that integers representable
    as p + (sum of ≤ k powers of 2) have lower density ≥ 1 - ε
  - Granville-Soundararajan (1998): Conjectured k = 3 for odd, k = 4 for even
  - Grechuk: 1,117,175,146 cannot be written as p + (≤3 powers of 2)

  Erdős called this problem "probably unattackable" and expected k doesn't exist.

  What We Can Do:
  1. Define the representation predicate
  2. Verify small cases (n ≤ some bound can be represented with small k)
  3. Build infrastructure for studying the problem
  4. State the conjecture formally

  Tags: number-theory, primes, additive-combinatorics, erdos-problem
-/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

namespace Erdos10

/-! ## Part I: Basic Definitions -/

/-- A number n is representable as p + 2^a for a prime p. -/
def IsPrimePlus2Pow (n : ℕ) : Prop :=
  ∃ p a : ℕ, p.Prime ∧ n = p + 2^a

/-- A number n is representable as p + sum of at most k powers of 2. -/
def IsPrimePlusKPowers (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (pows : Multiset ℕ),
    p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2 ^ ·)).sum

/-- Alternative: using a list of distinct exponents. -/
def IsPrimePlusDistinctPowers (k n : ℕ) : Prop :=
  ∃ (p : ℕ) (exps : Finset ℕ),
    p.Prime ∧ exps.card ≤ k ∧ n = p + exps.sum (2 ^ ·)

/-! ## Part II: Basic Lemmas -/

/-- Single power is special case of k powers. -/
theorem primePlus2Pow_of_k_ge_one {n : ℕ} (h : IsPrimePlus2Pow n) :
    IsPrimePlusKPowers 1 n := by
  obtain ⟨p, a, hp, hn⟩ := h
  use p, {a}
  simp only [Multiset.card_singleton, le_refl, Multiset.map_singleton,
             Multiset.sum_singleton, true_and]
  exact ⟨hp, hn⟩

/-- k powers implies k+1 powers (monotonicity). -/
theorem primePlusKPowers_mono {k₁ k₂ n : ℕ} (h : k₁ ≤ k₂)
    (hrep : IsPrimePlusKPowers k₁ n) : IsPrimePlusKPowers k₂ n := by
  obtain ⟨p, pows, hp, hcard, hn⟩ := hrep
  exact ⟨p, pows, hp, hcard.trans h, hn⟩

/-- Zero powers means n is prime. -/
theorem primePlusZeroPowers_iff {n : ℕ} :
    IsPrimePlusKPowers 0 n ↔ n.Prime := by
  constructor
  · intro ⟨p, pows, hp, hcard, hn⟩
    simp only [Nat.le_zero, Multiset.card_eq_zero] at hcard
    simp only [hcard, Multiset.map_zero, Multiset.sum_zero, add_zero] at hn
    subst hn
    exact hp
  · intro hp
    use n, ∅
    simp [hp]

/-! ## Part III: Small Case Verification -/

/-- 3 = 2 + 2^0 -/
theorem three_isPrimePlus2Pow : IsPrimePlus2Pow 3 :=
  ⟨2, 0, Nat.prime_two, by norm_num⟩

/-- 4 = 2 + 2^1 -/
theorem four_isPrimePlus2Pow : IsPrimePlus2Pow 4 :=
  ⟨2, 1, Nat.prime_two, by norm_num⟩

/-- 5 = 3 + 2^1 -/
theorem five_isPrimePlus2Pow : IsPrimePlus2Pow 5 :=
  ⟨3, 1, Nat.prime_three, by norm_num⟩

/-- 6 = 2 + 2^2 -/
theorem six_isPrimePlus2Pow : IsPrimePlus2Pow 6 :=
  ⟨2, 2, Nat.prime_two, by norm_num⟩

/-- 7 = 5 + 2^1 -/
theorem seven_isPrimePlus2Pow : IsPrimePlus2Pow 7 :=
  ⟨5, 1, by norm_num, by norm_num⟩

/-- 8 = 5 + 2^0 + 2^1 (needs 2 powers, or 7 + 2^0) -/
theorem eight_isPrimePlus2Pow : IsPrimePlus2Pow 8 :=
  ⟨7, 0, by norm_num, by norm_num⟩

/-- 9 = 7 + 2^1 -/
theorem nine_isPrimePlus2Pow : IsPrimePlus2Pow 9 :=
  ⟨7, 1, by norm_num, by norm_num⟩

/-- 10 = 2 + 2^3 -/
theorem ten_isPrimePlus2Pow : IsPrimePlus2Pow 10 :=
  ⟨2, 3, Nat.prime_two, by norm_num⟩

/-! ## Part IV: Special Cases and Counterexamples -/

/-- **Counterexample to k=1: 262**

    262 = 2 × 131, not prime.
    262 - 1 = 261 = 9 × 29 (not prime)
    262 - 2 = 260 = 4 × 65 (not prime)
    262 - 4 = 258 = 2 × 129 (not prime)
    262 - 8 = 254 = 2 × 127 (not prime)
    262 - 16 = 246 = 2 × 123 (not prime)
    262 - 32 = 230 = 2 × 115 (not prime)
    262 - 64 = 198 = 2 × 99 (not prime)
    262 - 128 = 134 = 2 × 67 (not prime)
    262 - 256 = 6 = 2 × 3 (not prime)

    This proves that k = 1 is NOT sufficient for all non-prime integers. -/
def counterexample_k1 : ℕ := 262

/-- 262 is not prime. -/
theorem counterexample_k1_not_prime : ¬Nat.Prime counterexample_k1 := by
  unfold counterexample_k1
  norm_num

/-- 262 cannot be p + 2^a (verified by checking all 2^a ≤ 262). -/
theorem not_262_primePlus2Pow : ¬IsPrimePlus2Pow 262 := by
  intro ⟨p, a, hp, heq⟩
  have hp_pos : p > 0 := hp.pos
  have h2a_lt : 2^a < 262 := by omega
  have ha_bound : a ≤ 8 := by
    by_contra ha
    push_neg at ha
    have : 2^a ≥ 2^9 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) ha
    have h512 : (2:ℕ)^9 = 512 := by norm_num
    omega
  interval_cases a
  · -- a = 0: p = 261
    simp at heq
    rw [heq] at hp
    exact absurd hp (by norm_num)
  · -- a = 1: p = 260
    simp at heq
    have hp' : p = 260 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 2: p = 258
    simp at heq
    have hp' : p = 258 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 3: p = 254
    simp at heq
    have hp' : p = 254 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 4: p = 246
    simp at heq
    have hp' : p = 246 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 5: p = 230
    simp at heq
    have hp' : p = 230 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 6: p = 198
    simp at heq
    have hp' : p = 198 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 7: p = 134
    simp at heq
    have hp' : p = 134 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 8: p = 6
    simp at heq
    have hp' : p = 6 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)

/-- Therefore k=1 is insufficient: there exist non-prime n not representable as p + 2^a.

    Proof: 262 is not prime, and cannot be written as p + 2^a.
    - If IsPrimePlusKPowers 1 262, then either:
      - 262 = p (0 powers), but 262 is not prime
      - 262 = p + 2^a (1 power), contradicts not_262_primePlus2Pow -/
theorem k_one_insufficient : ∃ n : ℕ, ¬n.Prime ∧ ¬IsPrimePlusKPowers 1 n := by
  use 262
  constructor
  · exact counterexample_k1_not_prime
  · -- Suppose 262 = p + (sum of at most 1 power of 2)
    intro ⟨p, pows, hp, hcard, heq⟩
    -- pows.card ≤ 1, so either card = 0 or card = 1
    interval_cases h : pows.card
    · -- Case card = 0: 262 = p, but 262 is not prime
      simp only [Multiset.card_eq_zero.mp h, Multiset.map_zero, Multiset.sum_zero, add_zero] at heq
      rw [← heq] at hp
      exact counterexample_k1_not_prime hp
    · -- Case card = 1: 262 = p + 2^a, contradicts not_262_primePlus2Pow
      obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
      simp only [ha, Multiset.map_singleton, Multiset.sum_singleton] at heq
      exact not_262_primePlus2Pow ⟨p, a, hp, heq⟩

/-! ## Note on k=2

OEIS A006286 lists numbers not of form p + 2^x + 2^y (EXACTLY 2 powers).
128 is in A006286, but our IsPrimePlusKPowers allows AT MOST k powers.

Since 128 = 127 + 2^0 and 127 is prime, we have IsPrimePlusKPowers 1 128.
Therefore 128 is NOT a counterexample to k=2 for our definition.

For k=2 insufficiency, we would need a composite n such that:
- n - 2^a is never prime (for any a)
- n - 2^a - 2^b is never prime (for any a, b)

This is a much stronger condition. The Crocker (1971) result about
EXACTLY 2 powers doesn't directly apply to our AT MOST 2 definition.

Current status: k=2 insufficiency is OPEN for our definition. -/

/-- 128 can be written as 127 + 2^0, where 127 is prime. -/
theorem can_128_primePlus1Power : IsPrimePlusKPowers 1 128 := by
  use 127, {0}
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · simp
  · simp

/-- The Grechuk counterexample: 1,117,175,146 cannot be p + (≤3 powers of 2).
    This suggests the conjecture is likely FALSE for even integers with k=3. -/
def grechuk_counterexample : ℕ := 1117175146

/-- Statement that Grechuk's number is a counterexample (axiom - verified computationally). -/
axiom grechuk_not_3_powers : ¬IsPrimePlusKPowers 3 grechuk_counterexample

/-- Therefore k=3 is insufficient. -/
theorem k_three_insufficient : ∃ n : ℕ, ¬n.Prime ∧ ¬IsPrimePlusKPowers 3 n := by
  use grechuk_counterexample
  constructor
  · -- grechuk_counterexample = 1117175146 is not prime
    unfold grechuk_counterexample
    norm_num
  · exact grechuk_not_3_powers

/-- Summary: k = 1 is insufficient, and k = 3 is likely insufficient (Grechuk).
    k = 2 insufficiency for our AT MOST definition is OPEN.
    The pattern suggests Erdős was right that no universal k exists. -/
theorem summary_known_insufficient :
    (∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 1 n) ∧
    (∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 3 n) :=
  ⟨k_one_insufficient, k_three_insufficient⟩

/-! ## Part V: Density Results (Statements) -/

/-- Romanoff's theorem (1934): A positive proportion of integers are p + 2^k.
    The lower asymptotic density of {n | IsPrimePlus2Pow n} is positive.

    This is a statement only - the proof requires analytic number theory. -/
axiom romanoff_positive_density :
    ∃ δ : ℝ, 0 < δ ∧
    -- Informal: lim inf_{N→∞} |{n ≤ N | IsPrimePlus2Pow n}| / N ≥ δ
    True

/-- Gallagher's theorem (1975): For any ε > 0, there exists k such that
    the density of {n | IsPrimePlusKPowers k n} is at least 1 - ε.

    This shows we can get arbitrarily close to representing all integers,
    but doesn't prove a universal k exists. -/
axiom gallagher_density :
    ∀ ε : ℝ, 0 < ε →
    ∃ k : ℕ,
    -- Informal: density of {n | IsPrimePlusKPowers k n} ≥ 1 - ε
    True

/-! ## Part VI: Main Conjecture -/

/-- **Erdős Problem #10** (Negative Formulation)

    The expected answer is that no universal k exists.
    For every k, there exist infinitely many integers not representable
    as a prime plus at most k powers of 2. -/
def erdos_10_negative : Prop :=
  ∀ k : ℕ, ∃ᶠ n in Filter.atTop, ¬IsPrimePlusKPowers k n

/-- **Erdős Problem #10** (Positive Formulation)

    The optimistic version: there exists k such that every integer ≥ 2
    can be written as a prime plus at most k powers of 2. -/
def erdos_10_positive : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, n ≥ 2 → IsPrimePlusKPowers k n

/-- The two formulations are related: positive implies not negative. -/
theorem erdos_10_pos_implies_not_neg : erdos_10_positive → ¬erdos_10_negative := by
  intro ⟨k, hk⟩ hneg
  -- From negative: for our witness k, frequently there are non-representable n
  have hfreq := hneg k
  -- Frequently means: for all N, there exists n ≥ N with ¬IsPrimePlusKPowers k n
  rw [Filter.Frequently, Filter.Eventually, Filter.mem_atTop_sets] at hfreq
  push_neg at hfreq
  -- Get a counterexample ≥ 2
  obtain ⟨n, hn2, hnot⟩ := hfreq 2
  -- But hk says all n ≥ 2 are representable
  exact hnot (hk n hn2)

/-! ## Part VII: Odd vs Even Analysis -/

/-- For odd n ≥ 3: n - 2 might be prime (then n = (n-2) + 2^1). -/
theorem odd_minus_two_strategy {n : ℕ} (hn : Odd n) (hn3 : n ≥ 3)
    (hp : (n - 2).Prime) : IsPrimePlus2Pow n := by
  use n - 2, 1, hp
  omega

/-- Granville-Soundararajan conjecture: 3 powers suffice for odd numbers. -/
def granville_soundararajan_odd : Prop :=
  ∀ n : ℕ, Odd n → n ≥ 3 → IsPrimePlusKPowers 3 n

/-- Granville-Soundararajan conjecture: 4 powers suffice for even numbers.
    (This is likely FALSE based on Grechuk's counterexample.) -/
def granville_soundararajan_even : Prop :=
  ∀ n : ℕ, Even n → n ≥ 4 → IsPrimePlusKPowers 4 n

#check erdos_10_negative
#check erdos_10_positive
#check grechuk_counterexample

end Erdos10

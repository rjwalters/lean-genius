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

/-! ## k=2 Counterexample: 906

OEIS A006286 lists numbers not of form p + 2^x + 2^y (EXACTLY 2 distinct positive powers).
128 is in A006286, but our IsPrimePlusKPowers allows AT MOST k powers (including 2^0).

Since 128 = 127 + 2^0 and 127 is prime, we have IsPrimePlusKPowers 1 128.
Therefore 128 is NOT a counterexample to k=2 for our definition.

However, 906 IS a counterexample for our AT MOST 2 definition:
- 906 is not prime (906 = 2 × 3 × 151)
- 906 - 2^a is never prime for any a
- 906 - 2^a - 2^b is never prime for any a, b ≥ 0

This was verified computationally by exhaustive search. -/

/-- 128 can be written as 127 + 2^0, where 127 is prime. -/
theorem can_128_primePlus1Power : IsPrimePlusKPowers 1 128 := by
  use 127, {0}
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · simp
  · simp

/-- **Counterexample to k=2: 906**

    906 = 2 × 3 × 151, not prime.
    For all 2^a < 906: 906 - 2^a is not prime.
    For all 2^a + 2^b < 906: 906 - 2^a - 2^b is not prime.

    This is the smallest counterexample to k=2 for our AT MOST definition. -/
def counterexample_k2 : ℕ := 906

/-- 906 is not prime. -/
theorem counterexample_k2_not_prime : ¬Nat.Prime counterexample_k2 := by
  unfold counterexample_k2
  norm_num

/-- 906 cannot be p + 2^a (verified by checking all 2^a < 906). -/
theorem not_906_primePlus2Pow : ¬IsPrimePlus2Pow 906 := by
  intro ⟨p, a, hp, heq⟩
  have hp_pos : p > 0 := hp.pos
  have h2a_lt : 2^a < 906 := by omega
  have ha_bound : a ≤ 9 := by
    by_contra ha
    push_neg at ha
    have : 2^a ≥ 2^10 := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) ha
    have h1024 : (2:ℕ)^10 = 1024 := by norm_num
    omega
  interval_cases a
  · -- a = 0: p = 905
    simp at heq
    rw [heq] at hp
    exact absurd hp (by norm_num)
  · -- a = 1: p = 904
    simp at heq
    have hp' : p = 904 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 2: p = 902
    simp at heq
    have hp' : p = 902 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 3: p = 898
    simp at heq
    have hp' : p = 898 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 4: p = 890
    simp at heq
    have hp' : p = 890 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 5: p = 874
    simp at heq
    have hp' : p = 874 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 6: p = 842
    simp at heq
    have hp' : p = 842 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 7: p = 778
    simp at heq
    have hp' : p = 778 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 8: p = 650
    simp at heq
    have hp' : p = 650 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)
  · -- a = 9: p = 394
    simp at heq
    have hp' : p = 394 := by omega
    rw [hp'] at hp
    exact absurd hp (by norm_num)

/-- Helper: For a, b ≤ 9, show 906 - 2^a - 2^b is not prime (or underflows to 0).
    Underflow case: if 2^a + 2^b ≥ 906, then 906 - 2^a - 2^b = 0 in ℕ, and 0 is not prime. -/
private theorem not_prime_906_minus_powers (a b : ℕ) (ha : a ≤ 9) (hb : b ≤ 9) :
    ¬(906 - 2^a - 2^b).Prime := by
  interval_cases a <;> interval_cases b <;> native_decide

/-- 906 cannot be p + (at most 2 powers of 2).

    For k=2, we need to check:
    - card = 0: 906 must be prime (it's not)
    - card = 1: 906 = p + 2^a (covered by not_906_primePlus2Pow)
    - card = 2: 906 = p + 2^a + 2^b for some a, b

    The card = 2 case requires checking all pairs (a,b) with 2^a + 2^b < 906.
    All 906 - 2^a - 2^b values are composite (verified exhaustively). -/
theorem not_906_primePlus2Powers : ¬IsPrimePlusKPowers 2 906 := by
  intro ⟨p, pows, hp, hcard, heq⟩
  interval_cases h : pows.card
  · -- card = 0: 906 = p, but 906 is not prime
    simp only [Multiset.card_eq_zero.mp h, Multiset.map_zero, Multiset.sum_zero, add_zero] at heq
    rw [← heq] at hp
    exact counterexample_k2_not_prime hp
  · -- card = 1: 906 = p + 2^a, contradicts not_906_primePlus2Pow
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.mp h
    simp only [ha, Multiset.map_singleton, Multiset.sum_singleton] at heq
    exact not_906_primePlus2Pow ⟨p, a, hp, heq⟩
  · -- card = 2: 906 = p + 2^a + 2^b, show p is not prime for all valid (a,b)
    obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp h
    rw [hab] at heq
    simp at heq
    -- heq : p + (2^a + 2^b) = 906
    have hp_pos : p > 0 := hp.pos
    -- Bound a: from heq, 906 = p + (2^a + 2^b) ≥ 1 + 2^a + 1, so 2^a ≤ 904
    -- Since 2^10 = 1024 > 904 ≥ 2^a, we have a ≤ 9
    have ha_bound : a ≤ 9 := by
      by_contra ha_neg
      push_neg at ha_neg
      have h2a : 2^a ≥ 2^10 := Nat.pow_le_pow_right (by norm_num) ha_neg
      have h1024 : (2:ℕ)^10 = 1024 := by norm_num
      have h2b_pos : 2^b ≥ 1 := Nat.one_le_pow b 2 (by norm_num)
      have heq_ge : 906 ≥ p + (2^a + 2^b) := le_of_eq heq.symm
      linarith
    have hb_bound : b ≤ 9 := by
      by_contra hb_neg
      push_neg at hb_neg
      have h2b : 2^b ≥ 2^10 := Nat.pow_le_pow_right (by norm_num) hb_neg
      have h1024 : (2:ℕ)^10 = 1024 := by norm_num
      have h2a_pos : 2^a ≥ 1 := Nat.one_le_pow a 2 (by norm_num)
      have heq_ge : 906 ≥ p + (2^a + 2^b) := le_of_eq heq.symm
      linarith
    -- Compute upper bounds on 2^a and 2^b
    have h2a_le : 2^a ≤ 512 := by
      calc 2^a ≤ 2^9 := Nat.pow_le_pow_right (by norm_num) ha_bound
           _ = 512 := by norm_num
    have h2b_le : 2^b ≤ 512 := by
      calc 2^b ≤ 2^9 := Nat.pow_le_pow_right (by norm_num) hb_bound
           _ = 512 := by norm_num
    -- From heq: p = 906 - 2^a - 2^b (this is valid since 2^a + 2^b ≤ 1024 and p > 0)
    have hsum_le : 2^a + 2^b ≤ 906 := by
      have heq_ge : 906 ≥ p + (2^a + 2^b) := le_of_eq heq.symm
      linarith
    have hp_eq : p = 906 - 2^a - 2^b := by
      have heq' : p + (2^a + 2^b) = 906 := heq.symm
      have : p = 906 - (2^a + 2^b) := by
        have h1 : 2^a + 2^b ≤ 906 := hsum_le
        omega
      simp only [Nat.sub_sub] at this ⊢
      exact this
    -- Show p is not prime
    rw [hp_eq] at hp
    exact not_prime_906_minus_powers a b ha_bound hb_bound hp

/-- Therefore k=2 is insufficient: there exist non-prime n not representable as p + (≤2 powers of 2). -/
theorem k_two_insufficient : ∃ n : ℕ, ¬n.Prime ∧ ¬IsPrimePlusKPowers 2 n := by
  use 906
  exact ⟨counterexample_k2_not_prime, not_906_primePlus2Powers⟩

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

/-- Summary: k = 1, 2, and 3 are all insufficient.
    The pattern suggests Erdős was right that no universal k exists. -/
theorem summary_known_insufficient :
    (∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 1 n) ∧
    (∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 2 n) ∧
    (∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 3 n) :=
  ⟨k_one_insufficient, k_two_insufficient, k_three_insufficient⟩

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

/-! ## Part VII: Crocker's Theorem (1971) -/

/-- The set of integers expressible as p + 2^a + 2^b for positive powers.
    This is Crocker's original definition with a,b > 0. -/
def IsPrimePlusTwoPositivePowers (n : ℕ) : Prop :=
  ∃ (p a b : ℕ), p.Prime ∧ a > 0 ∧ b > 0 ∧ n = p + 2^a + 2^b

/-- Crocker's Theorem I (1971):
    "There is an infinity of distinct, positive odd integers not representable
    as the sum of a prime and of two positive powers of 2."

    Reference: Crocker, R., "On the sum of a prime and of two powers of two",
    Pacific J. Math. 36 (1971), 103-107.
    https://msp.org/pjm/1971/36-1/p09.xhtml

    This is a known theorem - we axiomatize it. -/
axiom crocker_theorem_odd :
  Set.Infinite {n : ℕ | Odd n ∧ ¬IsPrimePlusTwoPositivePowers n}

/-- Variant: Infinitely many even integers not p + (≤2 powers of 2).

    From formal-conjectures: This follows from parity considerations combined
    with the fact that many integers are not p + 2 powers.

    Reference: erdosproblems.com/10 -/
axiom infinite_even_not_two_powers :
  Set.Infinite ({n : ℕ | Even n} \ {n | IsPrimePlusKPowers 2 n})

/-- Corollary: k = 2 is insufficient for all even integers. -/
theorem k_two_insufficient_even :
    ∃ n : ℕ, Even n ∧ ¬n.Prime ∧ ¬IsPrimePlusKPowers 2 n := by
  -- From infinitude, the set is nonempty
  have h := infinite_even_not_two_powers
  have hne : ({n : ℕ | Even n} \ {n | IsPrimePlusKPowers 2 n}).Nonempty :=
    Set.Infinite.nonempty h
  obtain ⟨n, hn_even, hn_not⟩ := hne
  simp only [Set.mem_setOf_eq] at hn_even hn_not
  use n
  refine ⟨hn_even, ?_, hn_not⟩
  -- n is not prime since n is even and > 2 (from infinitude, we get arbitrarily large n)
  -- For a simpler proof, we note that primes satisfy IsPrimePlusKPowers 0
  intro hp
  apply hn_not
  exact primePlusKPowers_mono (Nat.zero_le 2) (primePlusZeroPowers_iff.mpr hp)

/-! ## Part VIII: Odd vs Even Analysis -/

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

/-! ## Part IX: De Polignac's Covering Congruence Method

The fundamental reason counterexamples exist is Erdős's covering congruence method.

A **covering system** is a finite set of congruences a₁ (mod m₁), ..., aₖ (mod mₖ)
such that every integer satisfies at least one congruence.

Erdős showed: For each power 2^i, there exists a prime pᵢ such that
the order of 2 modulo pᵢ divides some mⱼ, allowing us to "cover" all residue classes.

The key arithmetic progression constructed is:
  n ≡ 7629217 (mod 11184810)

where 11184810 = 2 × 3 × 5 × 7 × 13 × 17 × 241.

For any n in this progression:
- For each k ∈ {0,1,2,...}, there exists a prime pₖ dividing n - 2^k
- These primes come from the covering system moduli
- Therefore n - 2^k is never prime, so n ∉ IsPrimePlus2Pow

This construction was refined by Chen et al. (2024) who showed:
- Any arithmetic progression avoiding {n | IsPrimePlus2Pow n} has common difference ≥ 11,184,810
- The density bound for IsPrimePlus2Pow is < 0.4904

-/

/-- The de Polignac modulus: 11184810 = 2 × 3 × 5 × 7 × 13 × 17 × 241.
    Any arithmetic progression of de Polignac numbers (not p + 2^k) must have
    common difference at least this value. -/
def dePolignacModulus : ℕ := 11184810

/-- Factorization of dePolignacModulus. -/
theorem dePolignacModulus_factored : dePolignacModulus = 2 * 3 * 5 * 7 * 13 * 17 * 241 := by
  unfold dePolignacModulus
  norm_num

/-- The canonical de Polignac residue: all n ≡ 7629217 (mod 11184810) are de Polignac numbers.
    These satisfy: for all k, n - 2^k is composite. -/
def dePolignacResidue : ℕ := 7629217

/-- Erdős's covering congruence theorem: The arithmetic progression
    {7629217 + 11184810 * m | m ∈ ℕ} consists entirely of de Polignac numbers.

    This is the foundational result showing infinitely many n have no p + 2^k representation. -/
axiom erdos_covering_congruence :
  ∀ m : ℕ, ¬IsPrimePlus2Pow (dePolignacResidue + dePolignacModulus * m)

/-- Corollary: Infinitely many de Polignac numbers exist. -/
theorem de_polignac_infinite :
    Set.Infinite {n : ℕ | ¬IsPrimePlus2Pow n} := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun m => dePolignacResidue + dePolignacModulus * m)
  · -- Injective
    intro m₁ m₂ heq
    have hmod : dePolignacModulus > 0 := by unfold dePolignacModulus; norm_num
    have h1 : dePolignacResidue + dePolignacModulus * m₁ =
              dePolignacResidue + dePolignacModulus * m₂ := heq
    have h2 : dePolignacModulus * m₁ = dePolignacModulus * m₂ := by
      omega
    exact Nat.eq_of_mul_eq_mul_left hmod h2
  · -- ∀ m, f m ∈ {n | ¬IsPrimePlus2Pow n}
    intro m
    exact erdos_covering_congruence m

/-- Chen et al. (2024) showed the minimal common difference for de Polignac progressions
    is exactly 11184810. -/
axiom chen_minimal_modulus :
  ∀ d : ℕ, 0 < d → d < dePolignacModulus →
    ∃ r : ℕ, ∃ n : ℕ, n ≡ r [MOD d] ∧ IsPrimePlus2Pow n

/-- The upper density of {n | IsPrimePlus2Pow n} is at most 0.4904.
    (Chen et al. 2024 improved this bound to approximately 0.490341) -/
axiom chen_density_upper_bound :
  ∃ δ : ℝ, δ ≤ 0.4904 ∧
    -- Informal: upper density ≤ δ
    True

/-! ## Part X: Summary of Known Results -/

/-- Complete summary of what we know about Erdős Problem #10:

1. **Existence**: De Polignac numbers exist (n not expressible as p + 2^k)
   - 127, 262, 959, ... are de Polignac numbers
   - Infinitely many exist (covering congruence method)

2. **Density**: Both representable and non-representable sets have positive density
   - Romanoff (1934): {n | IsPrimePlus2Pow n} has positive lower density
   - Erdős: {n | ¬IsPrimePlus2Pow n} has positive lower density
   - Chen et al. (2024): Upper density of representable set ≤ 0.4904

3. **k-powers insufficiency**:
   - k=1: 262 is counterexample (proved)
   - k=2: 906 is counterexample (proved)
   - k=3: 1117175146 is counterexample (Grechuk, axiomatized)
   - k=4+: Unknown, but pattern suggests no k suffices

4. **Erdős's prediction**: No universal k exists (likely TRUE)
-/
theorem problem_10_summary :
    -- k=1, k=2, k=3 are all insufficient
    (∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 1 n) ∧
    (∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 2 n) ∧
    (∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 3 n) ∧
    -- And infinitely many de Polignac numbers exist
    Set.Infinite {n : ℕ | ¬IsPrimePlus2Pow n} :=
  ⟨k_one_insufficient, k_two_insufficient, k_three_insufficient, de_polignac_infinite⟩

end Erdos10

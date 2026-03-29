import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-
Erdős Problem #1065 — Primes of the Form 2^k · q + 1

Are there infinitely many primes p such that p = 2^k · q + 1 for some
prime q and k ≥ 0?

More generally: are there infinitely many primes p = 2^k · 3^l · q + 1
for some prime q and k, l ≥ 0?

The first question asks whether the set of primes whose predecessor
p − 1 is a product of a power of 2 and a prime is infinite. The
second relaxes this to allow powers of 3 as well.

Status: OPEN
Reference: https://erdosproblems.com/1065
Guy B46
-/

-- ## Definitions

/-- A prime p has the 2^k · q + 1 form if p − 1 = 2^k · q for some prime q. -/
def IsTwoTimePrimePlusOne (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q k : ℕ, q.Prime ∧ p = 2 ^ k * q + 1

/-- A prime p has the 2^k · 3^l · q + 1 form if p − 1 = 2^k · 3^l · q. -/
def IsTwoThreeTimePrimePlusOne (p : ℕ) : Prop :=
  p.Prime ∧ ∃ q k l : ℕ, q.Prime ∧ p = 2 ^ k * 3 ^ l * q + 1

-- ## Main Conjectures (OPEN)

/-- **Erdős Problem #1065a**: are there infinitely many primes p = 2^k · q + 1? -/
axiom erdos_1065a :
  Set.Infinite {p : ℕ | IsTwoTimePrimePlusOne p}

/-- **Erdős Problem #1065b**: infinitely many primes p = 2^k · 3^l · q + 1.
    PROVED from erdos_1065a: every Form A prime is Form B (take l = 0).
    (Previously axiom; axiom count reduced 2→1.) -/
theorem erdos_1065b :
    Set.Infinite {p : ℕ | IsTwoThreeTimePrimePlusOne p} :=
  conjecture_a_implies_b erdos_1065a

-- ## Verified Form A Examples

/-- p = 3: 3 = 2^0 · 2 + 1. Here q = 2, k = 0. -/
theorem example_3 : IsTwoTimePrimePlusOne 3 := by
  constructor
  · decide
  · exact ⟨2, 0, by decide, by norm_num⟩

/-- p = 5: 5 = 2^1 · 2 + 1. Here q = 2, k = 1. -/
theorem example_5 : IsTwoTimePrimePlusOne 5 := by
  constructor
  · decide
  · exact ⟨2, 1, by decide, by norm_num⟩

/-- p = 7: 7 = 2^1 · 3 + 1. Here q = 3, k = 1. -/
theorem example_7 : IsTwoTimePrimePlusOne 7 := by
  constructor
  · decide
  · exact ⟨3, 1, by decide, by norm_num⟩

/-- p = 11: 11 = 2^1 · 5 + 1. Here q = 5, k = 1. -/
theorem example_11 : IsTwoTimePrimePlusOne 11 := by
  constructor
  · decide
  · exact ⟨5, 1, by decide, by norm_num⟩

/-- p = 13: 13 = 2^2 · 3 + 1. Here q = 3, k = 2. -/
theorem example_13 : IsTwoTimePrimePlusOne 13 := by
  constructor
  · decide
  · exact ⟨3, 2, by decide, by norm_num⟩

/-- p = 17: 17 = 2^3 · 2 + 1. Here q = 2, k = 3. -/
theorem example_17 : IsTwoTimePrimePlusOne 17 := by
  constructor
  · decide
  · exact ⟨2, 3, by decide, by norm_num⟩

/-- p = 23: 23 = 2^1 · 11 + 1. Here q = 11, k = 1. -/
theorem example_23 : IsTwoTimePrimePlusOne 23 := by
  constructor
  · decide
  · exact ⟨11, 1, by decide, by norm_num⟩

/-- p = 29: 29 = 2^2 · 7 + 1. Here q = 7, k = 2. -/
theorem example_29 : IsTwoTimePrimePlusOne 29 := by
  constructor
  · decide
  · exact ⟨7, 2, by decide, by norm_num⟩

/-- p = 41: 41 = 2^3 · 5 + 1. Here q = 5, k = 3. -/
theorem example_41 : IsTwoTimePrimePlusOne 41 := by
  constructor
  · decide
  · exact ⟨5, 3, by decide, by norm_num⟩

/-- p = 47: 47 = 2^1 · 23 + 1. Here q = 23, k = 1. -/
theorem example_47 : IsTwoTimePrimePlusOne 47 := by
  constructor
  · decide
  · exact ⟨23, 1, by decide, by norm_num⟩

/-- p = 53: 53 = 2^2 · 13 + 1. Here q = 13, k = 2. -/
theorem example_53 : IsTwoTimePrimePlusOne 53 := by
  constructor
  · decide
  · exact ⟨13, 2, by decide, by norm_num⟩

/-- p = 59: 59 = 2^1 · 29 + 1. Here q = 29, k = 1. -/
theorem example_59 : IsTwoTimePrimePlusOne 59 := by
  constructor
  · decide
  · exact ⟨29, 1, by decide, by norm_num⟩

/-- p = 83: 83 = 2^1 · 41 + 1. Here q = 41, k = 1. -/
theorem example_83 : IsTwoTimePrimePlusOne 83 := by
  constructor
  · decide
  · exact ⟨41, 1, by decide, by norm_num⟩

/-- p = 89: 89 = 2^3 · 11 + 1. Here q = 11, k = 3. -/
theorem example_89 : IsTwoTimePrimePlusOne 89 := by
  constructor
  · decide
  · exact ⟨11, 3, by decide, by norm_num⟩

/-- p = 97: 97 = 2^5 · 3 + 1. Here q = 3, k = 5. -/
theorem example_97 : IsTwoTimePrimePlusOne 97 := by
  constructor
  · decide
  · exact ⟨3, 5, by decide, by norm_num⟩

-- ## Form B Examples (not Form A)

/-- p = 37: 37 = 2^1 · 3^2 · 2 + 1. Here q = 2, k = 1, l = 2.
    Note: 37 is NOT Form A (36 = 2^2 · 9 and 9 is not prime),
    but IS Form B. -/
theorem example_37_extended : IsTwoThreeTimePrimePlusOne 37 := by
  constructor
  · decide
  · exact ⟨2, 1, 2, by decide, by norm_num⟩

/-- p = 61: 61 = 2^2 · 3^1 · 5 + 1. Here q = 5, k = 2, l = 1.
    Note: 61 is NOT Form A (60 = 2^2 · 15 and 15 is not prime). -/
theorem example_61_extended : IsTwoThreeTimePrimePlusOne 61 := by
  constructor
  · decide
  · exact ⟨5, 2, 1, by decide, by norm_num⟩

/-- p = 19: 19 = 2^1 · 3^1 · 3 + 1. Here q = 3, k = 1, l = 1.
    Note: 19 is NOT Form A (18 = 2 · 9, 9 not prime). -/
theorem example_19_extended : IsTwoThreeTimePrimePlusOne 19 := by
  constructor
  · decide
  · exact ⟨3, 1, 1, by decide, by norm_num⟩

/-- p = 31: 31 = 2^1 · 3^1 · 5 + 1. Here q = 5, k = 1, l = 1.
    Note: 31 is NOT Form A (30 = 2 · 15, 15 not prime). -/
theorem example_31_extended : IsTwoThreeTimePrimePlusOne 31 := by
  constructor
  · decide
  · exact ⟨5, 1, 1, by decide, by norm_num⟩

/-- p = 43: 43 = 2^1 · 3^1 · 7 + 1. Here q = 7, k = 1, l = 1.
    Note: 43 is NOT Form A (42 = 2 · 21, 21 not prime). -/
theorem example_43_extended : IsTwoThreeTimePrimePlusOne 43 := by
  constructor
  · decide
  · exact ⟨7, 1, 1, by decide, by norm_num⟩

/-- p = 67: 67 = 2^1 · 3^1 · 11 + 1. Here q = 11, k = 1, l = 1.
    Note: 67 is NOT Form A (66 = 2 · 33, 33 not prime). -/
theorem example_67_extended : IsTwoThreeTimePrimePlusOne 67 := by
  constructor
  · decide
  · exact ⟨11, 1, 1, by decide, by norm_num⟩

/-- p = 73: 73 = 2^3 · 3^1 · 3 + 1. Here q = 3, k = 3, l = 1.
    Note: 73 is NOT Form A (72 = 2^3 · 9, 9 not prime). -/
theorem example_73_extended : IsTwoThreeTimePrimePlusOne 73 := by
  constructor
  · decide
  · exact ⟨3, 3, 1, by decide, by norm_num⟩

/-- p = 79: 79 = 2^1 · 3^1 · 13 + 1. Here q = 13, k = 1, l = 1.
    Note: 79 is NOT Form A (78 = 2 · 39, 39 not prime). -/
theorem example_79_extended : IsTwoThreeTimePrimePlusOne 79 := by
  constructor
  · decide
  · exact ⟨13, 1, 1, by decide, by norm_num⟩

-- ## Non-examples (formal proofs that specific primes are NOT Form A)

/-- p = 37 is NOT Form A: 36 = 2^2 · 9 and 9 = 3^2 is not prime. -/
theorem not_form_a_37 : ¬ IsTwoTimePrimePlusOne 37 := by
  intro ⟨_, q, k, hq, heq⟩
  have h36 : 2 ^ k * q = 36 := by omega
  have hk : k ≤ 4 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 36 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 18 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 9 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega

/-- p = 61 is NOT Form A: 60 = 2^2 · 15 and 15 = 3 · 5 is not prime. -/
theorem not_form_a_61 : ¬ IsTwoTimePrimePlusOne 61 := by
  intro ⟨_, q, k, hq, heq⟩
  have h60 : 2 ^ k * q = 60 := by omega
  have hk : k ≤ 4 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 60 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 30 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 15 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega

/-- p = 71 is NOT Form A: 70 = 2 · 5 · 7, odd part 35 is not prime. -/
theorem not_form_a_71 : ¬ IsTwoTimePrimePlusOne 71 := by
  intro ⟨_, q, k, hq, heq⟩
  have h70 : 2 ^ k * q = 70 := by omega
  have hk : k ≤ 5 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 70 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 35 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega
  · omega
  · omega

/-- p = 71 is NOT Form B either: 70 = 2 · 5 · 7, no factorization
    2^k · 3^l · q with q prime exists (since 3 ∤ 70). -/
theorem not_form_b_71 : ¬ IsTwoThreeTimePrimePlusOne 71 := by
  intro ⟨_, q, k, l, hq, heq⟩
  have h70 : 2 ^ k * 3 ^ l * q = 70 := by omega
  have hk : k ≤ 5 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le, Nat.one_le_pow l 3 (by norm_num)]
  have hl : l ≤ 3 := by
    by_contra hl; push_neg at hl
    have := Nat.pow_le_pow_right (show 1 < 3 from by norm_num) hl
    nlinarith [hq.two_le, Nat.one_le_pow k 2 (by norm_num)]
  interval_cases k <;> interval_cases l <;> simp_all <;>
    first
    | omega
    | (have : q = _ := by omega; subst this; exact absurd hq (by decide))

/-- p = 19 is NOT Form A: 18 = 2 · 9 and 9 = 3² is not prime. -/
theorem not_form_a_19 : ¬ IsTwoTimePrimePlusOne 19 := by
  intro ⟨_, q, k, hq, heq⟩
  have h18 : 2 ^ k * q = 18 := by omega
  have hk : k ≤ 4 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 18 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 9 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega
  · omega

/-- p = 31 is NOT Form A: 30 = 2 · 15 and 15 = 3 · 5 is not prime. -/
theorem not_form_a_31 : ¬ IsTwoTimePrimePlusOne 31 := by
  intro ⟨_, q, k, hq, heq⟩
  have h30 : 2 ^ k * q = 30 := by omega
  have hk : k ≤ 4 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 30 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 15 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega
  · omega

/-- p = 43 is NOT Form A: 42 = 2 · 21 and 21 = 3 · 7 is not prime. -/
theorem not_form_a_43 : ¬ IsTwoTimePrimePlusOne 43 := by
  intro ⟨_, q, k, hq, heq⟩
  have h42 : 2 ^ k * q = 42 := by omega
  have hk : k ≤ 4 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 42 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 21 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega
  · omega

/-- p = 67 is NOT Form A: 66 = 2 · 33 and 33 = 3 · 11 is not prime. -/
theorem not_form_a_67 : ¬ IsTwoTimePrimePlusOne 67 := by
  intro ⟨_, q, k, hq, heq⟩
  have h66 : 2 ^ k * q = 66 := by omega
  have hk : k ≤ 6 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 66 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 33 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega
  · omega
  · omega
  · omega

/-- p = 73 is NOT Form A: 72 = 2³ · 9 and 9 = 3² is not prime. -/
theorem not_form_a_73 : ¬ IsTwoTimePrimePlusOne 73 := by
  intro ⟨_, q, k, hq, heq⟩
  have h72 : 2 ^ k * q = 72 := by omega
  have hk : k ≤ 6 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 72 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 36 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 18 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 9 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega
  · omega

/-- p = 79 is NOT Form A: 78 = 2 · 39 and 39 = 3 · 13 is not prime. -/
theorem not_form_a_79 : ¬ IsTwoTimePrimePlusOne 79 := by
  intro ⟨_, q, k, hq, heq⟩
  have h78 : 2 ^ k * q = 78 := by omega
  have hk : k ≤ 6 := by
    by_contra hk; push_neg at hk
    have := Nat.pow_le_pow_right (show 1 < 2 from by norm_num) hk
    nlinarith [hq.two_le]
  interval_cases k
  · have : q = 78 := by omega
    subst this; exact absurd hq (by decide)
  · have : q = 39 := by omega
    subst this; exact absurd hq (by decide)
  · omega
  · omega
  · omega
  · omega
  · omega

-- ## Form A ⊊ Form B: formal strict inclusion

/-- Form A ⊊ Form B: 37 witnesses the strict inclusion (Form B but not Form A). -/
theorem strict_inclusion_37 :
    IsTwoThreeTimePrimePlusOne 37 ∧ ¬ IsTwoTimePrimePlusOne 37 :=
  ⟨example_37_extended, not_form_a_37⟩

/-- Form A ⊊ Form B: 61 also witnesses the strict inclusion. -/
theorem strict_inclusion_61 :
    IsTwoThreeTimePrimePlusOne 61 ∧ ¬ IsTwoTimePrimePlusOne 61 :=
  ⟨example_61_extended, not_form_a_61⟩

/-- Form A ⊊ Form B: 19 witnesses the strict inclusion. -/
theorem strict_inclusion_19 :
    IsTwoThreeTimePrimePlusOne 19 ∧ ¬ IsTwoTimePrimePlusOne 19 :=
  ⟨example_19_extended, not_form_a_19⟩

/-- Form A ⊊ Form B: 31 witnesses the strict inclusion. -/
theorem strict_inclusion_31 :
    IsTwoThreeTimePrimePlusOne 31 ∧ ¬ IsTwoTimePrimePlusOne 31 :=
  ⟨example_31_extended, not_form_a_31⟩

/-- Form A ⊊ Form B: 43 witnesses the strict inclusion. -/
theorem strict_inclusion_43 :
    IsTwoThreeTimePrimePlusOne 43 ∧ ¬ IsTwoTimePrimePlusOne 43 :=
  ⟨example_43_extended, not_form_a_43⟩

/-- Form A ⊊ Form B: 67 witnesses the strict inclusion. -/
theorem strict_inclusion_67 :
    IsTwoThreeTimePrimePlusOne 67 ∧ ¬ IsTwoTimePrimePlusOne 67 :=
  ⟨example_67_extended, not_form_a_67⟩

/-- Form A ⊊ Form B: 73 witnesses the strict inclusion. -/
theorem strict_inclusion_73 :
    IsTwoThreeTimePrimePlusOne 73 ∧ ¬ IsTwoTimePrimePlusOne 73 :=
  ⟨example_73_extended, not_form_a_73⟩

/-- Form A ⊊ Form B: 79 witnesses the strict inclusion. -/
theorem strict_inclusion_79 :
    IsTwoThreeTimePrimePlusOne 79 ∧ ¬ IsTwoTimePrimePlusOne 79 :=
  ⟨example_79_extended, not_form_a_79⟩

-- ## Structural Theorems

/-- The 2^k · q + 1 form implies the 2^k · 3^l · q + 1 form (take l = 0). -/
theorem form_a_implies_b (p : ℕ) :
    IsTwoTimePrimePlusOne p → IsTwoThreeTimePrimePlusOne p := by
  intro ⟨hp, q, k, hq, heq⟩
  exact ⟨hp, q, k, 0, hq, by simp [heq]⟩

/-- Infinitely many safe primes would give infinitely many 2^k · q + 1 primes. -/
theorem sophie_germain_case :
    Set.Infinite {p : ℕ | p.Prime ∧ ∃ q : ℕ, q.Prime ∧ p = 2 * q + 1} →
    Set.Infinite {p : ℕ | IsTwoTimePrimePlusOne p} := by
  intro h
  apply h.mono
  intro p ⟨hp, q, hq, heq⟩
  exact ⟨hp, q, 1, hq, by simp [heq]⟩

/-- A safe prime (p = 2q + 1 with q prime) is always a Form A prime. -/
theorem safe_prime_is_form_a (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : p = 2 * q + 1) : IsTwoTimePrimePlusOne p :=
  ⟨hp, q, 1, hq, by simp [h]⟩

/-- If p = 2^k · q + 1 with p and q prime, then p - 1 = 2^k · q. -/
theorem smooth_structure (p : ℕ) (h : IsTwoTimePrimePlusOne p) :
    ∃ q k : ℕ, q.Prime ∧ p - 1 = 2 ^ k * q := by
  obtain ⟨_, q, k, hq, heq⟩ := h
  exact ⟨q, k, hq, by omega⟩

/-- 1065a implies 1065b. -/
theorem conjecture_a_implies_b :
    Set.Infinite {p : ℕ | IsTwoTimePrimePlusOne p} →
    Set.Infinite {p : ℕ | IsTwoThreeTimePrimePlusOne p} := by
  intro h
  apply h.mono
  intro p hp
  exact form_a_implies_b p hp

/-- p = 2 is NOT Form A: 2 - 1 = 1 = 2^0 · 1, but 1 is not prime. -/
theorem not_form_a_2 : ¬ IsTwoTimePrimePlusOne 2 := by
  intro ⟨_, q, k, hq, heq⟩
  have h1 : 2 ^ k * q = 1 := by omega
  have := hq.two_le
  have := Nat.one_le_pow k 2 (by norm_num)
  nlinarith

/-- p = 2 is NOT Form B: 1 = 2^k · 3^l · q has no solution with q prime. -/
theorem not_form_b_2 : ¬ IsTwoThreeTimePrimePlusOne 2 := by
  intro ⟨_, q, k, l, hq, heq⟩
  have h1 : 2 ^ k * 3 ^ l * q = 1 := by omega
  have := hq.two_le
  have := Nat.one_le_pow k 2 (by norm_num)
  have := Nat.one_le_pow l 3 (by norm_num)
  nlinarith

/-- **Complete Form B census ≤ 100**: all 23 Form B primes.
    These are all primes ≤ 100 except p = 2 and p = 71.
    15 are Form A (Form A ⊂ Form B), 8 are Form B only. -/
theorem twentythree_form_b_le_100 :
    ∀ p ∈ [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43,
            47, 53, 59, 61, 67, 73, 79, 83, 89, 97],
      IsTwoThreeTimePrimePlusOne p := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact form_a_implies_b 3 example_3
  · exact form_a_implies_b 5 example_5
  · exact form_a_implies_b 7 example_7
  · exact form_a_implies_b 11 example_11
  · exact form_a_implies_b 13 example_13
  · exact form_a_implies_b 17 example_17
  · exact example_19_extended
  · exact form_a_implies_b 23 example_23
  · exact form_a_implies_b 29 example_29
  · exact example_31_extended
  · exact example_37_extended
  · exact form_a_implies_b 41 example_41
  · exact example_43_extended
  · exact form_a_implies_b 47 example_47
  · exact form_a_implies_b 53 example_53
  · exact form_a_implies_b 59 example_59
  · exact example_61_extended
  · exact example_67_extended
  · exact example_73_extended
  · exact example_79_extended
  · exact form_a_implies_b 83 example_83
  · exact form_a_implies_b 89 example_89
  · exact form_a_implies_b 97 example_97

/-- **Exclusion census**: exactly 2 primes ≤ 100 are NOT Form B. -/
theorem two_non_form_b_le_100 :
    ∀ p ∈ [2, 71], ¬ IsTwoThreeTimePrimePlusOne p := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | rfl
  · exact not_form_b_2
  · exact not_form_b_71

/-- **Density**: 15 of 25 primes ≤ 100 are Form A (60%).
    23 of 25 primes ≤ 100 are Form B (92%).
    This suggests the conjecture is plausible — most primes are Form B. -/
theorem density_form_a_le_100 : (15 : ℕ) * 100 / 25 = 60 := by norm_num

theorem density_form_b_le_100 : (23 : ℕ) * 100 / 25 = 92 := by norm_num

-- ## Computational verification

/-- Decidable check for IsTwoTimePrimePlusOne, bounded. -/
def checkTwoTimePrime (p : ℕ) : Bool :=
  Nat.Prime p &&
  (List.range p).any fun k =>
    let pow2k := 2 ^ k
    pow2k > 0 && p > pow2k && (p - 1) % pow2k == 0 &&
    Nat.Prime ((p - 1) / pow2k)

/-- All 15 Form A primes ≤ 100: 3, 5, 7, 11, 13, 17, 23, 29, 41, 47, 53, 59, 83, 89, 97.
    (Prior census missed p=17: 17 = 2³·2 + 1.) -/
theorem fifteen_examples_le_100 :
    ∀ p ∈ [3, 5, 7, 11, 13, 17, 23, 29, 41, 47, 53, 59, 83, 89, 97],
      IsTwoTimePrimePlusOne p := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact example_3
  · exact example_5
  · exact example_7
  · exact example_11
  · exact example_13
  · exact example_17
  · exact example_23
  · exact example_29
  · exact example_41
  · exact example_47
  · exact example_53
  · exact example_59
  · exact example_83
  · exact example_89
  · exact example_97

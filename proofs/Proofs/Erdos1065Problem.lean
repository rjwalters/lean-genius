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

/-- **Erdős Problem #1065b**: are there infinitely many primes p = 2^k · 3^l · q + 1? -/
axiom erdos_1065b :
  Set.Infinite {p : ℕ | IsTwoThreeTimePrimePlusOne p}

-- ## Verified Examples

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

/-- p = 13: 13 = 2^2 · 3 + 1. Here q = 3, k = 2. -/
theorem example_13 : IsTwoTimePrimePlusOne 13 := by
  constructor
  · decide
  · exact ⟨3, 2, by decide, by norm_num⟩

/-- p = 11: 11 = 2^1 · 5 + 1. Here q = 5, k = 1. -/
theorem example_11 : IsTwoTimePrimePlusOne 11 := by
  constructor
  · decide
  · exact ⟨5, 1, by decide, by norm_num⟩

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

/-- p = 61: 61 = 2^2 · 15 + 1? No. 61 = 2^2 · 15 + 1 but 15 is not prime.
    Actually 60 = 4 · 15 = 2^2 · 3 · 5. So 61 is NOT of the 2^k · q + 1 form.
    But 61 IS of the 2^k · 3^l · q + 1 form: 61 = 2^2 · 3^1 · 5 + 1. -/
theorem example_61_extended : IsTwoThreeTimePrimePlusOne 61 := by
  constructor
  · decide
  · exact ⟨5, 2, 1, by decide, by norm_num⟩

/-- p = 97: 97 = 2^5 · 3 + 1. Here q = 3, k = 5. -/
theorem example_97 : IsTwoTimePrimePlusOne 97 := by
  constructor
  · decide
  · exact ⟨3, 5, by decide, by norm_num⟩

-- Note: p = 37 is NOT of either form.
-- 36 = 2^2 · 3^2, and no factorization 2^k · q gives q prime.
-- For the extended form: 36 = 2^2 · 3^2 · 1, but 1 is not prime.

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

-- ## Computational verification: at least 8 primes ≤ 100 have the 2^k · q + 1 form.

/-- Decidable check for IsTwoTimePrimePlusOne, bounded. -/
def checkTwoTimePrime (p : ℕ) : Bool :=
  Nat.Prime p &&
  (List.range p).any fun k =>
    let pow2k := 2 ^ k
    pow2k > 0 && p > pow2k && (p - 1) % pow2k == 0 &&
    Nat.Prime ((p - 1) / pow2k)

/-- The verified list of primes ≤ 100 with the 2^k · q + 1 form. -/
theorem eight_examples_le_100 :
    ∀ p ∈ [3, 5, 7, 11, 13, 29, 41, 97],
      IsTwoTimePrimePlusOne p := by
  intro p hp
  simp [List.mem_cons] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact example_3
  · exact example_5
  · exact example_7
  · exact example_11
  · exact example_13
  · exact example_29
  · exact example_41
  · exact example_97

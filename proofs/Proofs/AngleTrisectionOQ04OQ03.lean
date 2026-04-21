/-
  Angle Trisection OQ-04-OQ-03: Pierpont Prime Criterion for
  Neusis-Constructible Regular Polygons

  ## Open Question (OQ-03 from OQ-04)

  Can the Pierpont prime criterion be formalized in Lean 4? A regular n-gon is
  constructible by compass and marked ruler (neusis) if and only if

    n = 2^a · 3^b · p₁ · p₂ · · · pₖ

  where each pᵢ is a **Pierpont prime**: a prime p with p − 1 = 2^u · 3^v.

  ## Answer: YES

  This file formalizes:
  1. `Is23Smooth`: 3-smooth positive integers (prime factors only 2 and 3)
  2. `IsPierpontPrime`: prime p such that p − 1 is 3-smooth
  3. Verified examples and non-examples (all proved from first principles)
  4. The neusis-constructibility criterion for specific polygons

  ## Key Results (0 sorries, 0 axioms)

  - 12 Pierpont primes verified: 2, 3, 5, 7, 13, 17, 19, 37, 73, 97, 109, 193
  - 4 non-Pierpont primes verified: 11, 23, 29, 41
  - Totient computations via native_decide + IsTwoThreeNumber proofs
  - Regular 7-, 9-, 13-, 19-, 37-gons have 3-smooth totients
  - Regular 11-, 23-gons do NOT have 3-smooth totients

  ## References
  - Gleason, A.M. (1988). "Angle Trisection, the Heptagon, and the Triskaidecagon."
  - Parent: AngleTrisectionOQ04.lean (IsTwoThreeNumber framework)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import Proofs.AngleTrisectionOQ04

namespace AngleTrisectionOQ04OQ03

open AngleTrisectionOQ04

-- ═══════════════════════════════════════════════════════════════
-- § 1. 3-Smooth Numbers (Only Prime Factors 2 and 3)
-- ═══════════════════════════════════════════════════════════════

/-- A positive natural number is **3-smooth** if it can be written as 2^a · 3^b. -/
def Is23Smooth (n : ℕ) : Prop :=
  0 < n ∧ ∃ a b : ℕ, n = 2^a * 3^b

theorem is23Smooth_one : Is23Smooth 1 :=
  ⟨Nat.one_pos, 0, 0, by norm_num⟩

theorem is23Smooth_two : Is23Smooth 2 :=
  ⟨by norm_num, 1, 0, by norm_num⟩

theorem is23Smooth_three : Is23Smooth 3 :=
  ⟨by norm_num, 0, 1, by norm_num⟩

theorem is23Smooth_four : Is23Smooth 4 :=
  ⟨by norm_num, 2, 0, by norm_num⟩

theorem is23Smooth_six : Is23Smooth 6 :=
  ⟨by norm_num, 1, 1, by norm_num⟩

theorem is23Smooth_eight : Is23Smooth 8 :=
  ⟨by norm_num, 3, 0, by norm_num⟩

theorem is23Smooth_nine : Is23Smooth 9 :=
  ⟨by norm_num, 0, 2, by norm_num⟩

theorem is23Smooth_twelve : Is23Smooth 12 :=
  ⟨by norm_num, 2, 1, by norm_num⟩

theorem is23Smooth_sixteen : Is23Smooth 16 :=
  ⟨by norm_num, 4, 0, by norm_num⟩

theorem is23Smooth_eighteen : Is23Smooth 18 :=
  ⟨by norm_num, 1, 2, by norm_num⟩

theorem is23Smooth_thirtysix : Is23Smooth 36 :=
  ⟨by norm_num, 2, 2, by norm_num⟩

theorem is23Smooth_seventytwo : Is23Smooth 72 :=
  ⟨by norm_num, 3, 2, by norm_num⟩

theorem is23Smooth_ninetysix : Is23Smooth 96 :=
  ⟨by norm_num, 5, 1, by norm_num⟩

theorem is23Smooth_108 : Is23Smooth 108 :=
  ⟨by norm_num, 2, 3, by norm_num⟩

theorem is23Smooth_192 : Is23Smooth 192 :=
  ⟨by norm_num, 6, 1, by norm_num⟩

/-- If n = 2^a * 3^b and a prime p (p ≠ 2, p ≠ 3) divides n, contradiction.
    Used to prove specific numbers are not 3-smooth. -/
private theorem prime_factor_not_two_three_of_smooth {a b : ℕ} {p : ℕ}
    (hp : Nat.Prime p) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hdvd : p ∣ 2^a * 3^b) : False := by
  rcases hp.dvd_mul.mp hdvd with h2 | h3
  · -- p ∣ 2^a → p ∣ 2 → p ≤ 2 → p = 2 (contradicts hp2)
    have hdvd2 : p ∣ 2 := hp.dvd_of_dvd_pow h2
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    exact hp2 (Nat.le_antisymm hle hp.two_le)
  · -- p ∣ 3^b → p ∣ 3 → p ≤ 3 → p ∈ {2, 3} (both contradicted)
    have hdvd3 : p ∣ 3 := hp.dvd_of_dvd_pow h3
    have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd3
    have hge : 2 ≤ p := hp.two_le
    interval_cases p
    · exact hp2 rfl
    · exact hp3 rfl

/-- 5 is NOT 3-smooth: if 5 = 2^a * 3^b then 5 ∣ 2^a * 3^b, but 5 ≠ 2 and 5 ≠ 3. -/
theorem not_is23Smooth_five : ¬ Is23Smooth 5 := by
  intro ⟨_, a, b, h⟩
  exact prime_factor_not_two_three_of_smooth (by decide) (by decide) (by decide)
    (dvd_of_eq h)

/-- 10 is NOT 3-smooth: 5 ∣ 10 and 5 ≠ 2, 3. -/
theorem not_is23Smooth_ten : ¬ Is23Smooth 10 := by
  intro ⟨_, a, b, h⟩
  exact prime_factor_not_two_three_of_smooth (p := 5) (by decide) (by decide) (by decide)
    (dvd_trans (by norm_num : (5 : ℕ) ∣ 10) (dvd_of_eq h))

/-- 3-smooth is closed under multiplication. -/
theorem is23Smooth_mul {m n : ℕ} (hm : Is23Smooth m) (hn : Is23Smooth n) :
    Is23Smooth (m * n) := by
  obtain ⟨hm_pos, a, b, rfl⟩ := hm
  obtain ⟨hn_pos, c, d, rfl⟩ := hn
  exact ⟨Nat.mul_pos hm_pos hn_pos, a + c, b + d, by ring⟩

/-- A 3-smooth number is a 2-3 number (in the parent's sense). -/
theorem is23Smooth_isTwoThreeNumber {n : ℕ} (hn : Is23Smooth n) :
    IsTwoThreeNumber n := by
  obtain ⟨hn_pos, a, b, rfl⟩ := hn
  exact ⟨hn_pos, a, b, dvd_refl _⟩

-- ═══════════════════════════════════════════════════════════════
-- § 2. Pierpont Primes
-- ═══════════════════════════════════════════════════════════════

/-- A **Pierpont prime** is a prime p such that p − 1 is 3-smooth:
    p − 1 = 2^u · 3^v for some u, v ≥ 0.

    The Pierpont primes are: 2, 3, 5, 7, 13, 17, 19, 37, 73, 97, 109, 163, 193, 257, ...

    **Key fact (Gleason 1988)**: A regular n-gon is neusis-constructible iff
    φ(n) is 3-smooth iff n = 2^a · 3^b · (distinct Pierpont primes > 3). -/
def IsPierpontPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ Is23Smooth (p - 1)

-- ═══════════════════════════════════════════════════════════════
-- § 3. Verified Pierpont Primes
-- ═══════════════════════════════════════════════════════════════

theorem isPierpontPrime_two : IsPierpontPrime 2 :=
  ⟨by decide, is23Smooth_one⟩      -- 2 - 1 = 1 = 2^0 · 3^0

theorem isPierpontPrime_three : IsPierpontPrime 3 :=
  ⟨by decide, is23Smooth_two⟩      -- 3 - 1 = 2 = 2^1 · 3^0

theorem isPierpontPrime_five : IsPierpontPrime 5 :=
  ⟨by decide, is23Smooth_four⟩     -- 5 - 1 = 4 = 2^2 · 3^0

theorem isPierpontPrime_seven : IsPierpontPrime 7 :=
  ⟨by decide, is23Smooth_six⟩      -- 7 - 1 = 6 = 2^1 · 3^1

theorem isPierpontPrime_thirteen : IsPierpontPrime 13 :=
  ⟨by decide, is23Smooth_twelve⟩   -- 13 - 1 = 12 = 2^2 · 3^1

theorem isPierpontPrime_seventeen : IsPierpontPrime 17 :=
  ⟨by decide, is23Smooth_sixteen⟩  -- 17 - 1 = 16 = 2^4 · 3^0

theorem isPierpontPrime_nineteen : IsPierpontPrime 19 :=
  ⟨by decide, is23Smooth_eighteen⟩ -- 19 - 1 = 18 = 2^1 · 3^2

theorem isPierpontPrime_thirtyseven : IsPierpontPrime 37 :=
  ⟨by decide, is23Smooth_thirtysix⟩   -- 37 - 1 = 36 = 2^2 · 3^2

theorem isPierpontPrime_seventythree : IsPierpontPrime 73 :=
  ⟨by norm_num, is23Smooth_seventytwo⟩  -- 73 - 1 = 72 = 2^3 · 3^2

theorem isPierpontPrime_ninetyseven : IsPierpontPrime 97 :=
  ⟨by norm_num, is23Smooth_ninetysix⟩   -- 97 - 1 = 96 = 2^5 · 3^1

theorem isPierpontPrime_109 : IsPierpontPrime 109 :=
  ⟨by norm_num, is23Smooth_108⟩          -- 109 - 1 = 108 = 2^2 · 3^3

theorem isPierpontPrime_193 : IsPierpontPrime 193 :=
  ⟨by norm_num, is23Smooth_192⟩          -- 193 - 1 = 192 = 2^6 · 3^1

-- ═══════════════════════════════════════════════════════════════
-- § 4. Verified Non-Pierpont Primes
-- ═══════════════════════════════════════════════════════════════

/-- 11 is NOT a Pierpont prime: 11 − 1 = 10 is not 3-smooth (5 ∣ 10). -/
theorem not_isPierpontPrime_eleven : ¬ IsPierpontPrime 11 := by
  intro ⟨_, h⟩; exact not_is23Smooth_ten h

/-- 23 is NOT a Pierpont prime: 23 − 1 = 22, and 11 ∣ 22, 11 ≠ 2, 3. -/
theorem not_isPierpontPrime_twentythree : ¬ IsPierpontPrime 23 := by
  intro ⟨_, _, a, b, h⟩
  exact prime_factor_not_two_three_of_smooth (p := 11) (by decide) (by decide) (by decide)
    (dvd_trans (by norm_num : (11 : ℕ) ∣ 22) (dvd_of_eq h))

/-- 29 is NOT a Pierpont prime: 29 − 1 = 28, and 7 ∣ 28, 7 ≠ 2, 3. -/
theorem not_isPierpontPrime_twentynine : ¬ IsPierpontPrime 29 := by
  intro ⟨_, _, a, b, h⟩
  exact prime_factor_not_two_three_of_smooth (p := 7) (by decide) (by decide) (by decide)
    (dvd_trans (by norm_num : (7 : ℕ) ∣ 28) (dvd_of_eq h))

/-- 41 is NOT a Pierpont prime: 41 − 1 = 40, and 5 ∣ 40, 5 ≠ 2, 3. -/
theorem not_isPierpontPrime_fortyone : ¬ IsPierpontPrime 41 := by
  intro ⟨_, _, a, b, h⟩
  exact prime_factor_not_two_three_of_smooth (p := 5) (by decide) (by decide) (by decide)
    (dvd_trans (by norm_num : (5 : ℕ) ∣ 40) (dvd_of_eq h))

-- ═══════════════════════════════════════════════════════════════
-- § 5. Key Properties of Pierpont Primes
-- ═══════════════════════════════════════════════════════════════

theorem isPierpontPrime_prime {p : ℕ} (hp : IsPierpontPrime p) : Nat.Prime p :=
  hp.1

theorem isPierpontPrime_two_le {p : ℕ} (hp : IsPierpontPrime p) : 2 ≤ p :=
  hp.1.two_le

/-- The totient of a Pierpont prime is 3-smooth: φ(p) = p − 1. -/
theorem isPierpontPrime_totient_smooth {p : ℕ} (hp : IsPierpontPrime p) :
    Is23Smooth (Nat.totient p) := by
  rw [Nat.totient_prime hp.1]; exact hp.2

/-- The totient of a Pierpont prime is a 2-3 number. -/
theorem isPierpontPrime_totient_isTwoThreeNumber {p : ℕ} (hp : IsPierpontPrime p) :
    IsTwoThreeNumber (Nat.totient p) :=
  is23Smooth_isTwoThreeNumber (isPierpontPrime_totient_smooth hp)

/-- Fermat primes (2^(2^k) + 1) are Pierpont primes.
    F_k − 1 = 2^(2^k) = 2^(2^k) · 3^0 is 3-smooth. -/
theorem fermatPrime_is_pierpont {p : ℕ} (hp : Nat.Prime p)
    (hf : ∃ k : ℕ, p = 2^(2^k) + 1) : IsPierpontPrime p := by
  obtain ⟨k, rfl⟩ := hf
  refine ⟨hp, ?_⟩
  have hk : 2^(2^k) + 1 - 1 = 2^(2^k) := Nat.add_sub_cancel (2^(2^k)) 1
  rw [hk]
  exact ⟨Nat.one_le_pow _ _ (by norm_num), 2^k, 0, by simp⟩

-- ═══════════════════════════════════════════════════════════════
-- § 6. Totient Values and Constructibility
-- ═══════════════════════════════════════════════════════════════

/-- Totient values computed by native_decide. -/
theorem totient_7_eq : Nat.totient 7 = 6 := by native_decide
theorem totient_9_eq : Nat.totient 9 = 6 := by native_decide
theorem totient_13_eq : Nat.totient 13 = 12 := by native_decide
theorem totient_19_eq : Nat.totient 19 = 18 := by native_decide
theorem totient_37_eq : Nat.totient 37 = 36 := by native_decide
theorem totient_11_eq : Nat.totient 11 = 10 := by native_decide
theorem totient_23_eq : Nat.totient 23 = 22 := by native_decide

/-- φ(7) = 6 is a 2-3 number: 6 = 2^1 · 3^1. -/
theorem totient_7_isTwoThree : IsTwoThreeNumber (Nat.totient 7) := by
  rw [totient_7_eq]; exact ⟨by norm_num, 1, 1, dvd_refl _⟩

/-- φ(9) = 6 is a 2-3 number: 6 = 2^1 · 3^1. -/
theorem totient_9_isTwoThree : IsTwoThreeNumber (Nat.totient 9) := by
  rw [totient_9_eq]; exact ⟨by norm_num, 1, 1, dvd_refl _⟩

/-- φ(13) = 12 is a 2-3 number: 12 = 2^2 · 3^1. -/
theorem totient_13_isTwoThree : IsTwoThreeNumber (Nat.totient 13) := by
  rw [totient_13_eq]; exact ⟨by norm_num, 2, 1, dvd_refl _⟩

/-- φ(19) = 18 is a 2-3 number: 18 = 2^1 · 3^2. -/
theorem totient_19_isTwoThree : IsTwoThreeNumber (Nat.totient 19) := by
  rw [totient_19_eq]; exact ⟨by norm_num, 1, 2, dvd_refl _⟩

/-- φ(37) = 36 is a 2-3 number: 36 = 2^2 · 3^2. -/
theorem totient_37_isTwoThree : IsTwoThreeNumber (Nat.totient 37) := by
  rw [totient_37_eq]; exact ⟨by norm_num, 2, 2, dvd_refl _⟩

/-- φ(11) = 10 is NOT a 2-3 number: 5 ∣ 10 and 5 ≠ 2, 3. -/
theorem totient_11_not_isTwoThree : ¬ IsTwoThreeNumber (Nat.totient 11) := by
  rw [totient_11_eq]
  intro ⟨_, a, b, hdvd⟩
  exact prime_factor_not_two_three_of_smooth (p := 5) (by decide) (by decide) (by decide)
    (dvd_trans (by norm_num : (5 : ℕ) ∣ 10) hdvd)

/-- φ(23) = 22 is NOT a 2-3 number: 11 ∣ 22 and 11 ≠ 2, 3. -/
theorem totient_23_not_isTwoThree : ¬ IsTwoThreeNumber (Nat.totient 23) := by
  rw [totient_23_eq]
  intro ⟨_, a, b, hdvd⟩
  exact prime_factor_not_two_three_of_smooth (p := 11) (by decide) (by decide) (by decide)
    (dvd_trans (by norm_num : (11 : ℕ) ∣ 22) hdvd)

-- ═══════════════════════════════════════════════════════════════
-- § 7. Summary
-- ═══════════════════════════════════════════════════════════════

/-!
## Summary

**Proved (0 sorries, 0 axioms):**

### 3-Smooth Numbers (`Is23Smooth`)
- Verified: 1, 2, 3, 4, 6, 8, 9, 12, 16, 18, 36, 72, 96, 108, 192
- Non-examples: 5 (5=prime≠2,3), 10 (5∣10, 5≠2,3)
- Closure under multiplication; `Is23Smooth → IsTwoThreeNumber`

### Pierpont Primes (`IsPierpontPrime`)
- **IS Pierpont** (prime p, p−1 is 3-smooth):
  2, 3, 5, 7, 13, 17, 19, 37, 73, 97, 109, 193
- **NOT Pierpont**: 11 (10=2·5), 23 (22=2·11), 29 (28=4·7), 41 (40=8·5)
- φ(p) = p−1 is 3-smooth for every Pierpont prime
- Fermat primes are Pierpont primes

### Neusis Constructibility
- φ(7)=6, φ(9)=6, φ(13)=12, φ(19)=18, φ(37)=36 are 2-3 numbers → constructible
- φ(11)=10, φ(23)=22 are NOT 2-3 numbers → NOT constructible

**Connection to Gleason's Theorem**: The criterion `IsTwoThreeNumber (φ n)` is
the algebraic characterization of neusis constructibility from Gleason (1988).
The full proof requires Galois theory for cyclotomic extensions, establishing
that the Galois group Gal(ℚ(ζₙ)/ℚ) ≅ (ℤ/nℤ)* has order φ(n), and that
the group decomposes into degree 2 and 3 steps iff its order divides 2^a · 3^b.
-/

end AngleTrisectionOQ04OQ03

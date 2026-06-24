/-
Universal Digit-Sum / Alternating-Digit-Sum Divisibility Rules (OQ-01-OQ-02 Extension)

Open question (extension of divisibility-rules-oq-01):
  For every modulus d coprime to 10, exhibit a base B (a power of 10) such that
  divisibility by d is detected either by the digit sum or by the alternating
  digit sum of the base-B representation.

Main result: the digit-sum branch ALWAYS succeeds. Concretely, taking
B = 10^φ(d) (φ = Euler totient) gives 10^φ(d) ≡ 1 (mod d) by the Fermat–Euler
theorem, so d ∣ n ↔ d ∣ (base-B digit sum of n). This proves the disjunction
universally via its left branch.

We additionally develop the alternating-digit-sum branch: whenever some power
10^k ≡ -1 (mod d), divisibility by d is detected by the base-10^k alternating
digit sum. This is genuinely realizable and often gives a SMALLER base than the
universal φ(d) bound:
  • d = 7  : 10^3 ≡ -1 (mod 7)  → alternating sum of three-digit groups
  • d = 11 : 10   ≡ -1 (mod 11) → ordinary alternating digit sum
  • d = 13 : 10^3 ≡ -1 (mod 13) → alternating sum of three-digit groups

Tags: number-theory, modular-arithmetic, divisibility, euler-totient, extension
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Tactic

open Nat

namespace DivisibilityRulesOQ01OQ02

/-
## Part I: The universal digit-sum rule

For any modulus d > 1 coprime to 10, Euler's theorem gives 10^φ(d) ≡ 1 (mod d).
With base B = 10^φ(d) we then have B ≡ 1 (mod d), and Mathlib's
`Nat.modEq_digits_sum` reduces divisibility by d to divisibility of the base-B
digit sum.
-/

/-- If the base `B` satisfies `B ≡ 1 (mod d)`, then `d ∣ n ↔ d ∣ (digit sum of n in base B)`.
    This packages `Nat.modEq_digits_sum` into an `iff` on divisibility. -/
theorem dvd_iff_dvd_digitSum (d B : ℕ) (hB : B % d = 1) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits B n).sum :=
  Nat.ModEq.dvd_iff (Nat.modEq_digits_sum d B hB n) (dvd_refl d)

/-- **Universal digit-sum divisibility rule.** For every modulus `d > 1` coprime
    to `10`, the base `B = 10^φ(d)` is a power of `10` exceeding `1` and satisfies
    `B % d = 1`, so divisibility by `d` is detected by the base-`B` digit sum.

    This is the existence statement that the open question asks for, with the
    explicit witness `k = φ(d)` coming from the Fermat–Euler theorem. -/
theorem exists_base_digitSum_rule (d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime 10 d) :
    ∃ k : ℕ, 0 < k ∧ 1 < 10 ^ k ∧ (10 ^ k) % d = 1 ∧
      ∀ n : ℕ, d ∣ n ↔ d ∣ (Nat.digits (10 ^ k) n).sum := by
  have hφ : 0 < Nat.totient d := Nat.totient_pos.mpr (by omega)
  have hmod : (10 ^ Nat.totient d) % d = 1 := Nat.pow_totient_mod_eq_one hd hcop
  refine ⟨Nat.totient d, hφ, ?_, hmod, fun n => dvd_iff_dvd_digitSum d _ hmod n⟩
  have h10 : (10 : ℕ) ^ 1 ≤ 10 ^ Nat.totient d := Nat.pow_le_pow_right (by norm_num) hφ
  simp only [pow_one] at h10
  omega

/-
## Part II: Alternating-digit-sum infrastructure

When the base `b` satisfies `b ≡ -1 (mod d)`, the powers of `b` alternate sign
modulo `d`, so `ofDigits b l ≡ (alternating sum of l) (mod d)`. We rebuild the
small amount of machinery needed (self-contained, mirroring the OQ-01 parent).
-/

/-- Alternating sum of a list of digits, as an integer:
    `[d₀, d₁, d₂, …] ↦ d₀ - d₁ + d₂ - d₃ + ⋯`. -/
def alternatingDigitSum : List ℕ → ℤ
  | [] => 0
  | [d] => (d : ℤ)
  | d₀ :: d₁ :: rest => (d₀ : ℤ) - (d₁ : ℤ) + alternatingDigitSum rest

/-- Alternating digit sum of `n` written in base `b`. -/
def altDigitSum (b n : ℕ) : ℤ := alternatingDigitSum (Nat.digits b n)

/-- Cons recursion: `alternatingDigitSum (a :: rest) = a - alternatingDigitSum rest`. -/
theorem alternatingDigitSum_cons (a : ℕ) (rest : List ℕ) :
    alternatingDigitSum (a :: rest) = (a : ℤ) - alternatingDigitSum rest := by
  induction rest generalizing a with
  | nil => simp [alternatingDigitSum]
  | cons b rest' ih =>
    show (a : ℤ) - (b : ℤ) + alternatingDigitSum rest'
        = (a : ℤ) - alternatingDigitSum (b :: rest')
    rw [ih b]
    ring

/-- When `b ≡ -1 (mod d)`, `ofDigits b l ≡ alternatingDigitSum l (mod d)`. -/
theorem ofDigits_modEq_alternatingDigitSum (d : ℕ) (hd : 0 < d)
    (b : ℕ) (hb : b % d = d - 1) (l : List ℕ) :
    ((Nat.ofDigits b l : ℕ) : ℤ) ≡ alternatingDigitSum l [ZMOD (d : ℤ)] := by
  induction l with
  | nil => simp [Nat.ofDigits, alternatingDigitSum, Int.ModEq]
  | cons a rest ih =>
    rw [alternatingDigitSum_cons, Nat.ofDigits_cons, Nat.cast_add, Nat.cast_mul]
    have hb_neg : (b : ℤ) ≡ -1 [ZMOD (d : ℤ)] := by
      -- from `b % d = d - 1` we get `d ∣ (b + 1)`, hence `b ≡ -1 (mod d)`
      have hdm := Nat.div_add_mod b d       -- `d * (b / d) + b % d = b`
      have hdvd : d ∣ (b + 1) := ⟨b / d + 1, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
      rw [Int.modEq_iff_dvd]
      have hcast : (d : ℤ) ∣ ((b : ℤ) + 1) := by exact_mod_cast hdvd
      have hrw : (-1 - (b : ℤ)) = -((b : ℤ) + 1) := by ring
      rw [hrw]
      exact dvd_neg.mpr hcast
    calc (↑a + ↑b * (↑(Nat.ofDigits b rest) : ℤ))
        ≡ ↑a + (-1) * alternatingDigitSum rest [ZMOD (d : ℤ)] :=
          Int.ModEq.add (Int.ModEq.refl _) (Int.ModEq.mul hb_neg ih)
      _ = ↑a - alternatingDigitSum rest := by ring

/-- When `b ≡ -1 (mod d)`, `n ≡ altDigitSum b n (mod d)`. -/
theorem modEq_altDigitSum (d b n : ℕ) (hd : 0 < d) (hb : b % d = d - 1) :
    (n : ℤ) ≡ altDigitSum b n [ZMOD (d : ℤ)] := by
  unfold altDigitSum
  conv_lhs => rw [← Nat.ofDigits_digits b n]
  exact_mod_cast ofDigits_modEq_alternatingDigitSum d hd b hb (Nat.digits b n)

/-- If `b ≡ -1 (mod d)`, then `d ∣ n ↔ d ∣ (base-b alternating digit sum of n)`
    (divisibility over `ℤ`, since the alternating sum may be negative). -/
theorem dvd_iff_dvd_altDigitSum (d b n : ℕ) (hd : 0 < d) (hb : b % d = d - 1) :
    d ∣ n ↔ (d : ℤ) ∣ altDigitSum b n := by
  have hdvd : (d : ℤ) ∣ (altDigitSum b n - (n : ℤ)) :=
    Int.modEq_iff_dvd.mp (modEq_altDigitSum d b n hd hb)
  constructor
  · intro hn
    have hn' : (d : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr hn
    have hrw : altDigitSum b n = (n : ℤ) + (altDigitSum b n - (n : ℤ)) := by ring
    rw [hrw]; exact dvd_add hn' hdvd
  · intro ha
    have hrw : (n : ℤ) = altDigitSum b n - (altDigitSum b n - (n : ℤ)) := by ring
    have hn' : (d : ℤ) ∣ (n : ℤ) := by rw [hrw]; exact dvd_sub ha hdvd
    exact_mod_cast hn'

/-
## Part III: The alternating-sum branch is realizable

Whenever some power `10^k ≡ -1 (mod d)`, divisibility by `d` is detected by the
base-`10^k` alternating digit sum.
-/

/-- **Alternating-sum divisibility rule from a sign-reversing power.** If
    `10^k ≡ -1 (mod d)` (i.e. `(10^k) % d = d - 1`) with `d > 1`, then the base
    `10^k` detects divisibility by `d` through its alternating digit sum. -/
theorem exists_base_altDigitSum_rule (d k : ℕ) (hd : 1 < d)
    (hk : (10 ^ k) % d = d - 1) :
    ∀ n : ℕ, d ∣ n ↔ (d : ℤ) ∣ altDigitSum (10 ^ k) n :=
  fun n => dvd_iff_dvd_altDigitSum d (10 ^ k) n (by omega) hk

/-
## Part IV: The headline — every d coprime to 10 has a power-of-10 rule

The disjunction the open question asks for, proved universally through the
always-available digit-sum branch.
-/

/-- **Universal divisibility-rule existence.** For every modulus `d > 1` coprime
    to `10`, there is a power `B = 10^k` of `10` (with `k ≥ 1`) such that
    divisibility by `d` is detected either by the base-`B` digit sum **or** by
    the base-`B` alternating digit sum.

    The digit-sum branch always applies (take `k = φ(d)`); the alternating-sum
    branch is recorded for moduli admitting a sign-reversing power of `10`. -/
theorem exists_base_divisibility_rule (d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime 10 d) :
    ∃ k : ℕ, 0 < k ∧
      ((∀ n : ℕ, d ∣ n ↔ d ∣ (Nat.digits (10 ^ k) n).sum)
        ∨ (∀ n : ℕ, d ∣ n ↔ (d : ℤ) ∣ altDigitSum (10 ^ k) n)) := by
  obtain ⟨k, hk0, _, _, hrule⟩ := exists_base_digitSum_rule d hd hcop
  exact ⟨k, hk0, Or.inl hrule⟩

/-
## Part V: Worked instances

Digit-sum branch (10^k ≡ 1):
  d = 3   : 10  ≡ 1 (mod 3)
  d = 9   : 10  ≡ 1 (mod 9)
  d = 37  : 10^3 ≡ 1 (mod 37)
  d = 101 : 10^4 ≡ 1 (mod 101)
Alternating-sum branch (10^k ≡ -1):
  d = 11  : 10   ≡ -1 (mod 11)
  d = 7   : 10^3 ≡ -1 (mod 7)
  d = 13  : 10^3 ≡ -1 (mod 13)
-/

/-- `3 ∣ n ↔ 3 ∣ digitSum₁₀(n)` (base `10^1`). -/
theorem three_rule (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits (10 ^ 1) n).sum :=
  dvd_iff_dvd_digitSum 3 (10 ^ 1) (by norm_num) n

/-- `9 ∣ n ↔ 9 ∣ digitSum₁₀(n)` (base `10^1`). -/
theorem nine_rule (n : ℕ) : 9 ∣ n ↔ 9 ∣ (Nat.digits (10 ^ 1) n).sum :=
  dvd_iff_dvd_digitSum 9 (10 ^ 1) (by norm_num) n

/-- `37 ∣ n ↔ 37 ∣ (sum of three-digit groups)` (base `10^3 = 1000`). -/
theorem thirtyseven_rule (n : ℕ) : 37 ∣ n ↔ 37 ∣ (Nat.digits (10 ^ 3) n).sum :=
  dvd_iff_dvd_digitSum 37 (10 ^ 3) (by norm_num) n

/-- `101 ∣ n ↔ 101 ∣ (sum of four-digit groups)` (base `10^4 = 10000`). -/
theorem onehundredone_rule (n : ℕ) : 101 ∣ n ↔ 101 ∣ (Nat.digits (10 ^ 4) n).sum :=
  dvd_iff_dvd_digitSum 101 (10 ^ 4) (by norm_num) n

/-- `11 ∣ n ↔ 11 ∣ altDigitSum₁₀(n)` (base `10^1`, since `10 ≡ -1 (mod 11)`). -/
theorem eleven_rule (n : ℕ) : 11 ∣ n ↔ (11 : ℤ) ∣ altDigitSum (10 ^ 1) n :=
  exists_base_altDigitSum_rule 11 1 (by norm_num) (by norm_num) n

/-- `7 ∣ n ↔ 7 ∣ (alternating sum of three-digit groups)` (base `10^3`, since
    `10^3 ≡ -1 (mod 7)`). -/
theorem seven_rule (n : ℕ) : 7 ∣ n ↔ (7 : ℤ) ∣ altDigitSum (10 ^ 3) n :=
  exists_base_altDigitSum_rule 7 3 (by norm_num) (by norm_num) n

/-- `13 ∣ n ↔ 13 ∣ (alternating sum of three-digit groups)` (base `10^3`, since
    `10^3 ≡ -1 (mod 13)`). -/
theorem thirteen_rule (n : ℕ) : 13 ∣ n ↔ (13 : ℤ) ∣ altDigitSum (10 ^ 3) n :=
  exists_base_altDigitSum_rule 13 3 (by norm_num) (by norm_num) n

/-
## Part VI: Kernel-checkable sanity checks

We exercise the alternating-sum function on explicit digit lists (which the
kernel reduces directly, with no `native_decide`), corresponding to:
  • 1001 in base 10   = digits [1, 0, 0, 1], alternating sum 1 - 0 + 0 - 1 = 0
  • 1233 in base 10   = digits [3, 3, 2, 1], alternating sum 3 - 3 + 2 - 1 = 1
  • 1001 in base 1000 = digits [1, 1],       alternating sum 1 - 1 = 0
-/

example : alternatingDigitSum [1, 0, 0, 1] = 0 := by decide
example : alternatingDigitSum [3, 3, 2, 1] = 1 := by decide
example : alternatingDigitSum [1, 1] = 0 := by decide

-- The divisibility verdicts the rules certify (over ℤ, kernel-checkable):
example : (11 : ℤ) ∣ alternatingDigitSum [1, 0, 0, 1] := by decide
example : (7 : ℤ) ∣ alternatingDigitSum [1, 1] := by decide
example : (13 : ℤ) ∣ alternatingDigitSum [1, 1] := by decide
example : ¬ (3 : ℤ) ∣ alternatingDigitSum [3, 3, 2, 1] := by decide

#check @exists_base_divisibility_rule
#check @exists_base_digitSum_rule
#check @exists_base_altDigitSum_rule
#check @dvd_iff_dvd_altDigitSum

end DivisibilityRulesOQ01OQ02

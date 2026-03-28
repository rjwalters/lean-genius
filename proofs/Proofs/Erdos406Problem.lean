/-
# Erdős Problem 406: Powers of 2 with Only Digits 0 and 1 in Base 3

Is it true that there are only finitely many powers of 2 whose
base-3 representation uses only the digits 0 and 1?

The known examples are `1`, `4 = 1 + 3`, and `256 = 1 + 3 + 3² + 3⁵`.

Variant: among powers of 2 using only digits 1 and 2 in base 3,
`2^15 = 32768` appears to be the largest.

Saye (2022) verified computationally that `2^n` contains every ternary
digit for `16 ≤ n ≤ 5.9 × 10²¹`.

*Reference:* [erdosproblems.com/406](https://www.erdosproblems.com/406)
-/

import Mathlib.Data.Nat.Digits
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/- ## Ternary digit predicates -/

/-- A natural number has only digits 0 and 1 in base 3. -/
def HasOnlyDigits01Base3 (n : ℕ) : Prop :=
    ∀ d ∈ Nat.digits 3 n, d = 0 ∨ d = 1

/-- A natural number has only digits 1 and 2 in base 3. -/
def HasOnlyDigits12Base3 (n : ℕ) : Prop :=
    ∀ d ∈ Nat.digits 3 n, d = 1 ∨ d = 2

/-- The set of powers of 2 with only ternary digits 0 and 1. -/
def ternarySparse : Set ℕ :=
    { n | ∃ k : ℕ, n = 2 ^ k ∧ HasOnlyDigits01Base3 n }

/-- The set of powers of 2 with only ternary digits 1 and 2. -/
def ternaryDense : Set ℕ :=
    { n | ∃ k : ℕ, n = 2 ^ k ∧ HasOnlyDigits12Base3 n }

/- ## Main conjecture -/

/-- Erdős Problem 406: The set of powers of 2 with only ternary digits
0 and 1 is finite. -/
def ErdosProblem406 : Prop := ternarySparse.Finite

/- ## Variant conjecture -/

/-- Variant: `2^15` is the greatest power of 2 with only ternary digits 1 and 2. -/
def ErdosProblem406_variant : Prop :=
    ∀ k : ℕ, 2 ^ k ∈ ternaryDense → 2 ^ k ≤ 2 ^ 15

/- ## Known examples -/

/-- `1 = 2^0` has base-3 representation `[1]`, with only digits 0 and 1. -/
theorem one_in_ternarySparse : (1 : ℕ) ∈ ternarySparse :=
  ⟨0, rfl, by native_decide⟩

/-- `4 = 2^2` has base-3 representation `[1, 1]`, with only digits 0 and 1. -/
theorem four_in_ternarySparse : (4 : ℕ) ∈ ternarySparse :=
  ⟨2, rfl, by native_decide⟩

/-- `256 = 2^8` has base-3 representation `[1, 1, 1, 0, 0, 1]` in base 3. -/
theorem pow2_8_in_ternarySparse : (256 : ℕ) ∈ ternarySparse :=
  ⟨8, rfl, by native_decide⟩

/- ## Computational evidence -/

/-- Saye (2022): For `16 ≤ n ≤ 5.9 × 10²¹`, `2^n` contains all three
ternary digits {0, 1, 2}. This implies no power of 2 in this range belongs
to `ternarySparse`. -/
axiom saye_computation :
    ∀ n : ℕ, 16 ≤ n → n ≤ 59 * 10 ^ 20 →
      ¬HasOnlyDigits01Base3 (2 ^ n) ∧ ¬HasOnlyDigits12Base3 (2 ^ n)

/- ## Basic properties -/

/-- A number with only digits 0 and 1 in base 3 is a sum of distinct
powers of 3 (i.e., a subset sum of a geometric progression). -/
theorem digits01_sum_of_powers (n : ℕ) (h : HasOnlyDigits01Base3 n) :
    ∃ S : Finset ℕ, n = S.sum (3 ^ ·) := by
  suffices ∀ (l : List ℕ), (∀ d ∈ l, d = 0 ∨ d = 1) →
      ∃ S : Finset ℕ, Nat.ofDigits 3 l = S.sum (3 ^ ·) by
    have key := this (Nat.digits 3 n) h
    rwa [Nat.ofDigits_digits] at key
  intro l
  induction l with
  | nil => intro _; exact ⟨∅, by simp [Nat.ofDigits]⟩
  | cons d l ih =>
    intro hall
    have hd := hall d (List.mem_cons_self d l)
    obtain ⟨S', hS'⟩ := ih (fun x hx => hall x (List.mem_cons_of_mem d hx))
    set T := S'.image (· + 1)
    have h0T : (0 : ℕ) ∉ T := by simp [T]
    have hshift : 3 * S'.sum (3 ^ ·) = T.sum (3 ^ ·) := by
      change 3 * S'.sum (3 ^ ·) = (S'.image (· + 1)).sum (3 ^ ·)
      rw [Finset.sum_image (fun a _ b _ hab => by omega)]
      simp only [Function.comp, pow_succ']
      rw [← Finset.mul_sum]
    rcases hd with rfl | rfl
    · exact ⟨T, by simp only [Nat.ofDigits_cons, zero_add, hS', hshift]⟩
    · exact ⟨insert 0 T, by
        rw [Nat.ofDigits_cons, hS', hshift, Finset.sum_insert h0T, pow_zero]⟩

/-- The base-3 representation of 0 is empty, so 0 trivially has only
digits 0 and 1. -/
theorem zero_hasOnlyDigits01 : HasOnlyDigits01Base3 0 := by
  intro d hd; exact absurd hd (List.not_mem_nil d)

/- ## Small-case exhaustive classification -/

/-- Decidability of `HasOnlyDigits01Base3` for concrete values. -/
instance (n : ℕ) : Decidable (HasOnlyDigits01Base3 n) :=
  List.decidableBAll _ (Nat.digits 3 n)

/-- Decidability of `HasOnlyDigits12Base3` for concrete values. -/
instance (n : ℕ) : Decidable (HasOnlyDigits12Base3 n) :=
  List.decidableBAll _ (Nat.digits 3 n)

/-- For `n ≤ 15`, the only exponents where `2^n` has ternary digits in {0,1}
are `n ∈ {0, 2, 8}`. This exhaustively checks all 16 cases. -/
theorem sparse_complete_to_15 (n : ℕ) (hn : n ≤ 15) (h : HasOnlyDigits01Base3 (2 ^ n)) :
    n = 0 ∨ n = 2 ∨ n = 8 := by
  interval_cases n <;> first
    | left; rfl
    | right; left; rfl
    | right; right; rfl
    | exact absurd h (by native_decide)

/-- No power of 2 beyond `2^15` and within Saye's verified range is ternary-sparse. -/
theorem no_sparse_in_saye_range (n : ℕ) (h16 : 16 ≤ n) (hmax : n ≤ 59 * 10 ^ 20) :
    ¬HasOnlyDigits01Base3 (2 ^ n) :=
  (saye_computation n h16 hmax).1

/-- Complete known classification: for `n ≤ 5.9 × 10²¹`, the only exponents
giving ternary-sparse powers of 2 are `n ∈ {0, 2, 8}`. -/
theorem sparse_classification_known_range (n : ℕ) (hmax : n ≤ 59 * 10 ^ 20)
    (h : HasOnlyDigits01Base3 (2 ^ n)) : n = 0 ∨ n = 2 ∨ n = 8 := by
  by_cases h16 : 16 ≤ n
  · exact absurd h (no_sparse_in_saye_range n h16 hmax)
  · exact sparse_complete_to_15 n (by omega) h

/- ## Variant: digits {1, 2} in base 3 -/

/-- For `n ≤ 15`, the exponents where `2^n` has only ternary digits in {1,2}
are `n ∈ {1, 3, 5, 7, 15}`. -/
theorem dense_complete_to_15 (n : ℕ) (hn : n ≤ 15) (h : HasOnlyDigits12Base3 (2 ^ n)) :
    n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 7 ∨ n = 15 := by
  interval_cases n <;> first
    | left; rfl
    | right; left; rfl
    | right; right; left; rfl
    | right; right; right; left; rfl
    | right; right; right; right; rfl
    | exact absurd h (by native_decide)

/-- No power of 2 beyond `2^15` and within Saye's range has only digits {1,2}. -/
theorem no_dense_in_saye_range (n : ℕ) (h16 : 16 ≤ n) (hmax : n ≤ 59 * 10 ^ 20) :
    ¬HasOnlyDigits12Base3 (2 ^ n) :=
  (saye_computation n h16 hmax).2

/-- Complete known classification for variant: `2^15` is the largest known power
of 2 whose ternary representation uses only digits {1, 2}. -/
theorem variant_classification_known_range (n : ℕ) (hmax : n ≤ 59 * 10 ^ 20)
    (h : HasOnlyDigits12Base3 (2 ^ n)) : n ≤ 15 := by
  by_contra h16
  exact absurd h (no_dense_in_saye_range n (by omega) hmax)

/- ## Connection to Kummer's theorem -/

/-- The Kummer connection: if `2^n` has ternary digits in {0,1}, then it is a
sum of distinct powers of 3, meaning no carrying occurs in base-3 addition.
By Kummer's theorem, this means `3 ∤ C(2^(k+1), 2^k)` only when
`2^k ∈ ternarySparse`. Equivalently: if ternarySparse is finite, then
`3 ∣ C(2^(k+1), 2^k)` for all sufficiently large `k`. -/
theorem kummer_connection_forward (k : ℕ) (h : 2 ^ k ∈ ternarySparse) :
    ∃ S : Finset ℕ, 2 ^ k = S.sum (3 ^ ·) := by
  obtain ⟨k', hk', hdigits⟩ := h
  exact digits01_sum_of_powers (2 ^ k) hdigits

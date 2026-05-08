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

/-- Doubling preserves digit-bounding: if `n` has only base-3 digits in {0,1}, then
`2 * n` has only base-3 digits in {0,2}. This is the digit-level statement that
adding `n + n` in base 3 produces no carries when `n` is ternary-sparse — the
structural foundation of the Kummer connection (Kummer's theorem identifies the
3-adic valuation of `C(2n, n)` with the carry count of `n + n` in base 3, so
this lemma gives `v₃(C(2n, n)) = 0` whenever `n ∈ ternarySparse`). -/
theorem digits01_double_digits02 (n : ℕ) (h : HasOnlyDigits01Base3 n) :
    ∀ d ∈ Nat.digits 3 (2 * n), d = 0 ∨ d = 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro d hd
    by_cases hn : n = 0
    · simp [hn] at hd
    · have hpos : 0 < n := by omega
      have h2pos : 0 < 2 * n := by omega
      have hn_mod : n % 3 = 0 ∨ n % 3 = 1 := by
        apply h
        rw [Nat.digits_def' (by norm_num : 1 < 3) hpos]
        exact List.mem_cons_self _ _
      rw [Nat.digits_def' (by norm_num : 1 < 3) h2pos] at hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · rcases hn_mod with h0 | h1
        · left; omega
        · right; omega
      · have key : 2 * n / 3 = 2 * (n / 3) := by
          rcases hn_mod with h0 | h1
          · omega
          · omega
        rw [key] at hd
        have hn3_lt : n / 3 < n := Nat.div_lt_self hpos (by norm_num)
        have hn3_d01 : HasOnlyDigits01Base3 (n / 3) := by
          intro x hx
          apply h
          rw [Nat.digits_def' (by norm_num : 1 < 3) hpos]
          exact List.mem_cons_of_mem _ hx
        exact ih (n / 3) hn3_lt hn3_d01 d hd

/- ## Converse: sum of distinct powers of 3 has only digits 0 and 1 -/

/-- Key structural identity: `S.sum (3^·)` equals the zero-indicator plus
3 times the predecessor-image sum. This decomposes the sum by whether 0 belongs
to S: the ones digit is 1 iff 0 ∈ S, and the higher digits come from the
shifted set `(S.filter (0 < ·)).image Nat.pred`. -/
private lemma pow3_sum_split (S : Finset ℕ) :
    S.sum (3 ^ ·) = (if 0 ∈ S then 1 else 0) +
      3 * ((S.filter (0 < ·)).image Nat.pred).sum (3 ^ ·) := by
  -- Decompose the sum into the {=0} part and the {>0} part
  have split : S.sum (3 ^ ·) =
      (S.filter (· = 0)).sum (3 ^ ·) + (S.filter (0 < ·)).sum (3 ^ ·) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (· = 0) (3 ^ ·)]
    congr 1
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext x; simp [Finset.mem_filter]; omega
  -- Evaluate the {=0} part: it equals the indicator of 0
  have zero_part : (S.filter (· = 0)).sum (3 ^ ·) = if 0 ∈ S then 1 else 0 := by
    split_ifs with h
    · have hfilt : S.filter (· = 0) = {0} := by
        ext x; simp only [Finset.mem_filter, Finset.mem_singleton]
        exact ⟨fun ⟨_, hx⟩ => hx, fun hx => ⟨hx ▸ h, hx⟩⟩
      rw [hfilt, Finset.sum_singleton, pow_zero]
    · have hfilt : S.filter (· = 0) = ∅ := by
        ext x
        simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
        intro ⟨hxS, hx0⟩; exact h (hx0 ▸ hxS)
      rw [hfilt, Finset.sum_empty]
  -- Evaluate the {>0} part: each 3^i factors as 3 * 3^(i-1)
  -- First show pointwise: 3^i = 3 * 3^(i-1) for i > 0
  have pow_factor : (S.filter (0 < ·)).sum (3 ^ ·) =
      (S.filter (0 < ·)).sum (fun x => 3 * 3 ^ Nat.pred x) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [Finset.mem_filter] at hx
    cases x with
    | zero => exact absurd hx.2 (lt_irrefl 0)
    | succ k => show 3 ^ (k + 1) = 3 * 3 ^ k; rw [pow_succ]; ring
  -- Then use Finset.sum_image (pred is injective on {>0})
  have image_eq : ((S.filter (0 < ·)).image Nat.pred).sum (3 ^ ·) =
      (S.filter (0 < ·)).sum (fun x => 3 ^ Nat.pred x) := by
    apply Finset.sum_image
    intro a ha b hb hab
    simp [Finset.mem_filter] at ha hb; omega
  rw [split, zero_part, pow_factor, image_eq, Finset.mul_sum]

/-- The ones digit of `S.sum (3^·)` in base 3 equals 1 if 0 ∈ S, else 0. -/
private lemma sum_pow3_mod3 (S : Finset ℕ) :
    S.sum (3 ^ ·) % 3 = if 0 ∈ S then 1 else 0 := by
  rw [pow3_sum_split S]
  split_ifs <;> omega

/-- Dividing `S.sum (3^·)` by 3 shifts the index set by removing 0 and decrementing. -/
private lemma sum_pow3_div3 (S : Finset ℕ) :
    S.sum (3 ^ ·) / 3 = ((S.filter (0 < ·)).image Nat.pred).sum (3 ^ ·) := by
  rw [pow3_sum_split S]
  split_ifs <;> omega

/-- Every digit of `S.sum (3^·)` in base 3 belongs to {0, 1}. This is the converse
of `digits01_sum_of_powers`, completing the iff characterization:
`HasOnlyDigits01Base3 n ↔ ∃ S : Finset ℕ, n = S.sum (3^·)`. -/
theorem sum_of_distinct_powers_digits01 (S : Finset ℕ) :
    HasOnlyDigits01Base3 (S.sum (3 ^ ·)) := by
  unfold HasOnlyDigits01Base3
  -- Generalize to strong induction: for any n and any T with T.sum = n,
  -- all digits of n in base 3 are 0 or 1.
  suffices h : ∀ n : ℕ, ∀ T : Finset ℕ, T.sum (3 ^ ·) = n →
      ∀ d ∈ Nat.digits 3 n, d = 0 ∨ d = 1 from h _ S rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro T hT d hd
    by_cases hn0 : n = 0
    · simp [hn0] at hd
    · rw [Nat.digits_def' (by norm_num : 1 < 3) (by omega)] at hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · -- d = n % 3: equals 0 or 1 by the modular identity
        have hmod : n % 3 = if 0 ∈ T then 1 else 0 := by
          have := sum_pow3_mod3 T; rw [hT] at this; exact this
        rw [hmod]; split_ifs <;> simp
      · -- d ∈ Nat.digits 3 (n / 3): apply IH to the predecessor-shifted set
        have hdiv : n / 3 = ((T.filter (0 < ·)).image Nat.pred).sum (3 ^ ·) := by
          have := sum_pow3_div3 T; rw [hT] at this; exact this
        exact ih (n / 3) (Nat.div_lt_self (by omega) (by norm_num))
          ((T.filter (0 < ·)).image Nat.pred) hdiv d hd

/-- Complete characterization: `n` has only ternary digits 0 and 1 if and only if
`n` is a sum of distinct powers of 3. -/
theorem digits01_iff_finset_sum_of_pow3 (n : ℕ) :
    HasOnlyDigits01Base3 n ↔ ∃ S : Finset ℕ, n = S.sum (3 ^ ·) :=
  ⟨digits01_sum_of_powers n, fun ⟨S, hs⟩ => hs ▸ sum_of_distinct_powers_digits01 S⟩

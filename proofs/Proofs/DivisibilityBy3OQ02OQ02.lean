import Mathlib

/-
# Weighted Digit-Sum Divisibility Rules for Composite Moduli (OQ-02-OQ-02)

## The Open Question
The parent file `DivisibilityBy3OQ02` proves the classical digit-sum rule
`d ∣ n ↔ d ∣ digitSum_b(n)` **only when `d ∣ (b − 1)`** (casting out nines and
its generalizations). Its second open question asks:

> Can the theory extend to composite moduli **not** dividing `(b − 1)`?
> E.g. divisibility by 7 in base 10 requires a *weighted* digit sum, since `7 ∤ 9`.

This file answers that question in full generality.

## What This Proves
For an *arbitrary* modulus `m` and base `b`, define the **weighted digit sum**
`W_{b,m}(n) = Σᵢ dᵢ · (bⁱ mod m)`, where `dᵢ` are the base-`b` digits of `n`.
The positional weight `wᵢ = bⁱ mod m` is periodic in `i`. Then:

* `weighted_modEq`  :  `n ≡ W_{b,m}(n)  [MOD m]`   (for every `b`, `m`, `n`)
* `dvd_iff_dvd_weighted` :  `m ∣ n ↔ m ∣ W_{b,m}(n)`
* `mod_eq_weighted_mod`  :  `n % m = W_{b,m}(n) % m`

The classical `(b−1)`-rule is the special case where every weight collapses to `1`
(because `b ≡ 1 (mod m)` forces `bⁱ ≡ 1`).  Here **no** hypothesis relating `m` to
`b − 1` is needed — the weights carry the full modular information.

## Key Specializations
* **Divisibility by 7 in base 10** — weights `10ⁱ mod 7` cycle `[1,3,2,6,4,5]`
  with period 6 (since `10⁶ ≡ 1 (mod 7)`, a Fermat consequence).
* **Divisibility by 11 in base 10** — weights `10ⁱ mod 11` cycle `[1,10,1,10,…]`,
  recovering the alternating digit-sum rule (parent open question 1).

## Key Mathematical Insight
`n = Σᵢ dᵢ bⁱ` exactly (`Nat.ofDigits_eq_sum_mapIdx`).  Reducing each positional
weight `bⁱ` modulo `m` changes the sum only within its residue class mod `m`, so
the divisibility test is preserved.  The reduction `bⁱ ↦ bⁱ mod m` is what makes
the test *finite/periodic* even when `b ≢ 1 (mod m)`.

## Mathlib Dependencies
- `Nat.ofDigits_digits`        : `ofDigits b (digits b n) = n`
- `Nat.ofDigits_eq_sum_mapIdx` : `ofDigits b L = (L.mapIdx fun i a => a * b^i).sum`
- `Nat.modEq_zero_iff_dvd`, `Nat.mod_modEq`, `List.mapIdx_cons`
-/

namespace DivisibilityBy3OQ02OQ02

open Nat List

-- ============================================================
-- Part I: A congruence lemma for indexed list sums
-- ============================================================

/-- If two indexed weight functions agree modulo `m` at every position, then the
    `mapIdx`-sums they produce agree modulo `m`.  Proved by induction on the list,
    generalizing over the functions so the index shift in `mapIdx_cons` is handled. -/
theorem mapIdx_sum_modEq {m : ℕ} (f g : ℕ → ℕ → ℕ)
    (h : ∀ i d, f i d ≡ g i d [MOD m]) :
    ∀ L : List ℕ, (L.mapIdx f).sum ≡ (L.mapIdx g).sum [MOD m]
  | [] => by
      simp only [List.mapIdx_nil, List.sum_nil]
      exact Nat.ModEq.refl 0
  | a :: t => by
      simp only [List.mapIdx_cons, List.sum_cons]
      exact (h 0 a).add
        (mapIdx_sum_modEq (fun i => f (i + 1)) (fun i => g (i + 1))
          (fun i d => h (i + 1) d) t)

-- ============================================================
-- Part II: The weighted digit sum and the universal rule
-- ============================================================

/-- The **weighted digit sum** of `n` in base `b` relative to modulus `m`:
    `Σᵢ dᵢ · (bⁱ mod m)` where `dᵢ = (Nat.digits b n)`.
    The weights `bⁱ mod m` are periodic in `i`. -/
def weightedDigitSum (b m n : ℕ) : ℕ :=
  ((Nat.digits b n).mapIdx fun i d => d * (b ^ i % m)).sum

/-- **Universal weighted rule.** For *any* base `b` and modulus `m`, a number is
    congruent modulo `m` to its weighted digit sum.  No relation between `m` and
    `b − 1` is required — the weights `bⁱ mod m` encode everything. -/
theorem weighted_modEq (b m n : ℕ) :
    n ≡ weightedDigitSum b m n [MOD m] := by
  unfold weightedDigitSum
  -- n = Σᵢ dᵢ · bⁱ  (exact identity), then reduce each weight bⁱ modulo m.
  have hn : ((Nat.digits b n).mapIdx fun i d => d * b ^ i).sum = n := by
    rw [← Nat.ofDigits_eq_sum_mapIdx, Nat.ofDigits_digits]
  calc n = ((Nat.digits b n).mapIdx fun i d => d * b ^ i).sum := hn.symm
    _ ≡ ((Nat.digits b n).mapIdx fun i d => d * (b ^ i % m)).sum [MOD m] :=
        mapIdx_sum_modEq _ _
          (fun i d => Nat.ModEq.mul_left d (Nat.mod_modEq _ _).symm) _

/-- **Weighted divisibility test.** `m ∣ n` iff `m` divides the weighted digit sum.
    This is the requested extension to composite moduli not dividing `b − 1`. -/
theorem dvd_iff_dvd_weighted (b m n : ℕ) :
    m ∣ n ↔ m ∣ weightedDigitSum b m n := by
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨fun h => (weighted_modEq b m n).symm.trans h,
         fun h => (weighted_modEq b m n).trans h⟩

/-- The remainder of `n` mod `m` equals that of its weighted digit sum. -/
theorem mod_eq_weighted_mod (b m n : ℕ) :
    n % m = weightedDigitSum b m n % m :=
  weighted_modEq b m n

-- ============================================================
-- Part III: The (b−1) rule is the collapsed special case
-- ============================================================

/-- When `m ∣ (b − 1)` (so `b ≡ 1 mod m`), every weight `bⁱ mod m` equals `1`,
    and the weighted digit sum collapses to the ordinary digit sum.  This shows the
    parent's `(b−1)`-rule is precisely the constant-weight specialization. -/
theorem weight_eq_one_of_dvd_pred (b m : ℕ) (hm : 2 ≤ m) (hb : 2 ≤ b)
    (hdiv : m ∣ (b - 1)) (i : ℕ) : b ^ i % m = 1 := by
  have hb1 : b % m = 1 := by
    obtain ⟨k, hk⟩ := hdiv
    have : b = m * k + 1 := by omega
    rw [this, show m * k + 1 = 1 + m * k from by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hpow : b ^ i % m = (b % m) ^ i % m := by rw [Nat.pow_mod]
  rw [hpow, hb1, one_pow, Nat.mod_eq_of_lt (by omega)]

-- ============================================================
-- Part IV: Divisibility by 7 in base 10  (the motivating case)
-- ============================================================

/-- **Divisibility by 7, base 10.** `7 ∤ 9`, so no ordinary digit-sum rule exists;
    the weighted rule with periodic weights `10ⁱ mod 7` supplies the test. -/
theorem seven_dvd_iff (n : ℕ) :
    7 ∣ n ↔ 7 ∣ weightedDigitSum 10 7 n :=
  dvd_iff_dvd_weighted 10 7 n

/-- The base-10 weights for modulus 7 are `[1,3,2,6,4,5]`, repeating with period 6.
    The period is governed by `10⁶ ≡ 1 (mod 7)` (Fermat: `7` prime, `7 ∤ 10`). -/
theorem weights_seven_period : ∀ i, 10 ^ (i + 6) % 7 = 10 ^ i % 7 := by
  intro i
  have h6 : (10 : ℕ) ^ 6 % 7 = 1 := by decide
  calc 10 ^ (i + 6) % 7 = (10 ^ i % 7) * (10 ^ 6 % 7) % 7 := by
          rw [pow_add, Nat.mul_mod]
    _ = (10 ^ i % 7) * 1 % 7 := by rw [h6]
    _ = 10 ^ i % 7 := by rw [mul_one, Nat.mod_mod]

/-- The first six weights, exhibiting the cycle `[1,3,2,6,4,5]`. -/
example : List.map (fun i => 10 ^ i % 7) [0,1,2,3,4,5] = [1,3,2,6,4,5] := by decide

/-- `1001 = 7 · 11 · 13`.  Digits `[1,0,0,1]`, weighted sum `1·1 + 1·6 = 7`. -/
example : 7 ∣ 1001 := by rw [seven_dvd_iff]; native_decide

/-- `1000` is not divisible by 7: weighted sum `1·6 = 6`, and `7 ∤ 6`. -/
example : ¬ (7 ∣ 1000) := by rw [seven_dvd_iff]; native_decide

/-- A larger witness: `123452 = 7 · 17636`. -/
example : 7 ∣ 123452 := by rw [seven_dvd_iff]; native_decide

/-- Remainder form: `n % 7` is computable from the weighted digit sum. -/
theorem seven_mod_eq (n : ℕ) : n % 7 = weightedDigitSum 10 7 n % 7 :=
  mod_eq_weighted_mod 10 7 n

-- ============================================================
-- Part V: Divisibility by 11 — recovering the alternating rule
-- ============================================================

/-- **Divisibility by 11, base 10.**  Here `11 ∣ (10 + 1)`, and the weights
    `10ⁱ mod 11` cycle `[1,10,1,10,…]`; since `10 ≡ −1 (mod 11)` this is exactly
    the classical alternating digit-sum test (parent open question 1). -/
theorem eleven_dvd_iff (n : ℕ) :
    11 ∣ n ↔ 11 ∣ weightedDigitSum 10 11 n :=
  dvd_iff_dvd_weighted 10 11 n

/-- The base-10 weights for modulus 11 alternate `[1,10,1,10,…]` with period 2. -/
theorem weights_eleven_period : ∀ i, 10 ^ (i + 2) % 11 = 10 ^ i % 11 := by
  intro i
  have h2 : (10 : ℕ) ^ 2 % 11 = 1 := by decide
  calc 10 ^ (i + 2) % 11 = (10 ^ i % 11) * (10 ^ 2 % 11) % 11 := by
          rw [pow_add, Nat.mul_mod]
    _ = (10 ^ i % 11) * 1 % 11 := by rw [h2]
    _ = 10 ^ i % 11 := by rw [mul_one, Nat.mod_mod]

/-- The first weights exhibit the alternating pattern `[1,10,1,10,1,10]`. -/
example : List.map (fun i => 10 ^ i % 11) [0,1,2,3,4,5] = [1,10,1,10,1,10] := by decide

/-- `2728 = 11 · 248`.  Alternating (weighted) sum works. -/
example : 11 ∣ 2728 := by rw [eleven_dvd_iff]; native_decide

/-- `2729` is not divisible by 11. -/
example : ¬ (11 ∣ 2729) := by rw [eleven_dvd_iff]; native_decide

-- ============================================================
-- Part VI: Divisibility by 13 — another non-(b−1) modulus
-- ============================================================

/-- **Divisibility by 13, base 10.**  `13 ∤ 9`; weights `10ⁱ mod 13` cycle with
    period 6 as well (`10⁶ ≡ 1 mod 13`). -/
theorem thirteen_dvd_iff (n : ℕ) :
    13 ∣ n ↔ 13 ∣ weightedDigitSum 10 13 n :=
  dvd_iff_dvd_weighted 10 13 n

/-- `10⁶ ≡ 1 (mod 13)`, so the base-10 weights for 13 also have period 6. -/
theorem weights_thirteen_period : ∀ i, 10 ^ (i + 6) % 13 = 10 ^ i % 13 := by
  intro i
  have h6 : (10 : ℕ) ^ 6 % 13 = 1 := by decide
  calc 10 ^ (i + 6) % 13 = (10 ^ i % 13) * (10 ^ 6 % 13) % 13 := by
          rw [pow_add, Nat.mul_mod]
    _ = (10 ^ i % 13) * 1 % 13 := by rw [h6]
    _ = 10 ^ i % 13 := by rw [mul_one, Nat.mod_mod]

/-- `1001 = 7 · 11 · 13`, so `13 ∣ 1001` too. -/
example : 13 ∣ 1001 := by rw [thirteen_dvd_iff]; native_decide

-- ============================================================
-- Part VII: Consistency with the parent digit-sum rule
-- ============================================================

/-- Sanity check: for `m = 9` (which *does* divide `10 − 1`), all weights are `1`,
    so the weighted rule reduces to the parent's plain digit-sum rule for 9. -/
theorem nine_weights_all_one (i : ℕ) : 10 ^ i % 9 = 1 :=
  weight_eq_one_of_dvd_pred 10 9 (by omega) (by omega) ⟨1, by omega⟩ i

/-- Consequently `9 ∣ n ↔ 9 ∣ weightedDigitSum 10 9 n`, matching casting-out-nines. -/
theorem nine_dvd_iff (n : ℕ) :
    9 ∣ n ↔ 9 ∣ weightedDigitSum 10 9 n :=
  dvd_iff_dvd_weighted 10 9 n

end DivisibilityBy3OQ02OQ02

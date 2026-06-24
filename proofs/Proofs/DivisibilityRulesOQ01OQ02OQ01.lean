/-
Alternating Digit-Sum Divisibility Rules: A Sharp Order Characterization
(OQ-01-OQ-02-OQ-01 Extension)

Sibling of `divisibility-rules-oq-01-oq-02`. The parent file settled the
*digit-sum* rule: for EVERY modulus `d` coprime to 10 some power-of-10 base
`10^k` validates `d ∣ n ↔ d ∣ (digits (10^k) n).sum`, with the valid exponents
being exactly the multiples of `ord_d(10)`.

This file treats the *alternating* digit-sum rule (the base-10 rule for 11:
`10 ≡ -1 (mod 11)` makes `n ≡ d₀ - d₁ + d₂ - ⋯`).  Unlike the digit-sum rule,
the alternating rule is **not universal**, and we pin down exactly which moduli
admit one.

Main results:

* `altRule_base_iff` — a **genuine per-base iff**: the base-`10^k` alternating
  rule holds for *all* `n` **iff** `(10 : ZMod d)^k = -1`.  The forward
  direction is forced by the single test value `n = 10^k + 1` (digits `[1,1]`,
  alternating sum `0`), so the rule holding forces `d ∣ 10^k + 1`.

* `altRule_exists_iff` — the **sharp characterization**: for `d > 2` coprime to
  10, a power-of-10 alternating rule exists **iff** `ord_d(10)` is even and
  `10^{ord_d(10)/2} ≡ -1 (mod d)`.  Equivalently, `-1` is a power of `10` in
  `ZMod d`.

The forward arithmetic core is Mathlib's `Nat.dvd_iff_dvd_ofDigits` together
with `Nat.ofDigits_neg_one` (which rewrites `ofDigits (-1)` as the alternating
sum).  The order characterization is the cyclic-group fact that a cyclic group
contains the order-two element `-1` iff its order is even, with `10^{m/2}` the
unique such element.

The file is self-contained and imports only Mathlib.

Tags: number-theory, modular-arithmetic, divisibility, multiplicative-order, extension
-/

import Mathlib

open Nat

namespace DivisibilityRulesOQ01OQ02OQ01

/-
## Part I: The base condition `(10 : ZMod d)^k = -1`

We work with the clean algebraic condition `(10 : ZMod d)^k = -1` and relate it
to the integer divisibility `d ∣ 10^k + 1` that the digit machinery consumes.
-/

/-- `(10 : ZMod d)^k = -1` is exactly the integer statement `d ∣ 10^k + 1`. -/
theorem pow_zmod_eq_neg_one_iff (d k : ℕ) :
    (10 : ZMod d) ^ k = -1 ↔ (d : ℤ) ∣ (10 : ℤ) ^ k + 1 := by
  rw [eq_neg_iff_add_eq_zero]
  rw [show ((10 : ZMod d) ^ k + 1) = (((10 : ℤ) ^ k + 1 : ℤ) : ZMod d) by push_cast; ring]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ d

/-- **Workhorse (sufficiency).** Whenever `(10 : ZMod d)^k = -1` — i.e.
`10^k ≡ -1 (mod d)` — the base `B = 10^k` validates the alternating digit-sum
rule for `d`: a number is divisible by `d` iff the alternating sum of its
base-`10^k` digits is. -/
theorem altRule_of_pow_neg_one (d k : ℕ) (hk : (10 : ZMod d) ^ k = -1) (n : ℕ) :
    d ∣ n ↔
      (d : ℤ) ∣ ((Nat.digits (10 ^ k) n).map (fun a : ℕ => (a : ℤ))).alternatingSum := by
  have hdvd : (d : ℤ) ∣ (10 : ℤ) ^ k + 1 := (pow_zmod_eq_neg_one_iff d k).mp hk
  -- `dvd_iff_dvd_ofDigits` needs `d ∣ (10^k : ℤ) - (-1) = 10^k + 1`.
  have hsub : (d : ℤ) ∣ ((10 ^ k : ℕ) : ℤ) - (-1 : ℤ) := by
    have : ((10 ^ k : ℕ) : ℤ) - (-1 : ℤ) = (10 : ℤ) ^ k + 1 := by push_cast; ring
    rw [this]; exact hdvd
  have t := Nat.dvd_iff_dvd_ofDigits d (10 ^ k) (-1 : ℤ) hsub n
  rwa [Nat.ofDigits_neg_one] at t

/-
## Part II: A genuine per-base iff

The alternating rule for base `10^k` (k ≥ 1) holds for *all* `n` precisely when
`(10 : ZMod d)^k = -1`.  Sufficiency is the workhorse; necessity is forced by
the single value `n = 10^k + 1`, whose base-`10^k` digits are `[1, 1]` and whose
alternating sum is `0`.
-/

/-- The base-`10^k` digits of `10^k + 1` are `[1, 1]` (for `k ≥ 1`). -/
theorem digits_pow_add_one (k : ℕ) (hk : 0 < k) :
    Nat.digits (10 ^ k) (10 ^ k + 1) = [1, 1] := by
  have hb : 1 < 10 ^ k := by
    calc 1 < 10 ^ 1 := by norm_num
    _ ≤ 10 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hmod : (10 ^ k + 1) % 10 ^ k = 1 := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hb]
  have hdiv : (10 ^ k + 1) / 10 ^ k = 1 := by
    rw [add_comm, Nat.add_div_right 1 (by positivity), Nat.div_eq_of_lt hb]
  rw [Nat.digits_def' hb (by positivity), hmod, hdiv,
    Nat.digits_of_lt (10 ^ k) 1 (by norm_num) hb]

/-- **Per-base characterization (genuine iff).** For `k ≥ 1`, the base-`10^k`
alternating digit-sum rule holds for every `n` iff `(10 : ZMod d)^k = -1`. -/
theorem altRule_base_iff (d k : ℕ) (hk : 0 < k) :
    (∀ n, d ∣ n ↔
        (d : ℤ) ∣ ((Nat.digits (10 ^ k) n).map (fun a : ℕ => (a : ℤ))).alternatingSum)
      ↔ (10 : ZMod d) ^ k = -1 := by
  constructor
  · intro hrule
    -- Test the rule at `n = 10^k + 1`: alternating sum is `0`, so `d ∣ 10^k + 1`.
    have h := hrule (10 ^ k + 1)
    rw [digits_pow_add_one k hk] at h
    -- `alternatingSum (map ↑ [1,1]) = 0`, and `d ∣ 0` is trivial.
    have hdvdnat : d ∣ (10 ^ k + 1) := by rw [h]; simp [List.alternatingSum]
    have hdvdint : (d : ℤ) ∣ (10 : ℤ) ^ k + 1 := by
      have := Int.natCast_dvd_natCast.mpr hdvdnat
      push_cast at this; exact this
    exact (pow_zmod_eq_neg_one_iff d k).mpr hdvdint
  · intro hk2 n; exact altRule_of_pow_neg_one d k hk2 n

/-
## Part III: The sharp order characterization

`-1` is a power of `10` in `ZMod d` iff `ord_d(10)` is even and `10^{m/2} = -1`,
where `m = ord_d(10)`.  This is the cyclic-group fact that the order-two element
`-1` lies in `⟨10⟩` iff `|⟨10⟩| = m` is even, in which case `10^{m/2}` is the
unique element of order two.
-/

/-- For `d ≥ 2` coprime to 10, the order of `10` in `ZMod d` is positive. -/
theorem orderOf_ten_pos (d : ℕ) (hd : 2 ≤ d) (hcop : Nat.Coprime 10 d) :
    0 < orderOf (10 : ZMod d) := by
  have heuler : (10 : ZMod d) ^ d.totient = 1 := by
    have h := Nat.ModEq.pow_totient hcop
    have h2 : ((10 ^ d.totient : ℕ) : ZMod d) = ((1 : ℕ) : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    push_cast at h2; exact h2
  have hdvd : orderOf (10 : ZMod d) ∣ d.totient := orderOf_dvd_of_pow_eq_one heuler
  have hφ : 0 < d.totient := Nat.totient_pos.mpr (by omega)
  rcases Nat.eq_zero_or_pos (orderOf (10 : ZMod d)) with h | h
  · rw [h] at hdvd; simp only [Nat.zero_dvd] at hdvd; omega
  · exact h

/-- In `ZMod d` with `d > 2`, `1 ≠ -1` (else `d ∣ 2`). -/
theorem one_ne_neg_one (d : ℕ) (hd : 2 < d) : (1 : ZMod d) ≠ -1 := by
  intro h
  have h2 : (2 : ZMod d) = 0 := by linear_combination h
  have hcast : ((2 : ℕ) : ZMod d) = 0 := by push_cast; exact h2
  have hdvd : d ∣ 2 := (ZMod.natCast_eq_zero_iff 2 d).mp hcast
  have : d ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **Sharp characterization of solvability.** For `d > 2` coprime to 10, `-1`
is a power of `10` in `ZMod d` iff `ord_d(10)` is even and `10^{ord_d(10)/2} = -1`. -/
theorem exists_pow_neg_one_iff_order (d : ℕ) (hd : 2 < d) (hcop : Nat.Coprime 10 d) :
    (∃ k, (10 : ZMod d) ^ k = -1) ↔
      Even (orderOf (10 : ZMod d)) ∧
        (10 : ZMod d) ^ (orderOf (10 : ZMod d) / 2) = -1 := by
  set m := orderOf (10 : ZMod d) with hm
  have hpos : 0 < m := orderOf_ten_pos d (by omega) hcop
  have hone : (10 : ZMod d) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp dvd_rfl
  constructor
  · rintro ⟨k, hk⟩
    -- From `10^k = -1`: square gives `10^(2k) = 1`, so `m ∣ 2k`.
    have hsq : (10 : ZMod d) ^ (2 * k) = 1 := by
      rw [show 2 * k = k * 2 from Nat.mul_comm 2 k, pow_mul, hk]; ring
    have hdvd2k : m ∣ 2 * k := orderOf_dvd_of_pow_eq_one hsq
    -- `m ∤ k`, else `10^k = 1 = -1`, contradicting `1 ≠ -1`.
    have hnk : ¬ m ∣ k := by
      intro hmk
      have : (10 : ZMod d) ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp hmk
      rw [this] at hk
      exact one_ne_neg_one d hd hk
    -- Hence `m` is even.
    have hmeven : Even m := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      have hcop2 : Nat.Coprime m 2 := hodd.coprime_two_right
      exact hnk (hcop2.dvd_of_dvd_mul_left hdvd2k)
    refine ⟨hmeven, ?_⟩
    -- Let `h = m/2`; then `2h = m`, `h ∣ k`, write `k = h*q`.
    obtain ⟨h, hmh⟩ := hmeven           -- m = h + h
    have h2h : m = 2 * h := by omega
    have hhalf : m / 2 = h := by omega
    rw [hhalf]
    have hhk : h ∣ k := by
      have : 2 * h ∣ 2 * k := by rwa [← h2h]
      exact (mul_dvd_mul_iff_left (by norm_num : (2:ℕ) ≠ 0)).mp this
    obtain ⟨q, hq⟩ := hhk
    -- `y := 10^h` satisfies `y^2 = 1` and `y^q = -1`; deduce `y = -1`.
    set y := (10 : ZMod d) ^ h with hy
    have hysq : y ^ 2 = 1 := by rw [hy, ← pow_mul, show h * 2 = m from by omega]; exact hone
    have hyq : y ^ q = -1 := by rw [hy, ← pow_mul, ← hq]; exact hk
    -- `y^q = y^(q % 2)` since `y^2 = 1`.
    have hred : y ^ q = y ^ (q % 2) := by
      conv_lhs => rw [← Nat.div_add_mod q 2, pow_add, pow_mul, hysq, one_pow, one_mul]
    -- `q % 2 = 1` (else `y^q = 1 ≠ -1`); then `y = y^1 = -1`.
    have hcase : q % 2 = 0 ∨ q % 2 = 1 := by omega
    rcases hcase with hr | hr
    · exfalso; rw [hr, pow_zero] at hred; rw [hred] at hyq
      exact one_ne_neg_one d hd hyq
    · rw [hr, pow_one] at hred; rw [hred] at hyq; exact hyq
  · rintro ⟨hmeven, hhalf⟩
    exact ⟨m / 2, hhalf⟩

/-
## Part IV: Main theorem — when a power-of-10 alternating rule exists
-/

/-- **Main theorem (resolves the open question).** For a modulus `d > 2` coprime
to 10, a power-of-10 alternating digit-sum divisibility rule exists **iff**
`ord_d(10)` is even and `10^{ord_d(10)/2} ≡ -1 (mod d)`.  The witness base, when
it exists, is `10^{ord_d(10)/2}`. -/
theorem altRule_exists_iff (d : ℕ) (hd : 2 < d) (hcop : Nat.Coprime 10 d) :
    (∃ k, 0 < k ∧ ∀ n, d ∣ n ↔
        (d : ℤ) ∣ ((Nat.digits (10 ^ k) n).map (fun a : ℕ => (a : ℤ))).alternatingSum)
      ↔ Even (orderOf (10 : ZMod d)) ∧
          (10 : ZMod d) ^ (orderOf (10 : ZMod d) / 2) = -1 := by
  have hpos : 0 < orderOf (10 : ZMod d) := orderOf_ten_pos d (by omega) hcop
  constructor
  · rintro ⟨k, hk, hrule⟩
    have hkneg : (10 : ZMod d) ^ k = -1 := (altRule_base_iff d k hk).mp hrule
    exact (exists_pow_neg_one_iff_order d hd hcop).mp ⟨k, hkneg⟩
  · intro hcond
    have hkneg : (10 : ZMod d) ^ (orderOf (10 : ZMod d) / 2) = -1 := hcond.2
    refine ⟨orderOf (10 : ZMod d) / 2, ?_, ?_⟩
    · -- `m` even and positive ⟹ `m ≥ 2` ⟹ `m/2 ≥ 1`.
      obtain ⟨h, hmh⟩ := hcond.1
      omega
    · exact (altRule_base_iff d (orderOf (10 : ZMod d) / 2)
        (by obtain ⟨h, hmh⟩ := hcond.1; omega)).mpr hkneg

/-
## Part V: Concrete instances

Positive instances (rule exists), with the minimal witness exponent `k`:
* `d = 11`: `10^1 ≡ -1 (mod 11)`           (classic alternating rule).
* `d = 7` : `10^3 = 1000 ≡ -1 (mod 7)`     (`1001 = 7·143`).
* `d = 13`: `10^3 = 1000 ≡ -1 (mod 13)`    (`1001 = 13·77`).

Negative instances (no power-of-10 alternating rule exists):
* `d = 3` : `10 ≡ 1`, so every power of `10` is `1 ≠ -1`.
* `d = 37`: `10^3 ≡ 1` with `ord_37(10) = 3` odd; the three powers `{1, 10, 26}`
  miss `-1 = 36`.
-/

/-- Divisibility by 11 via the alternating digit sum (`k = 1`, `10 ≡ -1 mod 11`). -/
theorem eleven_altRule (n : ℕ) :
    11 ∣ n ↔
      (11 : ℤ) ∣ ((Nat.digits (10 ^ 1) n).map (fun a : ℕ => (a : ℤ))).alternatingSum :=
  altRule_of_pow_neg_one 11 1 (by decide) n

/-- Divisibility by 7 via the base-`10^3` alternating digit sum (`10^3 ≡ -1 mod 7`). -/
theorem seven_altRule (n : ℕ) :
    7 ∣ n ↔
      (7 : ℤ) ∣ ((Nat.digits (10 ^ 3) n).map (fun a : ℕ => (a : ℤ))).alternatingSum :=
  altRule_of_pow_neg_one 7 3 (by decide) n

/-- Divisibility by 13 via the base-`10^3` alternating digit sum (`10^3 ≡ -1 mod 13`). -/
theorem thirteen_altRule (n : ℕ) :
    13 ∣ n ↔
      (13 : ℤ) ∣ ((Nat.digits (10 ^ 3) n).map (fun a : ℕ => (a : ℤ))).alternatingSum :=
  altRule_of_pow_neg_one 13 3 (by decide) n

/-- **No alternating rule for 3.** Every power of `10` is `1` in `ZMod 3`, never
`-1`. -/
theorem three_no_altRule : ¬ ∃ k, (10 : ZMod 3) ^ k = -1 := by
  rintro ⟨k, hk⟩
  rw [show (10 : ZMod 3) = 1 by decide, one_pow] at hk
  exact (by decide : (1 : ZMod 3) ≠ -1) hk

/-- **No alternating rule for 37.** `ord_37(10) = 3` is odd; concretely the
powers `10^k = 10^{k mod 3} ∈ {1, 10, 26}` never equal `-1 = 36`. -/
theorem thirtyseven_no_altRule : ¬ ∃ k, (10 : ZMod 37) ^ k = -1 := by
  rintro ⟨k, hk⟩
  have h3 : (10 : ZMod 37) ^ 3 = 1 := by decide
  have hred : (10 : ZMod 37) ^ k = (10 : ZMod 37) ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [hred] at hk
  have hlt : k % 3 < 3 := Nat.mod_lt k (by norm_num)
  interval_cases (k % 3) <;> revert hk <;> decide

#check @altRule_base_iff
#check @exists_pow_neg_one_iff_order
#check @altRule_exists_iff
#check @eleven_altRule
#check @three_no_altRule

end DivisibilityRulesOQ01OQ02OQ01

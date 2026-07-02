/-
Kummer's Theorem in Digit-Sum Form: the 2-adic Valuation of Central
Binomial Coefficients (Wilson's Theorem OQ-03-OQ-03)

Source: Classical number theory — Ernst Kummer, 1852; the 2-adic
central-binomial identity is folklore (Legendre/Kummer + the popcount).
Status: COMPLETE

## Motivation
The parent entry (WilsonsTheoremOQ03) proves **Legendre's formula** in
digit-sum form:  (p - 1) · ν_p(n!) = n − S_p(n).  Applying it three times
to the factorization  n! = C(n,k) · k! · (n-k)!  yields **Kummer's theorem**:

  (p - 1) · ν_p(C(n,k)) = S_p(k) + S_p(n-k) − S_p(n),

i.e. ν_p(C(n,k)) equals the number of carries when adding k and n−k in
base p.  Mathlib already contains this identity
(`sub_one_mul_padicValNat_choose_eq_sub_sum_digits`).  This entry pushes it
to the *consequences* Mathlib does **not** record:

## What This Proves (new relative to Mathlib)
- [x] `digit_sum_two_mul`   : S₂(2n) = S₂(n)  (a left binary shift adds a 0 digit)
- [x] `digit_two_sum_pos`   : 0 < S₂(n) for n ≥ 1
- [x] `digit_sum_two_pow`   : S₂(2^m) = 1
- [x] **`padicValNat_centralBinom_two`** : ν₂(C(2n,n)) = S₂(n)
      — the 2-adic valuation of the central binomial coefficient equals the
      binary digit sum (popcount) of n.  This is the sharp form of the
      classical fact "C(2n,n) is even"; Mathlib has no exact-valuation result.
- [x] `centralBinom_two_dvd_iff` : 2 ∣ C(2n,n) ↔ n ≠ 0  (even except at n = 0)
- [x] `centralBinom_two_pow_valuation` : ν₂(C(2^{m+1}, 2^m)) = 1
      — the popcount bound is sharp: at powers of two the central binomial
      is divisible by 2 exactly once, hence ≡ 2 (mod 4).
- [x] `not_dvd_choose_iff` : Kummer's no-carry criterion —
      p ∤ C(n,k) ↔ S_p(k) + S_p(n-k) ≤ S_p(n)  (k ≤ n).

## Mathlib Dependencies
- `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` : Kummer (digit-sum form)
- `Nat.centralBinom_eq_two_mul_choose` : C(2n,n) = choose (2n) n
- `Nat.digits_def'`, `Nat.getLast_digit_ne_zero`, `Nat.digits_ne_nil_iff_ne_zero`
- `padicValNat.eq_zero_of_not_dvd`, `one_le_padicValNat_of_dvd`, `pow_padicValNat_dvd`

Parent proof: WilsonsTheoremOQ03.lean (Legendre's formula)
Open question answered: "What does Legendre's formula say about binomial
coefficients — in particular, exactly how even is C(2n,n)?"
-/

import Mathlib

namespace WilsonsTheoremCentralBinom

open Nat

/-! ## Base-2 Digit-Sum Infrastructure -/

/-- **Left binary shift**: multiplying by 2 prepends a `0` digit in base 2,
    so the digit sum is unchanged:  S₂(2n) = S₂(n). -/
theorem digit_sum_two_mul (n : ℕ) :
    (Nat.digits 2 (2 * n)).sum = (Nat.digits 2 n).sum := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · rw [Nat.digits_def' (by norm_num : (1 : ℕ) < 2) (by omega : 0 < 2 * n)]
    have h0 : 2 * n % 2 = 0 := Nat.mul_mod_right 2 n
    have hd : 2 * n / 2 = n := Nat.mul_div_cancel_left n (by norm_num)
    rw [h0, hd, List.sum_cons, Nat.zero_add]

/-- The base-2 digit sum is positive for every `n ≥ 1` (the top digit is
    nonzero and sits inside the digit list). -/
theorem digit_two_sum_pos (n : ℕ) (hn : 0 < n) : 0 < (Nat.digits 2 n).sum := by
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne'
  have hlast : 0 < (Nat.digits 2 n).getLast hnil :=
    Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hn.ne')
  calc (0 : ℕ) < (Nat.digits 2 n).getLast hnil := hlast
    _ ≤ (Nat.digits 2 n).sum :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.getLast_mem hnil)

/-- **Digit sum of a power of two**: S₂(2^m) = 1, since 2^m is a single 1-bit.
    Proved by induction, each step being a binary left shift. -/
theorem digit_sum_two_pow (m : ℕ) : (Nat.digits 2 (2 ^ m)).sum = 1 := by
  induction m with
  | zero =>
      have h1 : Nat.digits 2 (2 ^ 0) = [1] := by
        rw [pow_zero, Nat.digits_def' (by norm_num : (1 : ℕ) < 2) (by norm_num : 0 < 1)]
        simp
      rw [h1]; rfl
  | succ k ih => rw [pow_succ, mul_comm, digit_sum_two_mul, ih]

/-! ## The 2-adic Valuation of the Central Binomial Coefficient -/

/-- **ν₂(C(2n,n)) = popcount(n)**.  The 2-adic valuation of the central
    binomial coefficient `C(2n, n)` equals the number of `1`s in the binary
    expansion of `n` (the base-2 digit sum S₂(n)).

    **Proof.**  Kummer's digit-sum identity for `choose (2n) n` gives
    `(2-1)·ν₂ = S₂(n) + S₂(2n - n) − S₂(2n) = 2·S₂(n) − S₂(2n)`, and a binary
    left shift gives `S₂(2n) = S₂(n)`, so the right side collapses to `S₂(n)`. -/
theorem padicValNat_centralBinom_two (n : ℕ) :
    padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.centralBinom_eq_two_mul_choose]
  have key := sub_one_mul_padicValNat_choose_eq_sub_sum_digits
    (p := 2) (k := n) (n := 2 * n) (by omega)
  rw [show (2 * n - n) = n by omega, digit_sum_two_mul] at key
  -- key : (2 - 1) * ν₂(choose (2n) n) = S₂(n) + S₂(n) − S₂(n)
  simpa using key

/-- **C(2n,n) is even, except at n = 0**:  `2 ∣ C(2n,n) ↔ n ≠ 0`.
    A sharp, exact-parity statement following directly from
    `padicValNat_centralBinom_two`: the valuation is `S₂(n)`, which is
    positive iff `n ≠ 0`. -/
theorem centralBinom_two_dvd_iff (n : ℕ) :
    2 ∣ Nat.centralBinom n ↔ n ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro hd rfl
    rw [Nat.centralBinom_zero] at hd
    exact absurd hd (by norm_num)
  · intro hn
    have hval : padicValNat 2 (Nat.centralBinom n) = (Nat.digits 2 n).sum :=
      padicValNat_centralBinom_two n
    have hs : 0 < padicValNat 2 (Nat.centralBinom n) := by
      rw [hval]; exact digit_two_sum_pos n (Nat.pos_of_ne_zero hn)
    have hne : padicValNat 2 (Nat.centralBinom n) ≠ 0 := hs.ne'
    exact dvd_trans (dvd_pow_self 2 hne) (pow_padicValNat_dvd)

/-- **Sharpness of the popcount bound at powers of two**:
    `ν₂(C(2·2^m, 2^m)) = 1`.  Since `S₂(2^m) = 1`, the central binomial
    coefficient at a power of two is divisible by 2 exactly once — hence
    `C(2^{m+1}, 2^m) ≡ 2 (mod 4)`. -/
theorem centralBinom_two_pow_valuation (m : ℕ) :
    padicValNat 2 (Nat.centralBinom (2 ^ m)) = 1 := by
  rw [padicValNat_centralBinom_two, digit_sum_two_pow]

/-! ## Kummer's No-Carry Criterion (general prime) -/

/-- **Kummer's no-carry criterion (digit-sum form)**: for a prime `p` and
    `k ≤ n`, the prime `p` does *not* divide `C(n,k)` iff there are no carries
    when adding `k` and `n − k` in base `p`, expressed as
    `S_p(k) + S_p(n-k) ≤ S_p(n)`.

    (Together with the always-valid reverse inequality `S_p(n) ≤ S_p(k) +
    S_p(n-k)`, this is the classical equality `S_p(k)+S_p(n-k) = S_p(n)`.)

    **Proof.**  `p ∤ C(n,k)` iff `ν_p(C(n,k)) = 0`, iff `(p-1)·ν_p = 0`; by
    Kummer's identity the latter is `S_p(k) + S_p(n-k) − S_p(n) = 0`. -/
theorem not_dvd_choose_iff (p k n : ℕ) [hp : Fact p.Prime] (h : k ≤ n) :
    ¬ p ∣ n.choose k ↔
      (p.digits k).sum + (p.digits (n - k)).sum ≤ (p.digits n).sum := by
  have hpos : n.choose k ≠ 0 := (Nat.choose_pos h).ne'
  have key := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) (k := k) (n := n) h
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp.out.one_lt
  constructor
  · intro hnd
    have hv : padicValNat p (n.choose k) = 0 := padicValNat.eq_zero_of_not_dvd hnd
    rw [hv, Nat.mul_zero] at key
    omega
  · intro hle
    have hz : (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum = 0 := by omega
    rw [hz] at key
    have hv : padicValNat p (n.choose k) = 0 :=
      (Nat.mul_eq_zero.mp key).resolve_left hp1.ne'
    intro hd
    have := one_le_padicValNat_of_dvd hpos hd
    omega

end WilsonsTheoremCentralBinom

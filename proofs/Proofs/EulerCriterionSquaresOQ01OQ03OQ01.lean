import Mathlib

/-!
# Sophie Germain primes and Mersenne divisors

Follow-up (child) of `euler-criterion-squares-oq-01-oq-03`, which formalized the
**second supplement** to quadratic reciprocity:
`IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7`.

This file draws the classical arithmetic consequence for **Mersenne numbers**.

## Main result

If `p` is a prime with `p ≡ 3 (mod 4)` and `q = 2p + 1` is *also* prime (a Sophie
Germain prime of this residue class), then

```
q ∣ 2^p - 1,
```

i.e. `q` divides the Mersenne number `M_p = 2^p - 1`.

## Mechanism

`p ≡ 3 (mod 4)` forces `q = 2p + 1 ≡ 7 (mod 8)`, so by the second supplement `2` is a
quadratic residue mod `q`. Writing `2 = x^2` in `ZMod q` and applying Fermat's little
theorem,
```
2^p = (x^2)^p = x^(2p) = x^(q-1) = 1   in  ZMod q,
```
because `2p = q - 1`. Hence `q ∣ 2^p - 1`.

This explains, for example, `23 ∣ 2^11 - 1`, `47 ∣ 2^23 - 1`, `167 ∣ 2^83 - 1`.

## Corollary

For `p ≥ 5` in this class the divisor `q` is a *proper* divisor, so the Mersenne number
`2^p - 1` is composite.

All results are fully machine-checked: 0 sorries, 0 axioms.
-/

namespace SophieGermainMersenne

open ZMod

/-- `p ≡ 3 (mod 4)` forces `q = 2p + 1 ≡ 7 (mod 8)`. -/
theorem q_mod_eight (p : ℕ) (hp4 : p % 4 = 3) : (2 * p + 1) % 8 = 7 := by
  omega

/-- When `q ≡ 7 (mod 8)`, `2` is a quadratic residue mod `q` (second supplement). -/
theorem two_isSquare_of_mod {q : ℕ} [Fact q.Prime] (hq : q % 8 = 7) :
    IsSquare (2 : ZMod q) := by
  have hq2 : q ≠ 2 := by omega
  exact (ZMod.exists_sq_eq_two_iff hq2).mpr (Or.inr hq)

/-- **Sophie Germain / Mersenne divisor theorem.**
If `p` is prime with `p ≡ 3 (mod 4)` and `q = 2p + 1` is prime, then `q ∣ 2^p - 1`. -/
theorem dvd_mersenne {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hq : (2 * p + 1).Prime) : (2 * p + 1) ∣ 2 ^ p - 1 := by
  set q := 2 * p + 1 with hq_def
  haveI : Fact q.Prime := ⟨hq⟩
  have hp2 := hp.two_le
  have hqmod : q % 8 = 7 := q_mod_eight p hp4
  -- `2` is a square in `ZMod q`; extract a square root `x`.
  obtain ⟨x, hx⟩ := two_isSquare_of_mod hqmod
  -- `x ≠ 0`, else `2 = 0` in `ZMod q`, forcing `q ∣ 2`, impossible since `q ≥ 5`.
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hx
    have hdvd2 : q ∣ 2 := by
      rw [← Nat.cast_two (R := ZMod q)] at hx
      exact (ZMod.natCast_eq_zero_iff 2 q).mp hx
    have := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  -- Fermat: `2^p = (x^2)^p = x^(2p) = x^(q-1) = 1`.
  have key : (2 : ZMod q) ^ p = 1 := by
    have hsq : (2 : ZMod q) = x ^ 2 := by rw [hx]; ring
    have h2p : 2 * p = q - 1 := by omega
    rw [hsq, ← pow_mul, h2p]
    exact ZMod.pow_card_sub_one_eq_one hx0
  -- Convert back to divisibility over `ℕ`.
  have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
  have hcast : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := by
    rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_two, Nat.cast_one, key, sub_self]
  exact (ZMod.natCast_eq_zero_iff (2 ^ p - 1) q).mp hcast

/-- Linear-vs-exponential gap: `2p + 2 < 2^p` for `p ≥ 5`. -/
theorem lin_lt_two_pow (p : ℕ) (hp : 5 ≤ p) : 2 * p + 2 < 2 ^ p := by
  induction p with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 5 with h | h
    · interval_cases n <;> first | omega | norm_num
    · have hn := ih h
      have : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      omega

/-- **Corollary.** For `p ≥ 5` prime with `p ≡ 3 (mod 4)` and `q = 2p + 1` prime, the
Mersenne number `2^p - 1` is composite (it has the proper divisor `q`). -/
theorem mersenne_not_prime {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hq : (2 * p + 1).Prime) (hp5 : 5 ≤ p) : ¬ (2 ^ p - 1).Prime := by
  intro hM
  have hdvd := dvd_mersenne hp hp4 hq
  have hgap := lin_lt_two_pow p hp5
  rcases (hM.eq_one_or_self_of_dvd (2 * p + 1) hdvd) with h | h
  · omega
  · -- `2p + 1 = 2^p - 1` contradicts `2p + 2 < 2^p`.
    omega

/-! ## Concrete examples of the theorem -/

-- `p = 11`:  `23 ∣ 2^11 - 1 = 2047 = 23 · 89`.
example : (23 : ℕ) ∣ 2 ^ 11 - 1 :=
  dvd_mersenne (by norm_num) (by norm_num) (by norm_num)

-- `p = 23`:  `47 ∣ 2^23 - 1`.
example : (47 : ℕ) ∣ 2 ^ 23 - 1 :=
  dvd_mersenne (by norm_num) (by norm_num) (by norm_num)

-- `p = 83`:  `167 ∣ 2^83 - 1`.
example : (167 : ℕ) ∣ 2 ^ 83 - 1 :=
  dvd_mersenne (by norm_num) (by norm_num) (by norm_num)

-- The Mersenne number `2^11 - 1 = 2047` is composite.
example : ¬ (2 ^ 11 - 1).Prime :=
  mersenne_not_prime (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end SophieGermainMersenne

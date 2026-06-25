import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-
# Sophie Germain Primes and Mersenne Compositeness (sophie-germain-oq-01-oq-02)

The parent open question (sophie-germain-oq-01) asks whether there are infinitely
many Sophie Germain primes.  Its companion file already records the historical
motivation: Sophie Germain primes first arose in the study of Fermat's Last
Theorem.  A second, equally classical reason these primes matter is their effect
on **Mersenne numbers** `2^p - 1`.

## Result

Let `p` be a prime with `p ≡ 3 (mod 4)` such that `q = 2p + 1` is also prime
(so `p` is a Sophie Germain prime).  Then

    q = 2p + 1   divides   the Mersenne number   2^p - 1.

In particular, whenever `p > 3` the Mersenne number `2^p - 1` is **composite**:
it has the proper factor `2p + 1`.

This is the theorem behind Euler's and Lagrange's observation (1750s–1770s) that,
e.g., `M₁₁ = 2^11 - 1 = 2047 = 23 · 89` is composite — here `p = 11` is a Sophie
Germain prime with `11 ≡ 3 (mod 4)` and `2·11 + 1 = 23` is the predicted factor.

## Proof idea

Write `q = 2p + 1`.  From `p ≡ 3 (mod 4)` one computes `q ≡ 7 (mod 8)`, so by the
second supplement to quadratic reciprocity `2` is a quadratic residue modulo `q`.
Euler's criterion then gives

    2^((q-1)/2) ≡ 1 (mod q),   and   (q - 1)/2 = p,

hence `2^p ≡ 1 (mod q)`, i.e. `q ∣ 2^p - 1`.

Mathlib already knows that `2` is a square mod `q` exactly when `q ≡ ±1 (mod 8)`
(`ZMod.exists_sq_eq_two_iff`) and Euler's criterion (`ZMod.euler_criterion`); the
arithmetic linking Sophie Germain primes to Mersenne factors is original here.

All results are fully machine-checked with no axioms beyond Lean/Mathlib's
foundations.
-/

namespace SophieGermainOQ01OQ02

/-- A natural number `p` is a Sophie Germain prime if both `p` and `2p + 1` are prime.
(Mirror of `SophieGermain.IsSophieGermainPrime`; restated here to keep this file
self-contained.) -/
def IsSophieGermainPrime (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)

/-- For `p ≡ 3 (mod 4)`, the safe prime `q = 2p + 1` satisfies `q ≡ 7 (mod 8)`. -/
theorem safe_prime_mod_eight {p : ℕ} (hp4 : p % 4 = 3) : (2 * p + 1) % 8 = 7 := by
  omega

/-- `2` is a quadratic residue modulo the safe prime `q = 2p + 1` when `p ≡ 3 (mod 4)`.
This is the second supplement to quadratic reciprocity specialized to `q ≡ 7 (mod 8)`. -/
theorem two_isSquare_mod_safe {p : ℕ} (hp4 : p % 4 = 3)
    (hq : Nat.Prime (2 * p + 1)) : IsSquare (2 : ZMod (2 * p + 1)) := by
  haveI : Fact (Nat.Prime (2 * p + 1)) := ⟨hq⟩
  have hq2 : (2 * p + 1) ≠ 2 := by omega
  exact (ZMod.exists_sq_eq_two_iff hq2).mpr (Or.inr (safe_prime_mod_eight hp4))

/-- `2` is a unit (nonzero) in `ZMod q` for the safe prime `q = 2p + 1`. -/
theorem two_ne_zero_mod_safe {p : ℕ} (hp4 : p % 4 = 3)
    (hq : Nat.Prime (2 * p + 1)) : (2 : ZMod (2 * p + 1)) ≠ 0 := by
  haveI : Fact (Nat.Prime (2 * p + 1)) := ⟨hq⟩
  have h : ((2 : ℕ) : ZMod (2 * p + 1)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  simpa using h

/-- **Sophie Germain ⟹ Mersenne factor.**
If `p ≡ 3 (mod 4)` is prime and `q = 2p + 1` is also prime (i.e. `p` is a Sophie
Germain prime), then `q` divides the Mersenne number `2^p - 1`. -/
theorem safe_prime_dvd_mersenne {p : ℕ} (hp4 : p % 4 = 3)
    (hq : Nat.Prime (2 * p + 1)) : (2 * p + 1) ∣ 2 ^ p - 1 := by
  haveI : Fact (Nat.Prime (2 * p + 1)) := ⟨hq⟩
  -- 2 is a quadratic residue mod q, so Euler's criterion gives 2^((q-1)/2) = 1
  have hsq : IsSquare (2 : ZMod (2 * p + 1)) := two_isSquare_mod_safe hp4 hq
  have h2ne : (2 : ZMod (2 * p + 1)) ≠ 0 := two_ne_zero_mod_safe hp4 hq
  have heuler : (2 : ZMod (2 * p + 1)) ^ ((2 * p + 1) / 2) = 1 :=
    (ZMod.euler_criterion (2 * p + 1) h2ne).mp hsq
  have hhalf : (2 * p + 1) / 2 = p := by omega
  rw [hhalf] at heuler
  -- transport 2^p ≡ 1 (mod q) to a divisibility statement
  have hcast : ((2 ^ p : ℕ) : ZMod (2 * p + 1)) = ((1 : ℕ) : ZMod (2 * p + 1)) := by
    push_cast
    exact heuler
  rw [ZMod.natCast_eq_natCast_iff] at hcast
  have h1 : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_pow _ _ (by norm_num)
  exact (Nat.modEq_iff_dvd' h1).mp hcast.symm

/-- **Capstone, stated for Sophie Germain primes.**
If `p` is a Sophie Germain prime with `p ≡ 3 (mod 4)`, then the safe prime
`2p + 1` divides the Mersenne number `2^p - 1`. -/
theorem sophie_germain_dvd_mersenne {p : ℕ} (hsg : IsSophieGermainPrime p)
    (hp4 : p % 4 = 3) : (2 * p + 1) ∣ 2 ^ p - 1 :=
  safe_prime_dvd_mersenne hp4 hsg.2

/-- Auxiliary growth bound: `2p + 2 < 2^p` for `p ≥ 5`. Used to show the divisor
`2p + 1` is proper, hence the Mersenne number is composite. -/
theorem two_mul_add_two_lt_two_pow : ∀ {p : ℕ}, 5 ≤ p → 2 * p + 2 < 2 ^ p := by
  intro p
  induction p with
  | zero => intro h; omega
  | succ n ih =>
    intro h
    rcases Nat.lt_or_ge n 5 with hn | hn
    · have hn4 : n = 4 := by omega
      subst hn4
      norm_num
    · have hih := ih hn
      have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      omega

/-- **Mersenne compositeness.**
If `p ≡ 3 (mod 4)` is a Sophie Germain prime with `p ≥ 5`, then `2^p - 1` is not
prime: the safe prime `q = 2p + 1` is a proper divisor. -/
theorem mersenne_not_prime {p : ℕ} (hp4 : p % 4 = 3) (hp5 : 5 ≤ p)
    (hq : Nat.Prime (2 * p + 1)) : ¬ Nat.Prime (2 ^ p - 1) := by
  intro hM
  have hdvd : (2 * p + 1) ∣ 2 ^ p - 1 := safe_prime_dvd_mersenne hp4 hq
  rcases (Nat.Prime.eq_one_or_self_of_dvd hM _ hdvd) with h1 | hself
  · omega
  · have hlt : 2 * p + 2 < 2 ^ p := two_mul_add_two_lt_two_pow hp5
    omega

/-! ## Concrete instances

These exhibit the predicted Mersenne factors for the first Sophie Germain primes
`p ≡ 3 (mod 4)`. -/

/-- `11` is a Sophie Germain prime with `11 ≡ 3 (mod 4)`, so `23 = 2·11 + 1`
divides `2^11 - 1 = 2047`.  (Indeed `2047 = 23 · 89`.) -/
theorem twentythree_dvd_mersenne_eleven : (2 * 11 + 1) ∣ 2 ^ 11 - 1 :=
  safe_prime_dvd_mersenne (by norm_num) (by norm_num)

/-- Hence `2^11 - 1` is composite. -/
theorem mersenne_eleven_not_prime : ¬ Nat.Prime (2 ^ 11 - 1) :=
  mersenne_not_prime (by norm_num) (by norm_num) (by norm_num)

/-- `23` is a Sophie Germain prime with `23 ≡ 3 (mod 4)`, so `47 = 2·23 + 1`
divides `2^23 - 1 = 8388607`.  (Indeed `8388607 = 47 · 178481`.) -/
theorem fortyseven_dvd_mersenne_twentythree : (2 * 23 + 1) ∣ 2 ^ 23 - 1 :=
  safe_prime_dvd_mersenne (by norm_num) (by norm_num)

end SophieGermainOQ01OQ02

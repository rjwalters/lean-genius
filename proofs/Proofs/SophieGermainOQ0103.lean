import Mathlib

/-
# Sophie Germain primes and Fermat-type numbers: the `p ≡ 1 (mod 4)` branch

## Research problem `sophie-germain-oq-01-oq-03`

This file is the **complementary half** of the mod-4 dichotomy begun in the sibling
entry `sophie-germain-oq-01-oq-02`, which proves that a Sophie Germain prime
`p ≡ 3 (mod 4)` forces its safe prime `q = 2p + 1` to *divide the Mersenne number*
`2^p − 1` (so `M_p` is composite).  Here we settle the remaining residue class:

> **Theorem.** If `p` is a prime with `p ≡ 1 (mod 4)` and `q = 2p + 1` is also
> prime (i.e. `p` is a Sophie Germain prime in the complementary class), then
> `q ∣ 2^p + 1`.

Together the two leaves give a clean, complete picture of how a safe prime
`q = 2p + 1` interacts with the base-`2` exponential at the half-period `p`:

| `p mod 4` | `q mod 8` | `2` mod `q` | `2^p mod q` | divisibility    |
|-----------|-----------|-------------|-------------|-----------------|
| `3`       | `7`       | residue     | `+1`        | `q ∣ 2^p − 1`   |
| `1`       | `3`       | non-residue | `−1`        | `q ∣ 2^p + 1`   |

## Proof

Write `q = 2p + 1`.  From `p ≡ 1 (mod 4)` one computes `q ≡ 3 (mod 8)`, so by the
supplement to quadratic reciprocity (`ZMod.exists_sq_eq_two_iff`) **2 is a
quadratic non-residue** modulo `q`.  Euler's criterion (`ZMod.euler_criterion`)
then forces `2^{(q−1)/2} = −1` in `ZMod q` (it is `±1` because its square is
`2^{q−1} = 1`, and `+1` is excluded precisely because `2` is not a square).  Since
`(q − 1)/2 = q / 2 = p`, this reads `2^p = −1`, i.e. `q ∣ 2^p + 1`.

The argument is the mirror image of the sibling proof: there `q ≡ 7 (mod 8)`
makes `2` a residue and Euler's criterion yields `+1`; here `q ≡ 3 (mod 8)`
makes `2` a non-residue and yields `−1`.

The file is **self-contained**: it depends only on Mathlib and re-declares the
`IsSophieGermainPrime` predicate locally (the sibling parent file is a separate
research entry).  Research file — intentionally NOT registered in `Proofs.lean`.

Tags: number-theory, sophie-germain, quadratic-residue, euler-criterion,
fermat-number, safe-prime
-/

namespace SophieGermainOQ0103

/-- A **Sophie Germain prime**: a prime `p` such that `2p + 1` is also prime.
Re-declared locally so this entry stands alone. -/
def IsSophieGermainPrime (p : ℕ) : Prop := p.Prime ∧ (2 * p + 1).Prime

/-! ## Arithmetic of the safe prime `q = 2p + 1` for `p ≡ 1 (mod 4)` -/

/-- For `p ≡ 1 (mod 4)`, the safe prime `q = 2p + 1` satisfies `q ≡ 3 (mod 8)`. -/
theorem safePrime_mod_eight {p : ℕ} (hp4 : p % 4 = 1) : (2 * p + 1) % 8 = 3 := by
  omega

/-- A prime `p ≡ 1 (mod 4)` is at least `5`; hence `q = 2p + 1 ≥ 11 > 2`. -/
theorem safePrime_ne_two {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    2 * p + 1 ≠ 2 := by
  have h2 : 2 ≤ p := hp.two_le
  omega

/-- A prime `p ≡ 1 (mod 4)` satisfies `p ≥ 5` (the smallest such prime). -/
theorem five_le_of_prime_mod_four {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    5 ≤ p := by
  have h2 : 2 ≤ p := hp.two_le
  omega

/-! ## A small exponential estimate -/

/-- `2n < 2^n` for `n ≥ 5` (used to separate `q = 2p+1` from `2^p + 1`). -/
theorem two_mul_lt_two_pow {n : ℕ} (hn : 5 ≤ n) : 2 * n < 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
      rw [pow_succ]
      omega

/-! ## `2` is a quadratic non-residue mod `q` -/

/-- For `p ≡ 1 (mod 4)` and `q = 2p + 1` prime, `2` is **not** a square in
`ZMod q`. -/
theorem two_not_isSquare {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : (2 * p + 1).Prime) :
    ¬ IsSquare (2 : ZMod (2 * p + 1)) := by
  haveI : Fact (2 * p + 1).Prime := ⟨hq⟩
  rw [ZMod.exists_sq_eq_two_iff (p := 2 * p + 1) (safePrime_ne_two hp hp4)]
  have h8 : (2 * p + 1) % 8 = 3 := safePrime_mod_eight hp4
  omega

/-! ## Euler's criterion: `2^p = −1` in `ZMod q` -/

/-- The core congruence: for a Sophie Germain prime `p ≡ 1 (mod 4)`, the base-`2`
power at the half-period equals `−1` in `ZMod (2p+1)`. -/
theorem two_pow_eq_neg_one {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : (2 * p + 1).Prime) :
    (2 : ZMod (2 * p + 1)) ^ p = -1 := by
  haveI : Fact (2 * p + 1).Prime := ⟨hq⟩
  -- `2 ≠ 0` in `ZMod q` (since `q = 2p+1 ≥ 11` does not divide `2`)
  have hb0 : (2 : ZMod (2 * p + 1)) ≠ 0 := by
    have h2 : 2 ≤ p := hp.two_le
    have hcast : ((2 : ℕ) : ZMod (2 * p + 1)) ≠ 0 := by
      intro hdvd0
      rw [ZMod.natCast_eq_zero_iff] at hdvd0
      have := Nat.le_of_dvd (by norm_num) hdvd0
      omega
    simpa using hcast
  -- Euler's criterion: not a square ⟹ `2 ^ (q/2) ≠ 1`, and `q / 2 = p`
  have hns := two_not_isSquare hp hp4 hq
  have heuler := (ZMod.euler_criterion (p := 2 * p + 1) hb0).not
  have hdiv : (2 * p + 1) / 2 = p := by omega
  rw [hdiv] at heuler
  have hne1 : (2 : ZMod (2 * p + 1)) ^ p ≠ 1 := heuler.mp hns
  -- `(2^p)^2 = 2^(q-1) = 1`, so `2^p = ±1`; ruling out `+1` leaves `−1`
  have hsq : ((2 : ZMod (2 * p + 1)) ^ p) ^ 2 = 1 := by
    rw [← pow_mul]
    have hexp : p * 2 = (2 * p + 1) - 1 := by omega
    rw [hexp]
    exact ZMod.pow_card_sub_one_eq_one hb0
  have hpm : (2 : ZMod (2 * p + 1)) ^ p = 1 ∨ (2 : ZMod (2 * p + 1)) ^ p = -1 := by
    have hmul : (2 : ZMod (2 * p + 1)) ^ p * (2 : ZMod (2 * p + 1)) ^ p = 1 := by
      rw [← sq]; exact hsq
    exact mul_self_eq_one_iff.mp hmul
  rcases hpm with h | h
  · exact absurd h hne1
  · exact h

/-! ## Main divisibility theorem -/

/-- **Sophie Germain `p ≡ 1 (mod 4)` ⟹ `2p + 1 ∣ 2^p + 1`.**
If `p` is prime, `p ≡ 1 (mod 4)`, and `q = 2p + 1` is prime, then the safe prime
`q` divides the Fermat-type number `2^p + 1`. -/
theorem two_pow_add_one_dvd {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : (2 * p + 1).Prime) :
    (2 * p + 1) ∣ 2 ^ p + 1 := by
  haveI : Fact (2 * p + 1).Prime := ⟨hq⟩
  rw [← ZMod.natCast_eq_zero_iff]
  have hcong := two_pow_eq_neg_one hp hp4 hq
  push_cast
  rw [hcong]
  ring

/-- Packaged with the `IsSophieGermainPrime` predicate. -/
theorem sophieGermain_dvd_two_pow_add_one {p : ℕ}
    (hSG : IsSophieGermainPrime p) (hp4 : p % 4 = 1) :
    (2 * p + 1) ∣ 2 ^ p + 1 :=
  two_pow_add_one_dvd hSG.1 hp4 hSG.2

/-! ## Compositeness consequence -/

/-- For a Sophie Germain prime `p ≡ 1 (mod 4)` the safe prime `q = 2p + 1` is a
**proper** divisor of `2^p + 1` (`1 < q < 2^p + 1`), so `2^p + 1` is composite. -/
theorem two_pow_add_one_not_prime {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : (2 * p + 1).Prime) :
    ¬ (2 ^ p + 1).Prime := by
  have hdvd := two_pow_add_one_dvd hp hp4 hq
  have hp5 : 5 ≤ p := five_le_of_prime_mod_four hp hp4
  have hlt : 2 * p + 1 < 2 ^ p + 1 := by
    have := two_mul_lt_two_pow hp5
    omega
  have hgt : 1 < 2 * p + 1 := by omega
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd _ hdvd with h1 | hself
  · omega
  · omega

/-! ## Sanity check and the dichotomy

`p = 5`: `5 % 4 = 1` and `q = 11` is prime, so `11 ∣ 2^5 + 1 = 33 = 3 · 11`. -/

example : IsSophieGermainPrime 5 := by
  constructor <;> norm_num

example : (2 * 5 + 1) ∣ 2 ^ 5 + 1 := by decide

end SophieGermainOQ0103

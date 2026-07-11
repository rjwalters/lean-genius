import Mathlib
import Proofs.LagrangeFourSquaresOQ01OQ03Even

/-
# Jacobi four-square RHS: the multiplicative even closed form  (OQ-01 → OQ-03, continued)

`LagrangeFourSquaresOQ01OQ03Even.lean` pins the Jacobi right-hand side
`jacobiCount n = 8·Σ_{d|n, 4∤d} d` on every `n` from ordinary divisor sums, but on
the `4 ∣ n` locus it only records the **recursive/subtractive** form
`jacobiCount n = 8·σ(n) − 32·σ(n/4)`.  This file upgrades that to the textbook
**multiplicative closed form**: for every *even* `n = 2^a·m` with `m` odd and `a ≥ 1`,

  `jacobiCount (2^a · m) = 24 · σ(m)`   (with `σ = ∑_{d ∣ ·} d`).

So the Jacobi RHS on the even part is the single universal constant `24` times the
divisor sum of the odd part — independent of the power of two.  Combined with the
odd collapse `jacobiCount n = 8·σ(n)` (`4 ∤ n`) this is the standard closed form of
Jacobi's four-square theorem's right side, e.g. `r₄(n) = 24·σ(odd part of n)` for
`n` even, `= 8·σ(n)` for `n` odd — here proved for the RHS `jacobiCount`, which is
the elementary half that is *not* Mathlib-blocked (the `r₄ = jacobiCount` equality
still needs Hurwitz quaternions / weight-2 modular forms).

The crux is `sum_divisors_two_pow_mul_odd`: `σ(2^a · m) = (2^{a+1} − 1)·σ(m)` for odd
`m`, from `Nat.Coprime.sum_divisors_mul` (divisor-sum is multiplicative on coprime
factors), `Nat.sum_divisors_prime_pow`, and the geometric sum `Σ_{i<a+1} 2^i =
2^{a+1} − 1`.  Feeding it through the odd branch (`a = 1`) and the `4 ∣ n` recurrence
`jacobiCount_four_dvd_add` (`a ≥ 2`) collapses both to `24·σ(m)`.

Axiom-free (`propext`/`Classical.choice`/`Quot.sound` only): no `native_decide`, no
`sorry`, no `axiom`.
-/

namespace LagrangeFourSquaresOQ01OQ03Closed

open Finset LagrangeFourSquaresOQ01OQ03Even

/-- **Divisor sum of `2^a · m` for odd `m`.**  Since `2^a` and an odd `m` are
coprime, the divisor-sum function is multiplicative, and `σ(2^a) = 2^{a+1} − 1` by
the geometric series, giving `σ(2^a · m) = (2^{a+1} − 1)·σ(m)`. -/
theorem sum_divisors_two_pow_mul_odd (a : ℕ) {m : ℕ} (hm : Odd m) :
    ∑ d ∈ (2 ^ a * m).divisors, d = (2 ^ (a + 1) - 1) * ∑ d ∈ m.divisors, d := by
  have hcop : Nat.Coprime (2 ^ a) m := (Nat.coprime_two_left.mpr hm).pow_left a
  rw [hcop.sum_divisors_mul]
  congr 1
  -- σ(2^a) = ∑_{i < a+1} 2^i = 2^{a+1} − 1
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, Nat.geomSum_eq (le_refl 2) (a + 1)]
  simp

/-- **Multiplicative even closed form of the Jacobi RHS.**  For odd `m` and `a ≥ 1`,
`jacobiCount (2^a · m) = 24 · σ(m)` — the power of two drops out entirely, leaving
the universal factor `24` times the divisor sum of the odd part.

`a = 1` (`n ≡ 2 mod 4`): `4 ∤ 2m`, so `jacobiCount = 8·σ(2m) = 8·3·σ(m) = 24σ(m)`.
`a ≥ 2` (`4 ∣ n`): the recurrence `jacobiCount n + 32·σ(n/4) = 8·σ(n)` with
`σ(2^a m) = (2^{a+1}−1)σ(m)` and `σ(2^{a−2} m) = (2^{a−1}−1)σ(m)` telescopes the
powers of two to `24·σ(m)`. -/
theorem jacobiCount_two_pow_mul_odd {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m) :
    jacobiCount (2 ^ a * m) = 24 * ∑ d ∈ m.divisors, d := by
  rcases a with _ | _ | b
  · omega
  · -- a = 1: n = 2·m, and 4 ∤ 2m since m is odd
    have hnot4 : ¬ (4 : ℕ) ∣ 2 ^ 1 * m := by
      intro h
      rw [pow_one, show (4 : ℕ) = 2 * 2 from rfl,
        Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)] at h
      rw [Nat.odd_iff] at hm
      omega
    rw [jacobiCount_of_not_four_dvd hnot4, sum_divisors_two_pow_mul_odd 1 hm]
    ring
  · -- a = b + 2 ≥ 2: 4 ∣ n = 2^(b+2)·m
    have hfact : (2 : ℕ) ^ (b + 2) * m = 4 * (2 ^ b * m) := by ring
    have h4 : (4 : ℕ) ∣ 2 ^ (b + 2) * m := ⟨2 ^ b * m, hfact⟩
    have hquot : (2 ^ (b + 2) * m) / 4 = 2 ^ b * m := by
      rw [hfact, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
    have hadd := jacobiCount_four_dvd_add h4
    rw [hquot, sum_divisors_two_pow_mul_odd b hm,
        sum_divisors_two_pow_mul_odd (b + 2) hm] at hadd
    -- fold the power of two into an atom `x = 2^b` (x ≥ 1)
    have hx : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
    set x := 2 ^ b with hxdef
    have e1 : (2 : ℕ) ^ (b + 1) = 2 * x := by rw [hxdef]; ring
    have e3 : (2 : ℕ) ^ (b + 2 + 1) = 8 * x := by rw [hxdef]; ring
    rw [e1, e3] at hadd
    -- hadd : jc + 32·((2x−1)·σ) = 8·((8x−1)·σ),  σ = ∑ d ∈ m.divisors, d
    have hclaim : 8 * ((8 * x - 1) * ∑ d ∈ m.divisors, d)
        = 32 * ((2 * x - 1) * ∑ d ∈ m.divisors, d) + 24 * ∑ d ∈ m.divisors, d := by
      have hlin : 8 * (8 * x - 1) = 32 * (2 * x - 1) + 24 := by omega
      calc 8 * ((8 * x - 1) * ∑ d ∈ m.divisors, d)
            = (8 * (8 * x - 1)) * ∑ d ∈ m.divisors, d := by ring
        _ = (32 * (2 * x - 1) + 24) * ∑ d ∈ m.divisors, d := by rw [hlin]
        _ = 32 * ((2 * x - 1) * ∑ d ∈ m.divisors, d) + 24 * ∑ d ∈ m.divisors, d := by ring
    rw [hclaim] at hadd
    -- hadd : jc + K = K + 24·σ  with K = 32·((2x−1)·σ); cancel K
    rw [add_comm (32 * ((2 * x - 1) * ∑ d ∈ m.divisors, d))
        (24 * ∑ d ∈ m.divisors, d)] at hadd
    exact Nat.add_right_cancel hadd

/-- **Even closed form via the odd part.**  For every even `n ≠ 0`,
`jacobiCount n = 24 · σ(oddPart n)`, where `oddPart n = ordCompl[2] n = n / 2^{v₂(n)}`.
Packages `jacobiCount_two_pow_mul_odd` against the canonical `2`-adic factorization
`n = 2^{v₂(n)} · oddPart n`, so no explicit `(a, m)` decomposition is needed at the
call site. -/
theorem jacobiCount_even_ordCompl {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n) :
    jacobiCount n = 24 * ∑ d ∈ (ordCompl[2] n).divisors, d := by
  have ha : 1 ≤ n.factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn h2
  have hodd : Odd (ordCompl[2] n) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))
  have key := jacobiCount_two_pow_mul_odd ha hodd
  rwa [Nat.ordProj_mul_ordCompl_eq_self n 2] at key

/-- Sanity check at `n = 4 = 2² · 1`: `jacobiCount 4 = 24 · σ(1) = 24`. -/
example : jacobiCount (2 ^ 2 * 1) = 24 := by
  rw [jacobiCount_two_pow_mul_odd (by norm_num) (by norm_num)]; decide

/-- Sanity check at `n = 12 = 2² · 3`: `jacobiCount 12 = 24 · σ(3) = 24 · 4 = 96`. -/
example : jacobiCount 12 = 96 := by
  have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [this, jacobiCount_two_pow_mul_odd (by norm_num) (by norm_num)]; decide

end LagrangeFourSquaresOQ01OQ03Closed

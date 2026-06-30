/-
# Cube Root of 2 OQ-05-OQ-02: rational non-integer exponents, and ∛2 + ∛3

## Open Question (parent OQ-05, second listed)
Two related irrationality results that go beyond the parent family `p ^ (1/n)`:

1. **Rational non-integer exponents.** For a prime `p` and a *rational* exponent `q`
   that is not an integer, the real power `p ^ q` is irrational. The parent OQ-05 handles
   only unit-fraction exponents `1/n`; here the exponent is an arbitrary reduced fraction
   `a/b` with `b ≥ 2`.
2. **Sums of cube roots.** `∛2 + ∛3` is irrational.

## Approach

### Part 1 — prime to a non-integer rational power
Write `q = a/b` in lowest terms (`a = q.num.natAbs`, `b = q.den`, `Nat.Coprime a b`,
`b ≥ 2`). Then
  `p ^ (q : ℝ) = p ^ (a · b⁻¹) = (p ^ a) ^ (b⁻¹) = (p ^ a) ^ (1/b)`,
so by the sibling entry's rationality criterion (`irrational_rpow_inv_iff`) `p ^ q` is
irrational **iff** `p ^ a` is not a perfect `b`-th power. A prime power `p ^ a` is a
perfect `b`-th power iff `b ∣ a` (compare `p`-adic valuations:
`(p^a).factorization p = a`, `(k^b).factorization p = b · k.factorization p`). Since
`gcd a b = 1` and `b ≥ 2`, `b ∤ a`, so `p ^ q` is irrational.

### Part 2 — `∛2 + ∛3`
Let `s = ∛2 + ∛3`. Cubing and using `∛2·∛3 = ∛6` (`Real.mul_rpow`) gives the key identity
  `s³ = 5 + 3·∛6·s`.
If `s` were rational then `∛6 = (s³ - 5)/(3 s)` would be rational too (note `s > 0`),
contradicting the sibling entry's `irrational_cbrt_six`. Hence `s` is irrational.

Both parts reuse the sibling `CubeRoot2IrrationalOQ05OQ01`
(`irrational_rpow_inv_iff`, `IsPerfectNthPow`, `rpow_inv_pow`, `irrational_cbrt_six`).

Sorry-free and axiom-free.
-/
import Mathlib
import Proofs.CubeRoot2IrrationalOQ05OQ01

namespace CubeRoot2IrrationalOQ05OQ02

open Real
open CubeRoot2IrrationalOQ05OQ01 (IsPerfectNthPow irrational_rpow_inv_iff rpow_inv_pow
  irrational_cbrt_six)

/-! ## Part 1: prime raised to a non-integer rational power -/

/-- **A prime power is a perfect `b`-th power only when `b ∣ a`.** If `b ∤ a`, then `p ^ a`
is not a perfect `b`-th power. The proof compares `p`-adic valuations: from `p ^ a = k ^ b`
we get `a = b · v_p(k)`, hence `b ∣ a`. -/
theorem not_isPerfectNthPow_prime_pow {p a b : ℕ} (hp : p.Prime)
    (hndvd : ¬ b ∣ a) : ¬ IsPerfectNthPow (p ^ a) b := by
  rintro ⟨k, hk⟩
  -- compare the `p`-adic valuation of both sides of `p ^ a = k ^ b`
  have key : (p ^ a).factorization p = (k ^ b).factorization p := by rw [hk]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization_self, mul_one] at key
  -- `key : a = b * k.factorization p`, so `b ∣ a`
  exact hndvd ⟨k.factorization p, key⟩

/-- **Irrationality of a prime raised to a non-integer rational power.** For a prime `p`
and a positive rational `q` whose denominator is at least `2` (i.e. `q` is not an integer),
the real power `p ^ q` is irrational. This generalizes the parent OQ-05 result
`irrational_rpow_inv_prime` from unit-fraction exponents `1/n` to arbitrary reduced
fractions `a/b`. -/
theorem irrational_prime_rpow {p : ℕ} (hp : p.Prime) {q : ℚ} (hq : 0 < q)
    (hden : 2 ≤ q.den) : Irrational ((p : ℝ) ^ (q : ℝ)) := by
  set a : ℕ := q.num.natAbs with ha
  set b : ℕ := q.den with hb
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  -- `(a : ℤ) = q.num` since `q.num ≥ 0`
  have hacast : (a : ℤ) = q.num := by rw [ha]; exact Int.natAbs_of_nonneg hnum.le
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hbne : (b : ℝ) ≠ 0 := by positivity
  -- rewrite `p ^ q` as `(p ^ a) ^ (1/b)`
  have hrw : (p : ℝ) ^ (q : ℝ) = ((p ^ a : ℕ) : ℝ) ^ ((b : ℝ)⁻¹) := by
    rw [Rat.cast_def, ← hb]
    have hqnum : ((q.num : ℝ)) = (a : ℝ) := by
      rw [← hacast]; push_cast; ring
    rw [hqnum, div_eq_mul_inv, Real.rpow_mul hp0, Real.rpow_natCast]
    push_cast
    ring
  rw [hrw]
  -- not a perfect `b`-th power, since `b ∤ a`
  have hcop : Nat.Coprime a b := q.reduced
  have hndvd : ¬ b ∣ a := by
    intro hd
    have hg1 : Nat.gcd a b = 1 := hcop
    have hbg : b ∣ Nat.gcd a b := Nat.dvd_gcd hd dvd_rfl
    rw [hg1] at hbg
    have : b ≤ 1 := Nat.le_of_dvd one_pos hbg
    omega
  exact (irrational_rpow_inv_iff (m := p ^ a) (n := b) (by omega)).mpr
    (not_isPerfectNthPow_prime_pow hp hndvd)

/-- `2 ^ (2/3)` is irrational: a prime to a non-integer rational power. -/
theorem irrational_two_rpow_two_thirds :
    Irrational ((2 : ℝ) ^ ((2 / 3 : ℚ) : ℝ)) :=
  irrational_prime_rpow (p := 2) (by norm_num) (by norm_num) (by norm_num)

/-- `3 ^ (3/2)` is irrational: the exponent exceeds `1` yet is still non-integer. -/
theorem irrational_three_rpow_three_halves :
    Irrational ((3 : ℝ) ^ ((3 / 2 : ℚ) : ℝ)) :=
  irrational_prime_rpow (p := 3) (by norm_num) (by norm_num) (by norm_num)

/-! ## Part 2: irrationality of `∛2 + ∛3` -/

/-- **`∛2 + ∛3` is irrational.** Cubing the sum and using `∛2·∛3 = ∛6` yields
`(∛2+∛3)³ = 5 + 3·∛6·(∛2+∛3)`; were the sum rational, `∛6` would be rational too,
contradicting `irrational_cbrt_six`. -/
theorem irrational_cbrt_two_add_cbrt_three :
    Irrational ((2 : ℝ) ^ ((3 : ℝ)⁻¹) + (3 : ℝ) ^ ((3 : ℝ)⁻¹)) := by
  set a : ℝ := (2 : ℝ) ^ ((3 : ℝ)⁻¹) with hadef
  set c : ℝ := (3 : ℝ) ^ ((3 : ℝ)⁻¹) with hcdef
  set s : ℝ := a + c with hsdef
  -- the three real cube roots and their basic identities
  have ha3 : a ^ 3 = 2 := by
    have := rpow_inv_pow (m := 2) (n := 3) (by norm_num); simpa [hadef] using this
  have hc3 : c ^ 3 = 3 := by
    have := rpow_inv_pow (m := 3) (n := 3) (by norm_num); simpa [hcdef] using this
  have hac : a * c = (6 : ℝ) ^ ((3 : ℝ)⁻¹) := by
    rw [hadef, hcdef, ← Real.mul_rpow (by norm_num) (by norm_num)]
    norm_num
  -- positivity of the sum
  have ha0 : 0 < a := by rw [hadef]; positivity
  have hc0 : 0 < c := by rw [hcdef]; positivity
  have hs0 : 0 < s := by rw [hsdef]; linarith
  -- the key cubic identity `s³ = 5 + 3·∛6·s`
  have hkey : s ^ 3 = 5 + 3 * ((6 : ℝ) ^ ((3 : ℝ)⁻¹)) * s := by
    have hexp : s ^ 3 = a ^ 3 + c ^ 3 + 3 * (a * c) * (a + c) := by rw [hsdef]; ring
    rw [hexp, ha3, hc3, hac, ← hsdef]; ring
  -- if `s` were rational, `∛6` would be rational, contradicting `irrational_cbrt_six`
  intro hmem
  obtain ⟨r, hr⟩ := hmem
  have hr0 : (r : ℝ) ≠ 0 := by rw [hr]; exact hs0.ne'
  have hcbrt6 : (6 : ℝ) ^ ((3 : ℝ)⁻¹) = (((r ^ 3 - 5) / (3 * r) : ℚ) : ℝ) := by
    have h3r : (3 : ℝ) * (r : ℝ) ≠ 0 := mul_ne_zero (by norm_num) hr0
    rw [← hr] at hkey
    push_cast
    rw [eq_div_iff h3r]
    linear_combination -hkey
  exact irrational_cbrt_six ⟨(r ^ 3 - 5) / (3 * r), hcbrt6.symm⟩

end CubeRoot2IrrationalOQ05OQ02

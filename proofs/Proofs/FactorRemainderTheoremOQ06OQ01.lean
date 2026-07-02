/-
# Factor / Remainder Theorem, OQ-06-OQ-01: rational `k`-th roots of integers

This file answers the first open question left by the parent entry
`FactorRemainderTheoremOQ06.lean` (the rational root theorem in concrete
`num/den` form):

> Generalize the `√2` application to a clean criterion: for `n : ℤ` not a
> perfect `k`-th power, `∀ r : ℚ, rᵏ ≠ n`.

The parent proved `∀ r : ℚ, r ^ 2 ≠ 2` as a one-off worked example of the
rational root theorem applied to the monic polynomial `X² − 2`. Here we replace
`X² − 2` by the monic polynomial `X^k − C n` for arbitrary `k ≥ 1` and arbitrary
`n : ℤ`, obtaining the general principle that underlies **every** "`n`-th root of
an integer is either an integer or irrational" argument:

    a rational `k`-th root of an integer is itself an integer,

and hence the criterion

    (∀ m : ℤ, m ^ k ≠ n)  →  (∀ r : ℚ, r ^ k ≠ n),

together with the clean equivalence

    (∃ r : ℚ, r ^ k = n)  ↔  (∃ m : ℤ, m ^ k = n).

## Main results

- `rat_root_den_eq_one`  : a rational `k`-th root (`k ≥ 1`) of an integer has `den = 1`
- `int_pow_eq_of_rat_pow`: such a root is the integer `r.num`, and `r.num ^ k = n`
- `not_rat_pow_of_not_int_pow` : the **criterion** — `n` not a perfect `k`-th power ⟹ no rational `k`-th root
- `exists_rat_pow_iff_exists_int_pow` : rational and integral `k`-th-power problems coincide
- `rat_prime_ne_pow` : **no prime is a rational `k`-th power for `k ≥ 2`**
  (generalizes `√2 ∉ ℚ` to all primes and all exponents)
- worked instances: `rat_sq_ne_two`, `rat_cube_ne_two`, `rat_sq_ne_three`,
  `rat_cube_ne_four` (the last via the general criterion, `4` being a non-prime
  non-cube)

## Honest scope

The engine is the parent's `monic_root_den_eq_one` (itself a concrete repackaging
of Mathlib's rational root theorem). This file supplies the *general* monic
polynomial `X^k − C n` in place of the parent's single `X² − 2`, and packages the
resulting number-theoretic criterion. The proofs are short; the value is turning a
one-off example into the reusable general statement it was an instance of.

## References

- Parent gallery entry factor-remainder-theorem-oq-06 (rational root theorem, concrete form)
- Serge Lang, *Algebra* (integral closure; `n`-th roots of integers)
-/

import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Localization.Rat
import Mathlib.Tactic
import Proofs.FactorRemainderTheoremOQ06

open Polynomial

namespace FactorRemainderTheoremOQ06OQ01

open FactorRemainderTheoremOQ06

variable {k : ℕ} {n : ℤ} {r : ℚ}

/-! ### The monic polynomial `X^k − C n` and its evaluation -/

/-- `X^k − C n ∈ ℤ[X]` is monic for every exponent `k ≥ 1`. -/
theorem monic_X_pow_sub_C_int (hk : k ≠ 0) : (X ^ k - C n : ℤ[X]).Monic :=
  monic_X_pow_sub_C n hk

/-- Evaluating `X^k − C n` at a rational `r` gives `r^k − n`. -/
theorem aeval_X_pow_sub_C (r : ℚ) (k : ℕ) (n : ℤ) :
    aeval r (X ^ k - C n : ℤ[X]) = r ^ k - (n : ℚ) := by
  simp [map_sub, map_pow, aeval_X, map_intCast]

/-! ### A rational `k`-th root of an integer is an integer -/

/-- **Key step.** If `r : ℚ` satisfies `r ^ k = n` for some integer `n` and `k ≥ 1`,
then `r` is an integer: its denominator is `1`. This is the rational root theorem
applied to the monic polynomial `X^k − C n`, generalizing the parent's `√2` step. -/
theorem rat_root_den_eq_one (hk : k ≠ 0) (hr : r ^ k = (n : ℚ)) : r.den = 1 := by
  have hroot : aeval r (X ^ k - C n : ℤ[X]) = 0 := by
    rw [aeval_X_pow_sub_C, hr]; ring
  exact monic_root_den_eq_one (monic_X_pow_sub_C_int hk) hroot

/-- A rational `k`-th root of an integer equals its own numerator (it is an integer). -/
theorem rat_root_eq_num (hk : k ≠ 0) (hr : r ^ k = (n : ℚ)) : r = (r.num : ℚ) := by
  have hden := rat_root_den_eq_one hk hr
  conv_lhs => rw [← Rat.num_div_den r, hden]
  simp

/-- The integer `r.num` is an actual `k`-th root of `n`: `r.num ^ k = n`. -/
theorem int_pow_eq_of_rat_pow (hk : k ≠ 0) (hr : r ^ k = (n : ℚ)) : r.num ^ k = n := by
  have h : (r.num : ℚ) ^ k = (n : ℚ) := by rw [← rat_root_eq_num hk hr]; exact hr
  exact_mod_cast h

/-! ### The criterion and the rational ↔ integral equivalence -/

/-- **Generalized irrationality criterion.** If the integer `n` is not a perfect
`k`-th power (`k ≥ 1`) — no integer `m` has `m ^ k = n` — then no rational number
is a `k`-th root of `n`. This is the clean statement of which `√2 ∉ ℚ` is the
special case `n = 2`, `k = 2`. -/
theorem not_rat_pow_of_not_int_pow (hk : k ≠ 0)
    (h : ∀ m : ℤ, m ^ k ≠ n) : ∀ r : ℚ, r ^ k ≠ (n : ℚ) := by
  intro r hr
  exact h r.num (int_pow_eq_of_rat_pow hk hr)

/-- **Rational and integral `k`-th-power problems coincide** (`k ≥ 1`): an integer
`n` has a rational `k`-th root iff it has an integer `k`-th root. -/
theorem exists_rat_pow_iff_exists_int_pow (hk : k ≠ 0) :
    (∃ r : ℚ, r ^ k = (n : ℚ)) ↔ (∃ m : ℤ, m ^ k = n) := by
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r.num, int_pow_eq_of_rat_pow hk hr⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m : ℚ), by exact_mod_cast hm⟩

/-! ### No prime is a rational `k`-th power (`k ≥ 2`) -/

/-- A prime `p : ℕ` is not a nontrivial perfect power: `a ^ k ≠ p` for all `a : ℕ`
when `k ≥ 2`. -/
theorem nat_prime_ne_pow {p : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    ∀ a : ℕ, a ^ k ≠ p := by
  intro a ha
  have hadvd : a ∣ p := ha ▸ dvd_pow_self a (by omega)
  rcases (Nat.dvd_prime hp).mp hadvd with h1 | hpa
  · rw [h1, one_pow] at ha
    have := hp.two_le; omega
  · rw [hpa] at ha
    have hpow : p ^ k = p ^ 1 := by simpa using ha
    have := Nat.pow_right_injective hp.two_le hpow
    omega

/-- The integer version: a prime is not a nontrivial perfect power in `ℤ`. -/
theorem int_prime_ne_pow {p : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    ∀ m : ℤ, m ^ k ≠ (p : ℤ) := by
  intro m hm
  have key : m.natAbs ^ k = p := by
    have h := congrArg Int.natAbs hm
    rw [Int.natAbs_pow] at h
    simpa using h
  exact nat_prime_ne_pow hp hk m.natAbs key

/-- **No prime is a rational `k`-th power for `k ≥ 2`.** The full generalization of
the irrationality of `√2`: for every prime `p` and every exponent `k ≥ 2`, no
rational number `r` satisfies `r ^ k = p`. In particular `√p`, `∛p`, … are all
irrational for every prime `p`. -/
theorem rat_prime_ne_pow {p : ℕ} (hp : p.Prime) (hk : 2 ≤ k) (r : ℚ) :
    r ^ k ≠ (p : ℚ) := by
  have h := not_rat_pow_of_not_int_pow (n := (p : ℤ)) (by omega) (int_prime_ne_pow hp hk) r
  simpa using h

/-! ### Worked instances -/

/-- `√2 ∉ ℚ`, recovered from the general criterion (the parent's one-off example). -/
theorem rat_sq_ne_two (r : ℚ) : r ^ 2 ≠ 2 := by
  have h := rat_prime_ne_pow (p := 2) (by norm_num) (k := 2) (by norm_num) r
  simpa using h

/-- `∛2 ∉ ℚ`: no rational number cubes to `2`. New relative to the parent, which
only handled the square case. -/
theorem rat_cube_ne_two (r : ℚ) : r ^ 3 ≠ 2 := by
  have h := rat_prime_ne_pow (p := 2) (by norm_num) (k := 3) (by norm_num) r
  simpa using h

/-- `√3 ∉ ℚ`: no rational number squares to `3`. -/
theorem rat_sq_ne_three (r : ℚ) : r ^ 2 ≠ 3 := by
  have h := rat_prime_ne_pow (p := 3) (by norm_num) (k := 2) (by norm_num) r
  simpa using h

/-- A **non-prime** instance of the general criterion: `4` is not a perfect cube,
so `∛4 ∉ ℚ`. Here we discharge the integer hypothesis `∀ m : ℤ, m ^ 3 ≠ 4` by a
finite divisor check, exercising the criterion beyond the prime case. -/
theorem rat_cube_ne_four (r : ℚ) : r ^ 3 ≠ 4 := by
  have hint : ∀ m : ℤ, m ^ 3 ≠ 4 := by
    intro m hm
    have hmdvd : m ∣ 4 := hm ▸ dvd_pow_self m (by norm_num)
    have habs : |m| ≤ 4 := Int.le_of_dvd (by norm_num) ((abs_dvd m 4).mpr hmdvd)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    interval_cases m <;> norm_num at hm
  have h := not_rat_pow_of_not_int_pow (n := (4 : ℤ)) (by norm_num) hint r
  simpa using h

end FactorRemainderTheoremOQ06OQ01

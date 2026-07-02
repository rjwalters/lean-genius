import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# The Lucas / Kummer digit structure of vanishing Hasse derivatives of `Xᵐ`

Problem id: `factor-remainder-hasse-derivative-fq-oq-01-oq-01`
(child of `factor-remainder-hasse-derivative-fq-oq-01`, grandchild of
`factor-remainder-hasse-derivative-fq`).

## Question

The parent (`FactorRemainderHasseDerivativeFqOQ01`) established the *overcounting
dichotomy*: over a field of characteristic `p`, the **ordinary** iterated-derivative
multiplicity test is exact when the true root multiplicity `m` satisfies `m < p` and
becomes **blind** (every ordinary derivative vanishes) once `m ≥ p`.  The follow-up
open question asks, in the unbounded regime `m ≥ p`, to *stratify by the base-`p`
digits of `m`*: which Hasse derivatives remain nonvanishing, and how does the ordinary
test's blindness interact with the **Lucas / Kummer** structure of the binomial
coefficients `C(m, k)` that define `hasseDeriv`?

## Answer

For the pure power `Xᵐ` the `k`-th Hasse derivative is the single monomial

  `hasseDeriv k (Xᵐ) = C(m, k) · X^(m-k)`  (`hasseDeriv_X_pow`),

so over a characteristic-`p` field it is nonzero **exactly** when the binomial
coefficient survives reduction mod `p`:

  `hasseDeriv k (Xᵐ) ≠ 0  ↔  ¬ p ∣ C(m, k)`  (`hasseDeriv_X_pow_ne_zero_iff`).

Feeding this into **Lucas's theorem** (`Choose.choose_modEq_prod_range_choose_nat`) resolves the
question completely.  Writing `m` and `k` in base `p`, `C(m, k) ≢ 0 (mod p)` iff every
base-`p` digit of `k` is `≤` the corresponding digit of `m` (Kummer: no carries).  Hence

  `hasseDeriv k (Xᵐ) ≠ 0  ↔  ∀ i, (k's i-th base-p digit) ≤ (m's i-th base-p digit)`

(`hasseDeriv_X_pow_ne_zero_iff_digits`).  The ordinary test is blind for `m ≥ p`
precisely because *it can only read the orders `k < p` scaled by the unit `k!`*, while
the true surviving orders are the digit-dominated `k`, which for `m ≥ p` are spread all
the way out to `k = m`.  The number of surviving orders is `∏ (dᵢ + 1)` over the base-`p`
digits `dᵢ` of `m` (Glaisher/Fine count of odd/nonzero binomials), realized concretely
below over `𝔽₂`.

## Main results

* `hasseDeriv_X_pow` — closed form `hasseDeriv k (Xᵐ) = C(m,k) · X^(m-k)` over any ring.
* `hasseDeriv_X_pow_ne_zero_iff` / `hasseDeriv_X_pow_eq_zero_iff` — over a
  characteristic-`p` field, (non)vanishing of `hasseDeriv k (Xᵐ)` `↔ ¬ p ∣ C(m,k)`.
* `not_dvd_choose_digit_iff` — for a single base-`p` digit `a < p`, `¬ p ∣ C(a,b) ↔ b ≤ a`.
* `hasseDeriv_X_pow_ne_zero_iff_digits` — **capstone.** Lucas digit-domination
  criterion for which Hasse derivatives of `Xᵐ` survive in characteristic `p`.
* `nonzero_orders_X3_F2`, `nonzero_orders_X4_F2` — the digit count realized over `𝔽₂`:
  `X³` (digits `11₂`) keeps **all** four orders `k ≤ 3` (`∏(dᵢ+1) = 2·2 = 4`), while
  `X⁴` (digits `100₂`) keeps only `k ∈ {0,4}` (`∏(dᵢ+1) = 1·1·2 = 2`).

All results are `0`-axiom, `0`-sorry, over any characteristic-`p` field (hence every `𝔽_q`).
-/

namespace FactorRemainderHasseDerivativeFqOQ01OQ01

open Polynomial Nat Finset

variable {R : Type*} {F : Type*} {p : ℕ}

/-- **Closed form of the Hasse derivative of a pure power.** For every commutative ring,
`hasseDeriv k (Xᵐ) = C(m,k) · X^(m-k)`, a single monomial whose coefficient is the
binomial `m.choose k`. This is the object whose mod-`p` behaviour the open question
studies. -/
theorem hasseDeriv_X_pow [Semiring R] (k m : ℕ) :
    hasseDeriv k (X ^ m : R[X]) = monomial (m - k) ((m.choose k : R)) := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial, mul_one]

/-- **Vanishing criterion via divisibility of the binomial coefficient.** Over a field of
characteristic `p`, `hasseDeriv k (Xᵐ)` is nonzero exactly when `C(m,k)` survives
reduction mod `p`. This is the bridge from the polynomial world to Lucas's theorem. -/
theorem hasseDeriv_X_pow_ne_zero_iff [Field F] [CharP F p] (k m : ℕ) :
    hasseDeriv k (X ^ m : F[X]) ≠ 0 ↔ ¬ (p ∣ m.choose k) := by
  rw [hasseDeriv_X_pow, Ne, monomial_eq_zero_iff, CharP.cast_eq_zero_iff F p]

/-- Contrapositive packaging: `hasseDeriv k (Xᵐ) = 0 ↔ p ∣ C(m,k)`. -/
theorem hasseDeriv_X_pow_eq_zero_iff [Field F] [CharP F p] (k m : ℕ) :
    hasseDeriv k (X ^ m : F[X]) = 0 ↔ p ∣ m.choose k := by
  rw [← not_ne_iff, hasseDeriv_X_pow_ne_zero_iff, not_not]

/-- **A single base-`p` digit never introduces a factor of `p`.** If `b ≤ a < p` then the
binomial coefficient `C(a,b)` is coprime to `p`. Indeed `C(a,b)·b!·(a-b)! = a!` and `p`
does not divide `a!` because `a < p`. -/
theorem not_dvd_choose_of_le_of_lt_prime (hp : p.Prime) {a b : ℕ}
    (hba : b ≤ a) (ha : a < p) : ¬ p ∣ a.choose b := by
  intro hdvd
  have hfac : a.choose b * b ! * (a - b)! = a ! := Nat.choose_mul_factorial_mul_factorial hba
  have hpa : p ∣ a ! := by
    rw [← hfac]; exact (hdvd.mul_right _).mul_right _
  rw [Nat.Prime.dvd_factorial hp] at hpa
  omega

/-- **Digit-level Lucas criterion.** For a base-`p` digit position, i.e. `a < p`, the
binomial `C(a,b)` avoids `p` exactly when `b ≤ a`. This is the atomic statement that,
multiplied across digits, becomes Lucas's theorem. -/
theorem not_dvd_choose_digit_iff (hp : p.Prime) {a b : ℕ} (ha : a < p) :
    ¬ p ∣ a.choose b ↔ b ≤ a := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    rw [Nat.choose_eq_zero_of_lt hlt] at h
    exact h (dvd_zero p)
  · intro hba
    exact not_dvd_choose_of_le_of_lt_prime hp hba ha

/-- **Capstone — the Lucas digit-domination criterion for surviving Hasse derivatives.**
Over a field of characteristic `p`, once `m` and `k` are bounded by `p ^ a`, the `k`-th
Hasse derivative of `Xᵐ` is nonzero **iff every base-`p` digit of `k` is dominated by the
corresponding digit of `m`**:

  `hasseDeriv k (Xᵐ) ≠ 0 ↔ ∀ i < a, ⌊k / pⁱ⌋ mod p ≤ ⌊m / pⁱ⌋ mod p`.

This is exactly the Lucas/Kummer stratification the open question asked for: the ordinary
derivative test only ever inspects the low orders `k < p` (scaled by the unit `k!`), but
the Hasse derivatives that genuinely survive are the digit-dominated `k`, which for
`m ≥ p` reach all the way to `k = m`. -/
theorem hasseDeriv_X_pow_ne_zero_iff_digits [Field F] [CharP F p]
    (hp : p.Prime) {a m k : ℕ} (hm : m < p ^ a) (hk : k < p ^ a) :
    hasseDeriv k (X ^ m : F[X]) ≠ 0 ↔
      ∀ i ∈ range a, (k / p ^ i % p) ≤ (m / p ^ i % p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [hasseDeriv_X_pow_ne_zero_iff]
  -- Lucas's theorem: `C(m,k)` is congruent mod `p` to the product of digit binomials.
  have hlucas : m.choose k ≡
      ∏ i ∈ range a, (m / p ^ i % p).choose (k / p ^ i % p) [MOD p] :=
    Choose.choose_modEq_prod_range_choose_nat hm hk
  -- Divisibility transfers across the congruence.
  have hdvd_iff : p ∣ m.choose k ↔
      p ∣ ∏ i ∈ range a, (m / p ^ i % p).choose (k / p ^ i % p) := by
    constructor <;> intro h
    · exact Nat.modEq_zero_iff_dvd.mp (hlucas.symm.trans (Nat.modEq_zero_iff_dvd.mpr h))
    · exact Nat.modEq_zero_iff_dvd.mp (hlucas.trans (Nat.modEq_zero_iff_dvd.mpr h))
  rw [hdvd_iff, hp.prime.dvd_finset_prod_iff]
  push_neg
  constructor
  · intro h i hi
    have hmi : m / p ^ i % p < p := Nat.mod_lt _ hp.pos
    exact (not_dvd_choose_digit_iff hp hmi).mp (h i hi)
  · intro h i hi
    have hmi : m / p ^ i % p < p := Nat.mod_lt _ hp.pos
    exact (not_dvd_choose_digit_iff hp hmi).mpr (h i hi)

/-- **Realization over `𝔽₂`, digits `11₂` (dominating case).** `3 = 11₂`, so every
`k ≤ 3` is digit-dominated: all four Hasse derivatives of `X³` are nonzero over `𝔽₂`.
The count `4 = (1+1)(1+1) = ∏(dᵢ + 1)` matches the Glaisher/Fine formula. -/
theorem nonzero_orders_X3_F2 (k : ℕ) :
    hasseDeriv k (X ^ 3 : (ZMod 2)[X]) ≠ 0 ↔ k ≤ 3 := by
  constructor
  · intro h
    by_contra hk
    push_neg at hk
    exact h (hasseDeriv_eq_zero_of_lt_natDegree _ k (by rw [natDegree_X_pow]; omega))
  · intro hk
    rw [hasseDeriv_X_pow_ne_zero_iff]
    interval_cases k <;> decide

/-- **Realization over `𝔽₂`, digits `100₂` (sparse case).** `4 = 100₂`, so only `k` with
zero digits in the low positions survive: the Hasse derivatives of `X⁴` over `𝔽₂` are
nonzero exactly for `k ∈ {0, 4}` and vanish for `k = 1, 2, 3`. The count
`2 = (0+1)(0+1)(1+1) = ∏(dᵢ + 1)` again matches. -/
theorem nonzero_orders_X4_F2 (k : ℕ) :
    hasseDeriv k (X ^ 4 : (ZMod 2)[X]) ≠ 0 ↔ (k = 0 ∨ k = 4) := by
  constructor
  · intro h
    rcases le_or_gt k 4 with hle | hgt
    · rw [hasseDeriv_X_pow_ne_zero_iff] at h
      interval_cases k <;> first
        | (left; rfl)
        | (right; rfl)
        | (exact absurd (by decide) h)
    · exact absurd (hasseDeriv_eq_zero_of_lt_natDegree _ k (by rw [natDegree_X_pow]; omega)) h
  · rintro (rfl | rfl) <;> rw [hasseDeriv_X_pow_ne_zero_iff] <;> decide

/-- The middle orders vanish and the extreme orders survive, stated directly. -/
theorem hasseDeriv_X4_F2_profile :
    hasseDeriv 0 (X ^ 4 : (ZMod 2)[X]) ≠ 0 ∧
    hasseDeriv 1 (X ^ 4 : (ZMod 2)[X]) = 0 ∧
    hasseDeriv 2 (X ^ 4 : (ZMod 2)[X]) = 0 ∧
    hasseDeriv 3 (X ^ 4 : (ZMod 2)[X]) = 0 ∧
    hasseDeriv 4 (X ^ 4 : (ZMod 2)[X]) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hasseDeriv_X_pow_ne_zero_iff]; decide
  · rw [hasseDeriv_X_pow_eq_zero_iff]; decide
  · rw [hasseDeriv_X_pow_eq_zero_iff]; decide
  · rw [hasseDeriv_X_pow_eq_zero_iff]; decide
  · rw [hasseDeriv_X_pow_ne_zero_iff]; decide

end FactorRemainderHasseDerivativeFqOQ01OQ01

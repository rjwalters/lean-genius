import Mathlib

/-
# Factor–remainder theorem OQ-01-OQ-01-OQ-01-OQ-01:
# the full failure profile of the ordinary-derivative test over 𝔽_q

Problem id: `factor-remainder-theorem-oq-01-oq-01-oq-01-oq-01`
(child of `factor-remainder-theorem-oq-01-oq-01-oq-01`).

## Background

The parent entry (`FactorRemainderTheoremOQ01OQ01OQ01`) exhibited the canonical
positive-characteristic discrepancy with the single witness `f = Xᵖ` over the
*prime* field `𝔽ₚ = ZMod p`: the ordinary-derivative multiplicity test collapses
(`derivative (Xᵖ) = 0` identically, so every derivative condition holds vacuously
and the test would falsely certify `Xᵏ ∣ Xᵖ` for all `k`), while the
characteristic-free coefficient/Taylor test stays sharp (`Xᵏ ∣ Xᵖ ↔ k ≤ p`).

Its open question asks to **generalise the witness to `f = X^{pᵉ}` and to an
arbitrary finite field `𝔽_q`**, giving the *complete* failure profile of the test.
Since every finite field `𝔽_q` (`q = pᵈ`) is a field of characteristic `p`, we
work over an arbitrary `[Field K] [CharP K p]`; the results specialise to every
`𝔽_q` and to `ZMod p` at once.

## What is new here versus the sibling dichotomy

The sibling entry `factor-remainder-hasse-derivative-fq-oq-01` already proved the
*eval-level* dichotomy for a **general** polynomial (true multiplicity `m < p` ⟹
exact, `m ≥ p` ⟹ unbounded overcount).  `X^{pᵉ}` lands in the overcount regime,
so its ordinary collapse is a corollary of that work.

The genuinely new content is a **sharper, whole-polynomial statement specific to
the `p`-power witnesses**, driven by Kummer's theorem on binomial coefficients:

* For `X^{pᵉ}` even the **Hasse derivatives themselves vanish identically** at
  *every* intermediate order `0 < j < pᵉ` — not merely their values at `0`.  This
  is because `hasseDeriv j (X^{pᵉ}) = (C(pᵉ, j) : K)·X^{pᵉ − j}` and, over
  characteristic `p`, `p ∣ C(pᵉ, j)` for `0 < j < pᵉ`
  (`Nat.Prime.dvd_choose_pow`).
* The Hasse derivative therefore survives **only at the two extreme orders**:
  `hasseDeriv j (X^{pᵉ}) ≠ 0 ↔ j = 0 ∨ j = pᵉ`
  (`hasseDeriv_X_pe_ne_zero_iff`), using the exact criterion
  `Nat.Prime.dvd_choose_pow_iff`.

Contrast with the sibling's generic `f`, whose Hasse derivative first *fires* at
the true multiplicity: the `p`-power witnesses have the extra rigidity that the
Hasse derivative is dead throughout the open interval `(0, pᵉ)`.

## Main results

* `derivative_X_pe_eq_zero` — the ordinary derivative of `X^{pᵉ}` is `0` (`e ≥ 1`).
* `ordinary_criterion_vacuous` — every ordinary derivative condition holds at `0`:
  the ordinary test cannot bound the multiplicity (it certifies `Xᵏ ∣ X^{pᵉ}` for
  all `k`).
* `coeff_criterion_correct` — the characteristic-free test is exact:
  `Xᵏ ∣ X^{pᵉ} ↔ k ≤ pᵉ`; the true multiplicity is `pᵉ` (`multiplicity_eq_pe`).
* `hasseDeriv_X_pe` — closed form `hasseDeriv j (X^{pᵉ}) = monomial (pᵉ−j) C(pᵉ,j)`.
* `hasseDeriv_intermediate_eq_zero` — **the Kummer collapse**: the Hasse derivative
  vanishes identically for all `0 < j < pᵉ`.
* `hasseDeriv_X_pe_ne_zero_iff` — **the sharp profile**: the Hasse derivative is
  nonzero *iff* `j = 0` or `j = pᵉ`.
* `ordinary_collapses_hasse_survives` — the capstone contrast: the ordinary test
  is blind at every order while the Hasse derivative survives at `pᵉ`, and the
  true multiplicity is exactly `pᵉ`.
* `factorial_annihilates_hasseDeriv` — the obstruction is the factorial:
  `(pᵉ)! • hasseDeriv pᵉ (X^{pᵉ}) = 0` because `(pᵉ)! ≡ 0 (mod p)`.

All results are `0`-axiom, `0`-sorry, over every field of characteristic `p`.
-/

namespace FactorRemainderTheoremOQ01OQ01OQ01OQ01

open Polynomial

variable {K : Type*} [Field K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] (e : ℕ)

/-! ## The ordinary-derivative test collapses over `𝔽_q` -/

/-- `(pᵉ : K) = 0` for `e ≥ 1`, since `p ∣ pᵉ` and `K` has characteristic `p`. -/
theorem pe_cast_eq_zero (he : 1 ≤ e) : ((p ^ e : ℕ) : K) = 0 := by
  rw [CharP.cast_eq_zero_iff K p]
  exact dvd_pow_self p (by omega)

/-- **The ordinary derivative of `X^{pᵉ}` vanishes identically** over a field of
characteristic `p` (`e ≥ 1`): `derivative (X^{pᵉ}) = C(pᵉ)·X^{pᵉ−1} = 0` because
`pᵉ ≡ 0 (mod p)`.  This is the higher Frobenius analogue of the parent's
`derivative (Xᵖ) = 0`. -/
theorem derivative_X_pe_eq_zero (he : 1 ≤ e) :
    derivative ((X : K[X]) ^ (p ^ e)) = 0 := by
  rw [derivative_X_pow, pe_cast_eq_zero e he, map_zero, zero_mul]

/-- Consequently *every* iterated derivative of `X^{pᵉ}` of positive order is `0`. -/
theorem iterate_derivative_X_pe_eq_zero (he : 1 ≤ e) {j : ℕ} (hj : 1 ≤ j) :
    (derivative^[j]) ((X : K[X]) ^ (p ^ e)) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply, derivative_X_pe_eq_zero e he, iterate_derivative_zero]

/-- **The ordinary-derivative criterion is vacuous.** *Every* derivative condition
`(derivative^[j] (X^{pᵉ})).eval 0 = 0` holds — for `j = 0` because `X^{pᵉ}`
evaluates to `0` at `0`, and for `j ≥ 1` because the derivative is `0`.  The
criterion therefore certifies *no* finite multiplicity: it would (falsely) assert
`Xᵏ ∣ X^{pᵉ}` for every `k`. -/
theorem ordinary_criterion_vacuous (he : 1 ≤ e) (j : ℕ) :
    ((derivative^[j]) ((X : K[X]) ^ (p ^ e))).eval 0 = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [Function.iterate_zero, id_eq, eval_pow, eval_X]
    exact zero_pow (pow_pos hp.out.pos e).ne'
  · rw [iterate_derivative_X_pe_eq_zero e he hj, eval_zero]

/-! ## The coefficient / Taylor test stays sharp -/

/-- **The characteristic-free coefficient criterion gives the right multiplicity.**
`Xᵏ ∣ X^{pᵉ} ↔ k ≤ pᵉ`, via `X_pow_dvd_iff` (the `a = 0` Taylor-coefficient test):
the true multiplicity `pᵉ` of the root `0` is detected exactly, in every
characteristic. -/
theorem coeff_criterion_correct (k : ℕ) :
    (X : K[X]) ^ k ∣ (X : K[X]) ^ (p ^ e) ↔ k ≤ p ^ e := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h
    by_contra hk
    push_neg at hk
    have hc := h (p ^ e) (by omega)
    rw [coeff_X_pow, if_pos rfl] at hc
    exact one_ne_zero hc
  · intro hk d hd
    rw [coeff_X_pow, if_neg (by omega)]

/-- The true multiplicity of the root `0` is exactly `pᵉ`: `X^{pᵉ} ∣ X^{pᵉ}` but
`X^{pᵉ+1} ∤ X^{pᵉ}` — in flat contradiction with the vacuous ordinary certificate. -/
theorem multiplicity_eq_pe :
    (X : K[X]) ^ (p ^ e) ∣ (X : K[X]) ^ (p ^ e) ∧
      ¬ (X : K[X]) ^ (p ^ e + 1) ∣ (X : K[X]) ^ (p ^ e) :=
  ⟨dvd_refl _, by rw [coeff_criterion_correct]; omega⟩

/-! ## The Hasse profile: survival only at the two extreme orders -/

/-- **Closed form for the Hasse derivatives of `X^{pᵉ}`.**
`hasseDeriv j (X^{pᵉ}) = monomial (pᵉ − j) (C(pᵉ, j) : K)`, from
`Polynomial.hasseDeriv_monomial`. -/
theorem hasseDeriv_X_pe (j : ℕ) :
    hasseDeriv j ((X : K[X]) ^ (p ^ e)) = monomial (p ^ e - j) (((p ^ e).choose j : K)) := by
  rw [X_pow_eq_monomial, hasseDeriv_monomial, mul_one]

/-- **The sharp Hasse profile.** Over a field of characteristic `p`, the `j`-th Hasse
derivative of `X^{pᵉ}` is nonzero **exactly** at the two extreme orders `j = 0` and
`j = pᵉ`.  The proof reads off the monomial coefficient `(C(pᵉ, j) : K)`, which is
zero iff `p ∣ C(pᵉ, j)` (`CharP.cast_eq_zero_iff`), and `Nat.Prime.dvd_choose_pow_iff`
says this happens iff `j ≠ 0 ∧ j ≠ pᵉ`. -/
theorem hasseDeriv_X_pe_ne_zero_iff (j : ℕ) :
    hasseDeriv j ((X : K[X]) ^ (p ^ e)) ≠ 0 ↔ j = 0 ∨ j = p ^ e := by
  rw [hasseDeriv_X_pe, Ne, monomial_eq_zero_iff, CharP.cast_eq_zero_iff K p,
    hp.out.dvd_choose_pow_iff]
  omega

/-- **The Kummer collapse.** For *every* intermediate order `0 < j < pᵉ` the Hasse
derivative of `X^{pᵉ}` vanishes identically (as a polynomial), because
`p ∣ C(pᵉ, j)`.  This is strictly stronger than the eval-level vanishing that the
ordinary test sees. -/
theorem hasseDeriv_intermediate_eq_zero {j : ℕ} (hj0 : 0 < j) (hjn : j < p ^ e) :
    hasseDeriv j ((X : K[X]) ^ (p ^ e)) = 0 := by
  by_contra h
  rcases (hasseDeriv_X_pe_ne_zero_iff e j).mp h with h0 | hpe <;> omega

/-- **The Hasse derivative survives at the top order.**
`hasseDeriv pᵉ (X^{pᵉ}) = 1` (its only nonzero coefficient is `C(pᵉ, pᵉ) = 1`),
even though the `pᵉ`-th *ordinary* derivative is `0`. -/
theorem hasseDeriv_pe_eq_one :
    hasseDeriv (p ^ e) ((X : K[X]) ^ (p ^ e)) = 1 := by
  rw [hasseDeriv_X_pe, Nat.sub_self, Nat.choose_self, Nat.cast_one, monomial_zero_left, C_1]

/-! ## Capstone: ordinary collapses, Hasse survives -/

/-- **The full failure profile (capstone).** Over any field of characteristic `p`,
for the witness `X^{pᵉ}` (`e ≥ 1`):

* the ordinary-derivative test is **blind at every order** — `(derivative^[j]
  (X^{pᵉ})).eval 0 = 0` for all `j`, so it certifies every multiplicity; yet
* the Hasse derivative **survives at order `pᵉ`** (`hasseDeriv pᵉ (X^{pᵉ}) ≠ 0`);
  and
* the true multiplicity is **exactly `pᵉ`** (`X^{pᵉ} ∣ X^{pᵉ}`, `X^{pᵉ+1} ∤
  X^{pᵉ}`).

This is the arbitrary-finite-field, `p`-power-witness generalisation of the
parent's `Xᵖ`-over-`𝔽ₚ` discrepancy. -/
theorem ordinary_collapses_hasse_survives (he : 1 ≤ e) :
    (∀ j, ((derivative^[j]) ((X : K[X]) ^ (p ^ e))).eval 0 = 0) ∧
      hasseDeriv (p ^ e) ((X : K[X]) ^ (p ^ e)) ≠ 0 ∧
      ((X : K[X]) ^ (p ^ e) ∣ (X : K[X]) ^ (p ^ e) ∧
        ¬ (X : K[X]) ^ (p ^ e + 1) ∣ (X : K[X]) ^ (p ^ e)) :=
  ⟨ordinary_criterion_vacuous e he,
    by rw [hasseDeriv_pe_eq_one]; exact one_ne_zero,
    multiplicity_eq_pe e⟩

/-- **The factorial is exactly the obstruction.** The bridge
`derivative^[k] f = k! • hasseDeriv k f` (`Polynomial.factorial_smul_hasseDeriv`)
makes the discrepancy quantitative: the `pᵉ`-th Hasse derivative is nonzero
(`hasseDeriv_pe_eq_one`), yet scaling it by the factorial annihilates it —
`(pᵉ)! • hasseDeriv pᵉ (X^{pᵉ}) = derivative^[pᵉ] (X^{pᵉ}) = 0` — precisely because
`(pᵉ)! ≡ 0 (mod p)`.  This pinpoints the characteristic-zero hypothesis `k! ≠ 0`
as the exact input the ordinary-derivative test needs and the Hasse test does not. -/
theorem factorial_annihilates_hasseDeriv (he : 1 ≤ e) :
    Nat.factorial (p ^ e) • hasseDeriv (p ^ e) ((X : K[X]) ^ (p ^ e)) = 0 := by
  have h := congrFun (factorial_smul_hasseDeriv (R := K) (k := p ^ e))
    ((X : K[X]) ^ (p ^ e))
  rw [LinearMap.smul_apply] at h
  rw [h]
  exact iterate_derivative_X_pe_eq_zero e he (pow_pos hp.out.pos e)

end FactorRemainderTheoremOQ01OQ01OQ01OQ01

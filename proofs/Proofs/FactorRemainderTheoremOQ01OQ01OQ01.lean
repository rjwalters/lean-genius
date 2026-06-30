import Mathlib

/-!
# Factor–remainder theorem OQ-01-OQ-01-OQ-01:
# the sharp positive-characteristic discrepancy

The parent entry `factor-remainder-theorem-oq-01-oq-01` formalized the
**Taylor-coefficient** multiplicity test

  `(X − a)^k ∣ p ↔ ∀ m < k, (taylor a p).coeff m = 0`,

valid over *any* commutative ring, and noted that over a characteristic-zero
field it is equivalent to the parent's **ordinary-derivative** test
`(X − a)^k ∣ p ↔ p(a) = p′(a) = ⋯ = p^{(k−1)}(a) = 0`, because
`(derivative^[m] p).eval a = m! · (taylor a p).coeff m` and `m! ≠ 0`.

Its **first open question** asks to *make the discrepancy explicit*: exhibit a
polynomial over `𝔽ₚ` for which the ordinary-derivative criterion fails but the
Hasse/Taylor criterion succeeds, "quantifying exactly where the parent's
characteristic-zero hypothesis is needed."

This entry does so with the canonical witness `f = Xᵖ` over `𝔽ₚ = ZMod p`:

* **The ordinary-derivative test collapses.** `derivative (Xᵖ) = 0` identically
  (`derivative_X_pow_eq_zero`), so *every* iterated derivative vanishes and
  *every* derivative condition `(derivative^[j] f).eval 0 = 0` holds
  (`ordinary_criterion_vacuous`). The criterion therefore certifies *no* finite
  multiplicity — it would assert `Xᵏ ∣ Xᵖ` for all `k`, which is false.

* **The coefficient / Taylor test stays sharp.** It is characteristic-free
  (`X_pow_dvd_iff`), so `Xᵏ ∣ Xᵖ ↔ k ≤ p` (`coeff_criterion_correct`): the true
  multiplicity `p` is detected exactly.

* **The Hasse derivative survives where the ordinary one dies.**
  `hasseDeriv p (Xᵖ) ≠ 0` (`hasseDeriv_ne_zero`), yet `derivative^[p] (Xᵖ) = 0`.
  The bridge `derivative^[p] f = p! · hasseDeriv p f` shows the obstruction is
  *exactly* the factorial: `p! • hasseDeriv p (Xᵖ) = 0` because `p! ≡ 0 (mod p)`
  (`factorial_annihilates_hasseDeriv`). This pinpoints `k! ≠ 0` — i.e. the
  characteristic-zero hypothesis — as the precise input the ordinary-derivative
  test needs and the Hasse/Taylor test does not.

`0` axioms.
-/

namespace FactorRemainderTheoremOQ01OQ01OQ01

open Polynomial

variable (p : ℕ) [hp : Fact p.Prime]

/-! ## The ordinary-derivative test collapses over `𝔽ₚ` -/

/-- **The ordinary derivative of `Xᵖ` vanishes identically over `𝔽ₚ`.**
`derivative (Xᵖ) = C(p)·X^{p−1} = 0` since `p ≡ 0 (mod p)`. -/
theorem derivative_X_pow_eq_zero : derivative ((X : (ZMod p)[X]) ^ p) = 0 := by
  rw [derivative_X_pow, ZMod.natCast_self, map_zero, zero_mul]

/-- Consequently *every* iterated derivative of `Xᵖ` (of positive order) is `0`. -/
theorem iterate_derivative_X_pow_eq_zero {j : ℕ} (hj : 1 ≤ j) :
    (derivative^[j]) ((X : (ZMod p)[X]) ^ p) = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [Function.iterate_succ_apply, derivative_X_pow_eq_zero p, iterate_derivative_zero]

/-- **The ordinary-derivative criterion is vacuous.** *Every* derivative
condition `(derivative^[j] (Xᵖ)).eval 0 = 0` holds — for `j = 0` because
`Xᵖ` evaluates to `0` at `0`, and for `j ≥ 1` because the derivative is `0`.
The criterion thus cannot bound the multiplicity: it would (falsely) certify
`Xᵏ ∣ Xᵖ` for every `k`. -/
theorem ordinary_criterion_vacuous (j : ℕ) :
    ((derivative^[j]) ((X : (ZMod p)[X]) ^ p)).eval 0 = 0 := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [Function.iterate_zero, id_eq, eval_pow, eval_X]
    exact zero_pow hp.out.pos.ne'
  · rw [iterate_derivative_X_pow_eq_zero p hj, eval_zero]

/-! ## The coefficient / Taylor test stays sharp -/

/-- **The characteristic-free coefficient criterion gives the right multiplicity.**
`Xᵏ ∣ Xᵖ ↔ k ≤ p`, via `X_pow_dvd_iff` (the `a = 0` Taylor-coefficient test):
the true multiplicity `p` of the root `0` is detected exactly, in every
characteristic. -/
theorem coeff_criterion_correct (k : ℕ) :
    (X : (ZMod p)[X]) ^ k ∣ (X : (ZMod p)[X]) ^ p ↔ k ≤ p := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h
    by_contra hk
    push_neg at hk
    have hpc := h p (by omega)
    rw [coeff_X_pow] at hpc
    simp at hpc
  · intro hk d hd
    rw [coeff_X_pow, if_neg (by omega)]

/-- The true multiplicity is exactly `p`: `Xᵖ ∣ Xᵖ` but `X^{p+1} ∤ Xᵖ` — in
flat contradiction with the vacuous ordinary-derivative certificate. -/
theorem multiplicity_eq_p :
    (X : (ZMod p)[X]) ^ p ∣ (X : (ZMod p)[X]) ^ p ∧
      ¬ (X : (ZMod p)[X]) ^ (p + 1) ∣ (X : (ZMod p)[X]) ^ p :=
  ⟨dvd_refl _, by rw [coeff_criterion_correct]; omega⟩

/-! ## The Hasse derivative survives — and the factorial is the obstruction -/

/-- **The `p`-th Hasse derivative of `Xᵖ` is nonzero**, even though the `p`-th
*ordinary* derivative is `0`. (Its constant coefficient is `C(p,p) = 1 ≠ 0`.) -/
theorem hasseDeriv_ne_zero : hasseDeriv p ((X : (ZMod p)[X]) ^ p) ≠ 0 := by
  intro h
  have hc : (hasseDeriv p ((X : (ZMod p)[X]) ^ p)).coeff 0 = 0 := by rw [h, coeff_zero]
  rw [hasseDeriv_coeff, coeff_X_pow] at hc
  simp [Nat.choose_self] at hc

/-- **The factorial is exactly the obstruction.** The bridge
`derivative^[p] f = p! · hasseDeriv p f` makes the discrepancy quantitative: the
`p`-th Hasse derivative is nonzero (`hasseDeriv_ne_zero`), yet scaling it by the
factorial annihilates it, `p! • hasseDeriv p (Xᵖ) = derivative^[p] (Xᵖ) = 0`,
precisely because `p! ≡ 0 (mod p)`. This is *where* the characteristic-zero
hypothesis `k! ≠ 0` of the ordinary-derivative test is needed. -/
theorem factorial_annihilates_hasseDeriv :
    Nat.factorial p • hasseDeriv p ((X : (ZMod p)[X]) ^ p) = 0 := by
  have h := congrFun (factorial_smul_hasseDeriv (R := ZMod p) (k := p))
    ((X : (ZMod p)[X]) ^ p)
  rw [LinearMap.smul_apply] at h
  rw [h]
  exact iterate_derivative_X_pow_eq_zero p hp.out.one_lt.le

end FactorRemainderTheoremOQ01OQ01OQ01

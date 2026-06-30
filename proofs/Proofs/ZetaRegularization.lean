/-
# Zeta Regularization of Divergent Power Sums  (ζ(-1) = -1/12)

Follow-up to the *Arithmetic Series* gallery entry (open question OQ-03):
the analytic continuation of the Riemann zeta function assigns *finite* values
to the otherwise divergent power-sum series

  1 + 2 + 3 + 4 + ⋯   "="   ζ(-1)  = -1/12,
  1 + 1 + 1 + 1 + ⋯   "="   ζ( 0)  = -1/2,
  1 + 4 + 9 + 16 + ⋯  "="   ζ(-2)  =  0,
  1 + 8 + 27 + 64 + ⋯ "="   ζ(-3)  =  1/120.

These are *not* the limits of the partial sums (which diverge); they are the
values of the analytically continued zeta function at non-positive integers,
the standard "zeta regularization" used in physics (Casimir effect, string
theory) and in Ramanujan summation.

The single structural fact behind every value is Mathlib's
`riemannZeta_neg_nat_eq_bernoulli`:

  ζ(-k) = (-1)^k · B_{k+1} / (k+1),

so each regularized value is a *rational* number determined by a Bernoulli
number.  This file:

* evaluates the four classical values above in closed form (`ζ(-1) = -1/12`
  is the headline);
* proves the infinite family of **trivial zeros**: the regularized sum of
  every even power `∑ n^{2k}` (k ≥ 1) vanishes;
* records the **rationality** of every regularized value.

Everything is a fully verified, axiom-free consequence of Mathlib's analytic
continuation of ζ; the divergent-series interpretation is informal narrative.

## Scope / honesty

The analytic heavy lifting — meromorphic continuation of ζ and the value
formula at negative integers — is Mathlib's.  The contribution here is the
explicit closed-form evaluation of the classical regularized values, the
trivial-zero family stated directly on the power index, and the rationality
corollary.  No new analysis is proved.
-/

import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Tactic

namespace ZetaRegularization

open scoped Real

/-! ## The regularized power sum -/

/-- The zeta-regularized value assigned to the (divergent) power-sum series
`∑ₙ nᵖ`, defined as the analytic continuation `ζ(-p)`.  For `p = 1` this is the
famous "`1 + 2 + 3 + ⋯ = -1/12`". -/
noncomputable def regularizedPowerSum (p : ℕ) : ℂ := riemannZeta (-(p : ℂ))

/-! ## Bernoulli value at 4 (Mathlib only ships `bernoulli'_four`) -/

/-- `B₄ = -1/30`.  Mathlib ships `bernoulli'_four`; the signed Bernoulli number
agrees with the unsigned one away from index `1`. -/
theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

/-! ## Closed-form classical values -/

/-- **ζ(0) = -1/2** — the regularization of `1 + 1 + 1 + ⋯`. -/
theorem regularizedPowerSum_zero : regularizedPowerSum 0 = -1 / 2 := by
  unfold regularizedPowerSum
  simp [riemannZeta_zero]

/-- **ζ(-1) = -1/12** — the regularization of `1 + 2 + 3 + ⋯`.  The headline
identity. -/
theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  rw [Nat.cast_one] at h
  rw [h]
  norm_num [bernoulli_two]

/-- `1 + 2 + 3 + ⋯ = -1/12` in the regularized sense. -/
theorem regularizedPowerSum_one : regularizedPowerSum 1 = -1 / 12 := by
  unfold regularizedPowerSum
  rw [Nat.cast_one]
  exact riemannZeta_neg_one

/-- **ζ(-2) = 0** — the regularization of `1 + 4 + 9 + ⋯`. -/
theorem riemannZeta_neg_two : riemannZeta (-2) = 0 := by
  have h := riemannZeta_neg_two_mul_nat_add_one 0
  norm_num at h
  exact h

/-- **ζ(-3) = 1/120** — the regularization of `1 + 8 + 27 + ⋯`. -/
theorem riemannZeta_neg_three : riemannZeta (-3) = 1 / 120 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 3
  rw [show ((3 : ℕ) : ℂ) = 3 by norm_num] at h
  rw [h, bernoulli_four]
  norm_num

/-! ## The trivial zeros: every even power regularizes to `0` -/

/-- **Trivial zeros.**  For every `k ≥ 1` the regularized sum of the even power
series `∑ₙ n^{2k}` vanishes: `ζ(-2k) = 0`.  An infinite family. -/
theorem regularizedPowerSum_even (k : ℕ) (hk : 0 < k) :
    regularizedPowerSum (2 * k) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  unfold regularizedPowerSum
  have h := riemannZeta_neg_two_mul_nat_add_one n
  convert h using 2
  push_cast
  ring

/-! ## Rationality of every regularized value -/

/-- Every zeta-regularized power sum is a **rational** number, given explicitly
by `(-1)^p · B_{p+1} / (p+1)`. -/
theorem regularizedPowerSum_rational (p : ℕ) :
    ∃ q : ℚ, regularizedPowerSum p = (q : ℂ) := by
  refine ⟨(-1) ^ p * bernoulli (p + 1) / (p + 1), ?_⟩
  unfold regularizedPowerSum
  rw [riemannZeta_neg_nat_eq_bernoulli p]
  push_cast
  ring

/-! ## Sanity: the four classical values, packaged -/

/-- The four classical regularized values in one statement. -/
theorem classical_values :
    regularizedPowerSum 0 = -1 / 2 ∧
    regularizedPowerSum 1 = -1 / 12 ∧
    regularizedPowerSum 2 = 0 ∧
    regularizedPowerSum 3 = 1 / 120 := by
  refine ⟨regularizedPowerSum_zero, regularizedPowerSum_one, ?_, ?_⟩
  · have := regularizedPowerSum_even 1 one_pos
    simpa using this
  · unfold regularizedPowerSum
    rw [show ((3 : ℕ) : ℂ) = 3 by norm_num]
    exact riemannZeta_neg_three

end ZetaRegularization

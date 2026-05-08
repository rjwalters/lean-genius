import Mathlib
import Proofs.AmgmInequalityOQ04OQ01

/-
# Legendre's Relation for Elliptic Integrals

Open Question (OQ-04-OQ-02 from AmgmInequality):
Formalize Legendre's relation for the complete elliptic integrals of the first
and second kind:

  E(k)·K(k') + E(k')·K(k) − K(k)·K(k') = π/2,    for 0 < k < 1,

where k' = √(1 − k²) is the complementary modulus.

## What This File Does

This file is **Session 2 (write Lean stub)** for the problem. It:
1. Reuses `AmgmInequalityOQ04OQ01.ellipticK` (already rigorous, Mathlib intervalIntegral).
2. Defines `ellipticE` rigorously as a Mathlib intervalIntegral.
3. Defines the complementary modulus `complModulus k = √(1 − k²)`.
4. Defines `ellipticK'`, `ellipticE'` as the K, E at the complementary modulus.
5. Proves basic properties: E(0) = π/2, E continuous and integrable, E > 0
   for k² < 1.
6. Axiomatizes the general Legendre relation (deep analytic identity, classical
   19th-century result; proof requires differentiation under the integral and
   the Wronskian of the Legendre ODE — to be eliminated in a future session).
7. Derives the symmetric special case at k = 1/√2:
     2·K(1/√2)·E(1/√2) − K(1/√2)² = π/2
   This is the form taken as an axiom in `AmgmInequalityOQ04OQ05.legendre_relation`,
   so this file **provides infrastructure to eliminate that axiom in a future
   session**.

## Status (this session)

- [x] ellipticE defined as Mathlib interval integral
- [x] E(0) = π/2 proved
- [x] E(1) = 1 proved (boundary value, k = 1)
- [x] Integrand continuous and integrable for all k
- [x] E(k) > 0 for k² < 1 (proved via lower bound)
- [x] complModulus defined; (k')² = 1 − k², k' ≥ 0
- [x] Symmetric Legendre relation derived from the general form
- [x] **Session 4 (ACT)**: infrastructure for dE/dk:
      `dIntegrandE`, pointwise chain rule `integrandE_hasDerivAt_in_k`,
      algebraic split `dIntegrandE_mul_k`, and integral identity
      `integral_dIntegrandE_eq` (yielding ∫₀^{π/2} ∂_k F dθ = (E−K)/k for 0 < k < 1).
- [ ] General Legendre relation: axiomatized (deep — proof requires Mathlib
      derivative-under-the-integral plus Legendre ODE Wronskian; future session)
- [ ] Session 5: assemble `dE_dk : HasDerivAt ellipticE ((E−K)/k) k` by applying
      `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` to the
      Session-4 infrastructure (bound construction + integrability of the bound).

## File Inventory

Sorries: 0
Axioms (this file): 1 — `legendre_relation` (general form, classical result)
Inherits: 1 axiom from `AmgmInequalityOQ04OQ01` (`agm_ellipticK_connection`).

## References

- DLMF §19.7 (https://dlmf.nist.gov/19.7) — Legendre relation 19.7.1.
- Whittaker–Watson, *A Course of Modern Analysis* §22.41 (1927).
- Borwein & Borwein, *Pi and the AGM* (1987), Theorem 1.6.
-/

namespace AmgmInequalityOQ04OQ02

open MeasureTheory intervalIntegral Real
open AmgmInequalityOQ04OQ01 (ellipticK)

-- ============================================================================
-- § 1. The Complete Elliptic Integral E(k) of the Second Kind
-- ============================================================================

/-- The integrand of the complete elliptic integral of the second kind:
    `√(1 − k² sin²θ)`. Defined on all of ℝ via `Real.sqrt`. -/
noncomputable def ellipticIntegrandE (k θ : ℝ) : ℝ :=
  Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)

/-- **Complete Elliptic Integral E(k)** of the second kind defined via Mathlib's
    interval integral:
      E(k) = ∫₀^{π/2} √(1 − k² sin²θ) dθ. -/
noncomputable def ellipticE (k : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..π / 2, ellipticIntegrandE k θ

-- ============================================================================
-- § 2. Basic Properties of the E-Integrand
-- ============================================================================

/-- The E-integrand is nonneg (`Real.sqrt` is). -/
lemma integrandE_nonneg (k θ : ℝ) : 0 ≤ ellipticIntegrandE k θ :=
  Real.sqrt_nonneg _

/-- The E-integrand is bounded above by 1 (since `1 − k² sin²θ ≤ 1`). -/
lemma integrandE_le_one (k θ : ℝ) : ellipticIntegrandE k θ ≤ 1 := by
  unfold ellipticIntegrandE
  have h : 1 - k ^ 2 * Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg k, sq_nonneg (Real.sin θ)]
  calc Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
    _ = 1 := Real.sqrt_one

/-- The E-integrand at k = 0 is identically 1. -/
lemma integrandE_zero_eq_one (θ : ℝ) : ellipticIntegrandE 0 θ = 1 := by
  simp [ellipticIntegrandE, Real.sqrt_one]

/-- For k² < 1 the E-integrand has the positive lower bound `√(1 − k²)`. -/
lemma integrandE_lower_bound (hk : k ^ 2 < 1) (θ : ℝ) :
    Real.sqrt (1 - k ^ 2) ≤ ellipticIntegrandE k θ := by
  unfold ellipticIntegrandE
  apply Real.sqrt_le_sqrt
  have h1 : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have h2 : 0 ≤ k ^ 2 := sq_nonneg k
  nlinarith

/-- The E-integrand is continuous on ℝ for any fixed k. -/
lemma integrandE_continuous (k : ℝ) : Continuous (ellipticIntegrandE k) := by
  unfold ellipticIntegrandE
  refine Real.continuous_sqrt.comp ?_
  refine Continuous.sub continuous_const ?_
  exact (continuous_const.mul (continuous_sin.pow 2))

/-- The E-integrand is interval-integrable on `[0, π/2]` for any k. -/
lemma ellipticE_integrable (k : ℝ) :
    IntervalIntegrable (ellipticIntegrandE k) MeasureTheory.volume 0 (π / 2) :=
  (integrandE_continuous k).intervalIntegrable 0 (π / 2)

-- ============================================================================
-- § 3. Key Values of E
-- ============================================================================

/-- **E(0) = π/2**: the degenerate elliptic integral of the second kind. -/
theorem ellipticE_zero : ellipticE 0 = π / 2 := by
  unfold ellipticE
  simp_rw [integrandE_zero_eq_one]
  rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]

/-- **E(k) > 0** for k² < 1: the integrand has a positive lower bound. -/
theorem ellipticE_pos (hk : k ^ 2 < 1) : 0 < ellipticE k := by
  -- E(k) ≥ ∫₀^{π/2} √(1−k²) dθ = √(1−k²) · (π/2) > 0
  have hπ : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  have hk1 : (0 : ℝ) < 1 - k ^ 2 := by linarith
  have hsqrt_pos : 0 < Real.sqrt (1 - k ^ 2) := Real.sqrt_pos.mpr hk1
  have hlb : (Real.sqrt (1 - k ^ 2)) * (π / 2 - 0) ≤ ellipticE k := by
    have := intervalIntegral.integral_mono_on (a := 0) (b := π / 2)
      (μ := MeasureTheory.volume)
      (f := fun _ => Real.sqrt (1 - k ^ 2))
      (g := ellipticIntegrandE k)
      (le_of_lt hπ)
      ((continuous_const :
        Continuous (fun _ : ℝ => Real.sqrt (1 - k ^ 2))).intervalIntegrable 0 (π / 2))
      (ellipticE_integrable k)
      (fun θ _ => integrandE_lower_bound hk θ)
    have h_int : (π / 2 - 0) * Real.sqrt (1 - k ^ 2) ≤ ellipticE k := by
      simpa [ellipticE, intervalIntegral.integral_const, smul_eq_mul] using this
    have : (π / 2 - 0) * Real.sqrt (1 - k ^ 2)
        = Real.sqrt (1 - k ^ 2) * (π / 2 - 0) := by ring
    linarith [this, h_int]
  have hpos : 0 < Real.sqrt (1 - k ^ 2) * (π / 2 - 0) := by
    have : 0 < Real.sqrt (1 - k ^ 2) * (π / 2) := mul_pos hsqrt_pos hπ
    simpa [sub_zero] using this
  exact lt_of_lt_of_le hpos hlb

/-- **E(1) = 1**: the boundary modulus value.

    For `k = 1` the integrand reduces to `√(cos²θ) = cos θ` on `[0, π/2]`
    (using `sin²θ + cos²θ = 1` and `cos θ ≥ 0` on this interval).
    Hence `E(1) = ∫₀^{π/2} cos θ dθ = sin(π/2) − sin 0 = 1`.

    Together with `ellipticE_zero` (E(0) = π/2), this pins down the boundary
    values of E on the canonical modulus interval [0, 1]. Reference: DLMF §19.6.1. -/
theorem ellipticE_one : ellipticE 1 = 1 := by
  unfold ellipticE
  -- Step 1: rewrite the integrand to `cos θ` on [0, π/2].
  have h_eq : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      ellipticIntegrandE 1 θ = Real.cos θ := by
    intro θ hθ
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos] : (0 : ℝ) ≤ π / 2)] at hθ
    obtain ⟨hθ0, hθ1⟩ := hθ
    have h_cos_nn : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ1⟩
    unfold ellipticIntegrandE
    have h_id : (1 : ℝ) - 1 ^ 2 * Real.sin θ ^ 2 = Real.cos θ ^ 2 := by
      linear_combination -Real.sin_sq_add_cos_sq θ
    rw [h_id, Real.sqrt_sq_eq_abs, abs_of_nonneg h_cos_nn]
  rw [intervalIntegral.integral_congr h_eq]
  -- Step 2: apply FTC with antiderivative `sin`.
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      HasDerivAt Real.sin (Real.cos θ) θ := fun θ _ => Real.hasDerivAt_sin θ
  rw [integral_eq_sub_of_hasDerivAt hderiv
      (continuous_cos.intervalIntegrable _ _)]
  rw [Real.sin_pi_div_two, Real.sin_zero]; norm_num

-- ============================================================================
-- § 4. The Complementary Modulus
-- ============================================================================

/-- The **complementary modulus** k' = √(1 − k²). -/
noncomputable def complModulus (k : ℝ) : ℝ := Real.sqrt (1 - k ^ 2)

/-- The complementary modulus is nonneg. -/
lemma complModulus_nonneg (k : ℝ) : 0 ≤ complModulus k := Real.sqrt_nonneg _

/-- For k² < 1, the complementary modulus is positive. -/
lemma complModulus_pos (hk : k ^ 2 < 1) : 0 < complModulus k :=
  Real.sqrt_pos.mpr (by linarith)

/-- The Pythagorean identity for the modulus: (k')² = 1 − k² for k² ≤ 1. -/
lemma complModulus_sq (hk : k ^ 2 ≤ 1) : (complModulus k) ^ 2 = 1 - k ^ 2 := by
  unfold complModulus
  rw [sq, Real.mul_self_sqrt (by linarith)]

/-- For k² < 1, the complementary modulus also satisfies (k')² < 1. -/
lemma complModulus_sq_lt_one (hk1 : 0 < k ^ 2) (hk2 : k ^ 2 < 1) :
    (complModulus k) ^ 2 < 1 := by
  rw [complModulus_sq (le_of_lt hk2)]; linarith

/-- The complementary modulus is involutive on the open interval k² < 1, k ≥ 0:
    k'' = k. -/
lemma complModulus_complModulus (hk : 0 ≤ k) (hk1 : k ^ 2 ≤ 1) :
    complModulus (complModulus k) = k := by
  unfold complModulus
  rw [sq, Real.mul_self_sqrt (by linarith), sub_sub_cancel]
  exact Real.sqrt_sq hk

-- ============================================================================
-- § 5. K and E at the Complementary Modulus
-- ============================================================================

/-- The **complementary K**: `K'(k) := K(k')`. -/
noncomputable def ellipticK' (k : ℝ) : ℝ := ellipticK (complModulus k)

/-- The **complementary E**: `E'(k) := E(k')`. -/
noncomputable def ellipticE' (k : ℝ) : ℝ := ellipticE (complModulus k)

/-- For 0 < k² < 1, the complementary K is positive. -/
lemma ellipticK'_pos (hk1 : 0 < k ^ 2) (hk2 : k ^ 2 < 1) : 0 < ellipticK' k :=
  AmgmInequalityOQ04OQ01.ellipticK_pos (complModulus_sq_lt_one hk1 hk2)

/-- For 0 < k² < 1, the complementary E is positive. -/
lemma ellipticE'_pos (hk1 : 0 < k ^ 2) (hk2 : k ^ 2 < 1) : 0 < ellipticE' k :=
  ellipticE_pos (complModulus_sq_lt_one hk1 hk2)

-- ============================================================================
-- § 6. Legendre's Relation (axiomatized — deep classical analysis)
-- ============================================================================

/-
Legendre's relation (NIST DLMF 19.7.1, Whittaker–Watson §22.41):

  For 0 < k < 1,    E(k)·K(k') + E(k')·K(k) − K(k)·K(k') = π/2.

A standard proof uses:
1. The Legendre ODE for K(k) and E(k) in the modulus k.
2. The Wronskian of K(k) and K'(k) viewed as solutions of related ODEs.
3. Pinning down the constant π/2 by a boundary value (e.g. k → 0⁺ where
   K → π/2 and E → π/2 while K(k') → ∞ but the bracketed combination tends
   to π/2).

This requires **differentiation under the integral sign** plus careful limits,
both of which are present in Mathlib (`MeasureTheory.intervalIntegral.deriv_*`)
but not yet wired up to `ellipticK`. We therefore axiomatize the relation here
and target a fully constructive proof in a future session.
-/

/-- **Legendre's Relation** (axiomatized).

For all `k` with `0 < k < 1`:
  `ellipticE k · ellipticK' k + ellipticE' k · ellipticK k − ellipticK k · ellipticK' k = π/2`. -/
axiom legendre_relation (k : ℝ) (hk0 : 0 < k) (hk1 : k < 1) :
    ellipticE k * ellipticK' k + ellipticE' k * ellipticK k
      - ellipticK k * ellipticK' k = π / 2

-- ============================================================================
-- § 7. Symmetric Special Case: k = 1/√2
-- ============================================================================

/-
At k = 1/√2 the complementary modulus equals the modulus itself: k' = k.
Hence K(k') = K(k) and E(k') = E(k), and Legendre's relation collapses to the
**symmetric form** `2·K·E − K² = π/2` which is the form axiomatized in
`AmgmInequalityOQ04OQ05.legendre_relation`.

Future session goal: replace the OQ04OQ05 axiom with this corollary
(import `AmgmInequalityOQ04OQ02` and discharge that file's axiom from this
file's general result).
-/

private lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 :=
  Real.sqrt_pos.mpr (by norm_num)

private lemma one_div_sqrt_two_sq : ((1 : ℝ) / Real.sqrt 2) ^ 2 = 1 / 2 := by
  rw [div_pow, one_pow, sq, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]

private lemma one_div_sqrt_two_pos : (0 : ℝ) < 1 / Real.sqrt 2 := by
  have h := sqrt_two_pos; positivity

private lemma one_div_sqrt_two_lt_one : (1 : ℝ) / Real.sqrt 2 < 1 := by
  rw [div_lt_one sqrt_two_pos]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- At k = 1/√2 the complementary modulus equals the modulus itself. -/
theorem complModulus_symmetric :
    complModulus (1 / Real.sqrt 2) = 1 / Real.sqrt 2 := by
  unfold complModulus
  rw [show (1 : ℝ) - (1 / Real.sqrt 2) ^ 2 = (1 / Real.sqrt 2) ^ 2 by
        rw [one_div_sqrt_two_sq]; norm_num]
  exact Real.sqrt_sq one_div_sqrt_two_pos.le

/-- **Symmetric Legendre Relation** at k = 1/√2:
    2·K(1/√2)·E(1/√2) − K(1/√2)² = π/2.

This matches the form axiomatized in `AmgmInequalityOQ04OQ05.legendre_relation`
and is derivable from `legendre_relation` applied at k = 1/√2 using
`complModulus_symmetric`. -/
theorem legendre_relation_symmetric :
    2 * ellipticK (1 / Real.sqrt 2) * ellipticE (1 / Real.sqrt 2)
      - (ellipticK (1 / Real.sqrt 2)) ^ 2 = π / 2 := by
  have h := legendre_relation (1 / Real.sqrt 2)
    one_div_sqrt_two_pos one_div_sqrt_two_lt_one
  unfold ellipticK' ellipticE' at h
  rw [complModulus_symmetric] at h
  -- h : E(k₀)·K(k₀) + E(k₀)·K(k₀) − K(k₀)·K(k₀) = π/2  where k₀ = 1/√2
  -- goal : 2·K(k₀)·E(k₀) − K(k₀)² = π/2
  linear_combination h

-- ============================================================================
-- § 8. Partial Derivative ∂_k F_E and the Integral Identity ∫ ∂_k F = (E−K)/k
-- (Infrastructure for `dE_dk`; see session report S4.)
-- ============================================================================

/-
The Legendre-relation programme requires `dE/dk = (E − K)/k`, proved by
differentiation under the integral sign via
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. This
section provides the gallery-side ingredients that feed that lemma:

1. `dIntegrandE`: the partial derivative `∂_k F_E = −k sin²θ / √(1 − k² sin²θ)`.
2. `dIntegrandE_continuous`, `dIntegrandE_integrable`: regularity for `k² < 1`.
3. `integrandE_hasDerivAt_in_k`: the pointwise chain-rule fact that, for fixed
   θ and `k² < 1`, `κ ↦ √(1 − κ² sin²θ)` has derivative `dIntegrandE k θ` at `k`
   (one of the seven hypotheses of the Mathlib lemma).
4. `dIntegrandE_mul_k`: the algebraic identity
   `k · dIntegrandE k θ = ellipticIntegrandE k θ − ellipticIntegrand k θ`,
   the core split that converts `∫ ∂_k F` to `(E − K)/k`.
5. `integral_dIntegrandE_eq`: the integral identity itself.

Session 5 will combine (2)–(5) with a uniform bound to invoke the Mathlib lemma
and conclude `HasDerivAt ellipticE ((ellipticE k − ellipticK k)/k) k`.
-/

/-- The partial derivative of the E-integrand with respect to k:
    `∂/∂k √(1 − k² sin²θ) = −k sin²θ / √(1 − k² sin²θ)`. -/
noncomputable def dIntegrandE (k θ : ℝ) : ℝ :=
  -(k * Real.sin θ ^ 2) / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)

/-- For `k² < 1` the partial-derivative integrand is continuous in θ. -/
lemma dIntegrandE_continuous (hk : k ^ 2 < 1) :
    Continuous (dIntegrandE k) := by
  unfold dIntegrandE
  refine Continuous.div₀ ?_ ?_ ?_
  · -- numerator: −(k · sin²θ)
    exact ((continuous_const.mul (continuous_sin.pow 2)).neg)
  · -- denominator: √(1 − k² sin²θ)
    refine Real.continuous_sqrt.comp ?_
    refine Continuous.sub continuous_const ?_
    exact (continuous_const.mul (continuous_sin.pow 2))
  · intro θ
    exact (AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ).ne'

/-- For `k² < 1` the partial-derivative integrand is interval-integrable
    on `[0, π/2]`. -/
lemma dIntegrandE_integrable (hk : k ^ 2 < 1) :
    IntervalIntegrable (dIntegrandE k) MeasureTheory.volume 0 (π / 2) :=
  (dIntegrandE_continuous hk).intervalIntegrable 0 (π / 2)

/-- **Pointwise chain rule** (one of the 7 hypotheses for the Mathlib
    differentiation-under-the-integral lemma).

    For fixed θ and `k² < 1`, the map `κ ↦ √(1 − κ² sin²θ)` has derivative
    `−k sin²θ / √(1 − k² sin²θ) = dIntegrandE k θ` at `k`. -/
lemma integrandE_hasDerivAt_in_k (hk : k ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun κ : ℝ => ellipticIntegrandE κ θ) (dIntegrandE k θ) k := by
  have h_pos : (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 :=
    (AmgmInequalityOQ04OQ01.denom_pos hk θ).ne'
  have hs_ne : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 :=
    (AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ).ne'
  -- Inner function f(κ) = 1 − κ² sin²θ has derivative f'(κ) = −2 κ sin²θ.
  have h_inner : HasDerivAt (fun κ : ℝ => 1 - κ ^ 2 * Real.sin θ ^ 2)
      (-(2 * k * Real.sin θ ^ 2)) k := by
    have h_pow' : HasDerivAt (fun κ : ℝ => κ ^ 2) (2 * k) k := by
      simpa using hasDerivAt_pow 2 k
    have h_mul : HasDerivAt (fun κ : ℝ => κ ^ 2 * Real.sin θ ^ 2)
        (2 * k * Real.sin θ ^ 2) k := h_pow'.mul_const _
    have h_sub : HasDerivAt (fun κ : ℝ => 1 - κ ^ 2 * Real.sin θ ^ 2)
        (0 - 2 * k * Real.sin θ ^ 2) k :=
      (hasDerivAt_const k (1 : ℝ)).sub h_mul
    simpa using h_sub
  -- Chain rule for sqrt: HasDerivAt.sqrt requires `f x ≠ 0`.
  have h_sqrt := h_inner.sqrt h_pos
  -- h_sqrt : HasDerivAt (fun κ => √(1 − κ²·sin²θ))
  --                     (−(2 k sin²θ) / (2·√(1 − k²·sin²θ))) k
  -- Goal after unfolding `ellipticIntegrandE`: same function arg as h_sqrt.
  show HasDerivAt (fun κ : ℝ => Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2))
        (dIntegrandE k θ) k
  -- Reduce the deriv expression to match h_sqrt's deriv.
  have h_eq_deriv : -(2 * k * Real.sin θ ^ 2)
        / (2 * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
      = dIntegrandE k θ := by
    unfold dIntegrandE
    field_simp
  rw [← h_eq_deriv]
  exact h_sqrt

/-- **Algebraic split** (the core of the integral identity).

    For `k² < 1`,
    `k · dIntegrandE k θ = ellipticIntegrandE k θ − ellipticIntegrand k θ`,
    where `ellipticIntegrand k θ = 1/√(1 − k² sin²θ)` is the K-integrand and
    `ellipticIntegrandE k θ = √(1 − k² sin²θ)` is the E-integrand.

    Proof: using `s² = 1 − k² sin²θ` (where `s := √(1 − k² sin²θ) > 0`),
    multiplying both sides by `s` gives `−k² sin²θ = s² − 1`, which is exactly
    the Pythagorean identity `s² = 1 − k² sin²θ` rearranged. -/
lemma dIntegrandE_mul_k (hk : k ^ 2 < 1) (θ : ℝ) :
    k * dIntegrandE k θ
      = ellipticIntegrandE k θ - AmgmInequalityOQ04OQ01.ellipticIntegrand k θ := by
  unfold dIntegrandE ellipticIntegrandE AmgmInequalityOQ04OQ01.ellipticIntegrand
  have hs_pos : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
    AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ
  have hs_ne : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := hs_pos.ne'
  have hs_sq : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        = 1 - k ^ 2 * Real.sin θ ^ 2 :=
    Real.mul_self_sqrt (le_of_lt (AmgmInequalityOQ04OQ01.denom_pos hk θ))
  field_simp
  linear_combination -hs_sq

/-- **Integral identity for `dE/dk`** (the post-application target).

    For `0 < k < 1`,
    `∫₀^{π/2} dIntegrandE k θ dθ = (ellipticE k − ellipticK k) / k`.

    This is the form that the conclusion of
    `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` must be
    rewritten into — once the lemma gives
    `HasDerivAt ellipticE (∫ dIntegrandE k θ dθ) k`, applying this identity
    yields the stated `dE/dk` formula. -/
theorem integral_dIntegrandE_eq (hk_pos : 0 < k) (hk_lt : k < 1) :
    ∫ θ in (0 : ℝ)..π / 2, dIntegrandE k θ
      = (ellipticE k - ellipticK k) / k := by
  have hk_sq : k ^ 2 < 1 := by nlinarith
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  -- Pointwise: dIntegrandE k θ = (E_int − K_int) / k.
  have h_eq : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      dIntegrandE k θ
        = (ellipticIntegrandE k θ
            - AmgmInequalityOQ04OQ01.ellipticIntegrand k θ) / k := by
    intro θ _
    have h_mul : k * dIntegrandE k θ
        = ellipticIntegrandE k θ
          - AmgmInequalityOQ04OQ01.ellipticIntegrand k θ :=
      dIntegrandE_mul_k hk_sq θ
    field_simp
    linear_combination h_mul
  rw [intervalIntegral.integral_congr h_eq]
  rw [intervalIntegral.integral_div]
  congr 1
  rw [intervalIntegral.integral_sub (ellipticE_integrable k)
        (AmgmInequalityOQ04OQ01.ellipticK_integrable hk_sq)]
  rfl

end AmgmInequalityOQ04OQ02

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

/-- **Chain rule for the complementary modulus.**

    For `k² < 1`, the complementary modulus `k' := √(1 − k²)` is differentiable
    in `k` with derivative `−k / k'`. Mirrors `integrandE_hasDerivAt_in_k`
    (§8, with the `θ` parameter dropped): chain rule on the inner polynomial
    `1 − k²` (derivative `−2k`), `HasDerivAt.sqrt` using `1 − k² ≠ 0`, then
    reduce the native quotient `−(2k) / (2 · √(1 − k²))` to `−k / k'` via
    `field_simp`.

    This is the missing K-side ingredient (alongside the eventually-assembled
    `dE_dk` and `dK_dk`) for the S11 Wronskian closure: the complementary
    elliptic integrals `K(k')` and `E(k')` then differentiate by composition
    `(d/dk) ellipticK' k = (d/dk') ellipticK k' · (−k / k')`. -/
lemma complModulus_hasDerivAt (hk : k ^ 2 < 1) :
    HasDerivAt complModulus (-k / complModulus k) k := by
  unfold complModulus
  -- Inner: f(κ) = 1 − κ²; f'(κ) = −2κ.
  have h_inner : HasDerivAt (fun κ : ℝ => 1 - κ ^ 2) (-(2 * k)) k := by
    have h_pow : HasDerivAt (fun κ : ℝ => κ ^ 2) (2 * k) k := by
      simpa using hasDerivAt_pow 2 k
    have h_sub : HasDerivAt (fun κ : ℝ => 1 - κ ^ 2) (0 - 2 * k) k :=
      (hasDerivAt_const k (1 : ℝ)).sub h_pow
    simpa using h_sub
  -- 1 − k² ≠ 0 since k² < 1 implies 1 − k² > 0.
  have h_ne : (1 : ℝ) - k ^ 2 ≠ 0 :=
    (show (0 : ℝ) < 1 - k ^ 2 by linarith).ne'
  -- Chain rule for sqrt: HasDerivAt.sqrt requires the inner ≠ 0.
  have h_sqrt := h_inner.sqrt h_ne
  -- h_sqrt : HasDerivAt (fun κ => √(1 − κ²)) (−(2k) / (2 · √(1 − k²))) k
  have h_sqrt_ne : Real.sqrt (1 - k ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  -- Reduce the deriv expression to match h_sqrt's deriv.
  have h_eq_deriv : -(2 * k) / (2 * Real.sqrt (1 - k ^ 2))
      = -k / Real.sqrt (1 - k ^ 2) := by
    field_simp
  rw [← h_eq_deriv]
  exact h_sqrt


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

-- ============================================================================
-- § 9. Uniform Bound for `dIntegrandE` (Infrastructure for the Mathlib
--      differentiation-under-the-integral lemma)
-- ============================================================================

/-
The lemma `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
requires an integrable bound on `|F'(κ, θ)|` uniform over a neighborhood of
the base point `κ = k`. This section provides that bound.

Concretely: pick `M` with `k < M < 1` (so the open interval `(-M, M)` is a
neighborhood of `k`). On `|κ| ≤ M`,

    |dIntegrandE κ θ|  =  |κ| · sin²θ / √(1 − κ² sin²θ)
                       ≤  M · sin²θ / √(1 − M² sin²θ)
                       =: boundDIntegrandE M θ.

The right-hand side is continuous and interval-integrable on `[0, π/2]`,
giving the `h_bound` and `bound_integrable` ingredients for Session 6.
-/

/-- The dominating bound for `|dIntegrandE κ θ|` on the band `|κ| ≤ M`:
    `M · sin²θ / √(1 − M² sin²θ)`.

    Mirrors `dIntegrandE` but with the sign stripped (positive form) and `κ`
    replaced by `M` everywhere — designed to give a uniform integrable upper
    bound on `|dIntegrandE κ θ|` for `κ` in a closed band, which is the
    `h_bound` hypothesis of
    `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
noncomputable def boundDIntegrandE (M θ : ℝ) : ℝ :=
  M * Real.sin θ ^ 2 / Real.sqrt (1 - M ^ 2 * Real.sin θ ^ 2)

/-- For `M² < 1` the bound function is continuous in `θ`. -/
lemma boundDIntegrandE_continuous (hM : M ^ 2 < 1) :
    Continuous (boundDIntegrandE M) := by
  unfold boundDIntegrandE
  refine Continuous.div₀ ?_ ?_ ?_
  · -- numerator: `M · sin²θ`
    exact continuous_const.mul (continuous_sin.pow 2)
  · -- denominator: `√(1 − M² sin²θ)`
    refine Real.continuous_sqrt.comp ?_
    refine Continuous.sub continuous_const ?_
    exact continuous_const.mul (continuous_sin.pow 2)
  · intro θ
    exact (AmgmInequalityOQ04OQ01.sqrt_denom_pos hM θ).ne'

/-- For `M² < 1` the bound function is interval-integrable on `[0, π/2]`. -/
lemma boundDIntegrandE_integrable (hM : M ^ 2 < 1) :
    IntervalIntegrable (boundDIntegrandE M) MeasureTheory.volume 0 (π / 2) :=
  (boundDIntegrandE_continuous hM).intervalIntegrable 0 (π / 2)

/-- **Uniform bound** on `|dIntegrandE|` over the band `|κ| ≤ M`.

    For `0 ≤ M` with `M² < 1` and any `κ` satisfying `κ² ≤ M²`,
    `|dIntegrandE κ θ| ≤ boundDIntegrandE M θ` for every `θ`.

    This is the pointwise content of the `h_bound` hypothesis of
    `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The
    Session-6 task is then to package this together with the `dIntegrandE`
    facts from §8 (continuity, integrability, pointwise differentiability)
    and the integrability of `boundDIntegrandE` to apply that lemma at any
    `0 < k < 1` (e.g. with `M = (k + 1) / 2`), yielding
    `HasDerivAt ellipticE ((E(k) − K(k)) / k) k`. -/
lemma dIntegrandE_abs_le_bound
    (hM : M ^ 2 < 1) (hM_nn : 0 ≤ M) (κ θ : ℝ) (hκ : κ ^ 2 ≤ M ^ 2) :
    |dIntegrandE κ θ| ≤ boundDIntegrandE M θ := by
  unfold dIntegrandE boundDIntegrandE
  have hsin2_nn : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hκ_sq_lt : κ ^ 2 < 1 := lt_of_le_of_lt hκ hM
  have hM_sqrt_pos : 0 < Real.sqrt (1 - M ^ 2 * Real.sin θ ^ 2) :=
    AmgmInequalityOQ04OQ01.sqrt_denom_pos hM θ
  have hκ_sqrt_pos : 0 < Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) :=
    AmgmInequalityOQ04OQ01.sqrt_denom_pos hκ_sq_lt θ
  -- |κ| ≤ M from κ² ≤ M² and 0 ≤ M (via `Real.sqrt`).
  have habs_κ : |κ| ≤ M := by
    have h1 : Real.sqrt (κ ^ 2) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hκ
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hM_nn] at h1
  -- Compute |·| on the LHS.
  have h_num : |-(κ * Real.sin θ ^ 2)| = |κ| * Real.sin θ ^ 2 := by
    rw [abs_neg, abs_mul, abs_of_nonneg hsin2_nn]
  have h_denom : |Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2)|
      = Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) :=
    abs_of_pos hκ_sqrt_pos
  rw [abs_div, h_num, h_denom]
  -- Goal: |κ| · sin²θ / √(1 − κ² sin²θ) ≤ M · sin²θ / √(1 − M² sin²θ).
  apply div_le_div
  · exact mul_nonneg hM_nn hsin2_nn
  · exact mul_le_mul_of_nonneg_right habs_κ hsin2_nn
  · exact hM_sqrt_pos
  · apply Real.sqrt_le_sqrt
    nlinarith [hsin2_nn, hκ]

-- ============================================================================
-- § 10. Partial Derivative ∂_k F_K and Chain-Rule Infrastructure for `dK_dk`
-- (K-side analog of §8; mirrors §8's `dIntegrandE` work for the K-integrand.)
-- ============================================================================

/-
The Whittaker–Watson §22.41 Wronskian proof of Legendre's relation needs
both `dE/dk = (E − K)/k` and `dK/dk = (E − (1−k²)K) / (k(1−k²))`. §8 set
up the chain-rule + algebraic-split + integral-identity infrastructure
for the E side. This section provides the **chain-rule infrastructure**
for the K side — the K-analog of §8's `dIntegrandE`,
`dIntegrandE_continuous`, `dIntegrandE_integrable`,
`integrandE_hasDerivAt_in_k`.

Specifically:

1. `dIntegrandK k θ := k sin²θ / [(1 − k² sin²θ) · √(1 − k² sin²θ)]` — the
   partial derivative of the K-integrand `1/√(1 − k² sin²θ)` with respect
   to `k`. (The denominator `(1 − u) · √(1 − u) = (1 − u)^{3/2}` matches
   the form produced by `HasDerivAt.div` applied to `1` over
   `√(1 − κ² sin²θ)`, avoiding any `Real.rpow` rewriting.)
2. `dIntegrandK_continuous (hk : k² < 1)`, `dIntegrandK_integrable (hk : k² < 1)`
   — regularity for `k² < 1`, by the same `Continuous.div₀` template as §8.
3. `integrandK_hasDerivAt_in_k (hk : k² < 1) (θ : ℝ)` — the pointwise chain
   rule: `HasDerivAt (κ ↦ ellipticIntegrand κ θ) (dIntegrandK k θ) k`. This
   is one of the seven hypotheses of
   `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

A future session will add the K-side **algebraic split** and **integral
identity** (the K-analog of §8's `dIntegrandE_mul_k` /
`integral_dIntegrandE_eq`), then a uniform bound (the K-analog of §9), then
assemble `dK_dk : HasDerivAt ellipticK ((E(k) − (1−k²) K(k))/(k(1−k²))) k`
via the Mathlib parametric-integral lemma. The K-side algebraic split is
**not** pointwise (a difference from §8); it requires integration by parts
on `∫ k sin²θ (1 − k² sin²θ)^{−3/2} dθ`. That work is deferred.
-/

/-- The partial derivative of the K-integrand with respect to k:
    `∂/∂k (1 − k² sin²θ)^{−1/2} = k sin²θ · (1 − k² sin²θ)^{−3/2}`.

    Written in the `(1 − u) · √(1 − u)` form (rather than `(1 − u)^{3/2}`)
    to match the result of `HasDerivAt.div` applied to `(fun _ => 1)` over
    `(fun κ => √(1 − κ² sin²θ))` — see `integrandK_hasDerivAt_in_k`. -/
noncomputable def dIntegrandK (k θ : ℝ) : ℝ :=
  k * Real.sin θ ^ 2 /
    ((1 - k ^ 2 * Real.sin θ ^ 2) * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))

/-- For `k² < 1` the K-derivative integrand is continuous in θ. -/
lemma dIntegrandK_continuous (hk : k ^ 2 < 1) :
    Continuous (dIntegrandK k) := by
  unfold dIntegrandK
  refine Continuous.div₀ ?_ ?_ ?_
  · -- numerator: `k · sin²θ`
    exact continuous_const.mul (continuous_sin.pow 2)
  · -- denominator: `(1 − k²·sin²θ) · √(1 − k²·sin²θ)`
    have h_inner : Continuous (fun θ : ℝ => 1 - k ^ 2 * Real.sin θ ^ 2) :=
      Continuous.sub continuous_const
        (continuous_const.mul (continuous_sin.pow 2))
    exact h_inner.mul (Real.continuous_sqrt.comp h_inner)
  · intro θ
    have hp : 0 < 1 - k ^ 2 * Real.sin θ ^ 2 :=
      AmgmInequalityOQ04OQ01.denom_pos hk θ
    have hsp : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
      AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ
    exact (mul_pos hp hsp).ne'

/-- For `k² < 1` the K-derivative integrand is interval-integrable on `[0, π/2]`. -/
lemma dIntegrandK_integrable (hk : k ^ 2 < 1) :
    IntervalIntegrable (dIntegrandK k) MeasureTheory.volume 0 (π / 2) :=
  (dIntegrandK_continuous hk).intervalIntegrable 0 (π / 2)

/-- **Pointwise chain rule** for the K-integrand (one of the seven hypotheses
    for the Mathlib differentiation-under-the-integral lemma).

    For fixed θ and `k² < 1`, the map `κ ↦ 1/√(1 − κ² sin²θ)` has derivative
    `k sin²θ / [(1 − k² sin²θ) · √(1 − k² sin²θ)] = dIntegrandK k θ` at `k`.

    Proof sketch: chain rule on the inner polynomial `1 − κ² sin²θ`
    (derivative `−2κ sin²θ`); `HasDerivAt.sqrt` on the result (using
    positivity of the inner); then `HasDerivAt.div` of the constant `1`
    over `√(1 − κ² sin²θ)` and an algebraic reduction using
    `Real.mul_self_sqrt` on the denominator. -/
lemma integrandK_hasDerivAt_in_k (hk : k ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun κ : ℝ => AmgmInequalityOQ04OQ01.ellipticIntegrand κ θ)
        (dIntegrandK k θ) k := by
  have h_pos : 0 < 1 - k ^ 2 * Real.sin θ ^ 2 :=
    AmgmInequalityOQ04OQ01.denom_pos hk θ
  have h_pos_ne : (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := h_pos.ne'
  have hs_pos : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
    AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ
  have hs_ne : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := hs_pos.ne'
  -- Inner: f(κ) = 1 − κ² sin²θ, f'(k) = −2k sin²θ.
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
  -- Outer sqrt: HasDerivAt (κ ↦ √(1 − κ² sin²θ)) (...) k.
  have h_sqrt := h_inner.sqrt h_pos_ne
  -- One: HasDerivAt (fun _ => 1) 0 k.
  have h_one : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 k := hasDerivAt_const k 1
  -- Quotient: HasDerivAt (κ ↦ 1 / √(1 − κ² sin²θ)) (...) k.
  have h_div := h_one.div h_sqrt hs_ne
  -- Reduce h_div's derivative expression to `dIntegrandK k θ`.
  show HasDerivAt (fun κ : ℝ => 1 / Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2))
      (dIntegrandK k θ) k
  have h_eq_deriv :
      (0 * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
          - 1 * (-(2 * k * Real.sin θ ^ 2)
                  / (2 * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))))
        / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 2
      = dIntegrandK k θ := by
    unfold dIntegrandK
    have hsq : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 2
        = 1 - k ^ 2 * Real.sin θ ^ 2 := by
      rw [sq, Real.mul_self_sqrt h_pos.le]
    rw [hsq]
    field_simp
    ring
  rw [← h_eq_deriv]
  -- The unfold of ellipticIntegrand gives `1 / √(1 − κ² sin²θ)`.
  show HasDerivAt
      (fun κ : ℝ => AmgmInequalityOQ04OQ01.ellipticIntegrand κ θ) _ k
  unfold AmgmInequalityOQ04OQ01.ellipticIntegrand
  exact h_div

-- ============================================================================
-- § 11. Uniform Bound for `dIntegrandK` (K-side analog of §9)
-- ============================================================================

/-
The K-side counterpart of §9. To apply
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` for
`ellipticK` we need an integrable function `boundDIntegrandK M θ` that
majorizes `|dIntegrandK κ θ|` uniformly for `|κ| ≤ M`. This section
provides exactly that infrastructure, mirroring §9 line for line.

The bound is

    boundDIntegrandK M θ
      :=  M · sin²θ / [(1 − M² sin²θ) · √(1 − M² sin²θ)],

obtained from `dIntegrandK κ θ = κ sin²θ / [(1 − κ²sin²θ) √(1 − κ²sin²θ)]`
by replacing every `κ` with `M`. For `|κ| ≤ M < 1`:

* numerator  `|κ| · sin²θ ≤ M · sin²θ`  (since `|κ| ≤ M`, `sin²θ ≥ 0`);
* denominator factor `(1 − M² sin²θ) ≤ (1 − κ² sin²θ)` (from `κ² ≤ M²`);
* so `√(1 − M² sin²θ) ≤ √(1 − κ² sin²θ)`, and hence the product
  `(1 − M² sin²θ) · √(1 − M² sin²θ) ≤ (1 − κ² sin²θ) · √(1 − κ² sin²θ)`.

The two displayed inequalities feed `div_le_div`. The denominator on the
M-side is positive (we only use the bound for `M² < 1`), so the quotient
inequality is well-formed.

This section is the K-side precondition for the future `dK_dk` assembly,
which will follow the same template as the (still-open) `dE_dk` work in
§10/PR #17371. Once the K-side algebraic split + integral identity (the
non-pointwise IBP step) is also in place, `dK_dk` can be assembled in a
parallel session.
-/

/-- Dominating bound for `|dIntegrandK κ θ|` on the band `|κ| ≤ M`:
    `M · sin²θ / [(1 − M² sin²θ) · √(1 − M² sin²θ)]`.

    Mirrors `dIntegrandK` with `κ` replaced by `M` everywhere — designed
    to give a uniform integrable upper bound on `|dIntegrandK κ θ|` for
    `κ` in a closed band. The denominator is the same `(1 − u) · √(1 − u)`
    form as `dIntegrandK` itself (§10), so the two pieces compose
    naturally in `dIntegrandK_abs_le_bound`. -/
noncomputable def boundDIntegrandK (M θ : ℝ) : ℝ :=
  M * Real.sin θ ^ 2 /
    ((1 - M ^ 2 * Real.sin θ ^ 2) * Real.sqrt (1 - M ^ 2 * Real.sin θ ^ 2))

/-- For `M² < 1` the K-side bound function is continuous in `θ`. -/
lemma boundDIntegrandK_continuous (hM : M ^ 2 < 1) :
    Continuous (boundDIntegrandK M) := by
  unfold boundDIntegrandK
  refine Continuous.div₀ ?_ ?_ ?_
  · -- numerator: `M · sin²θ`
    exact continuous_const.mul (continuous_sin.pow 2)
  · -- denominator: `(1 − M² sin²θ) · √(1 − M² sin²θ)`
    have h_inner : Continuous (fun θ : ℝ => 1 - M ^ 2 * Real.sin θ ^ 2) :=
      Continuous.sub continuous_const
        (continuous_const.mul (continuous_sin.pow 2))
    exact h_inner.mul (Real.continuous_sqrt.comp h_inner)
  · intro θ
    have hp : 0 < 1 - M ^ 2 * Real.sin θ ^ 2 :=
      AmgmInequalityOQ04OQ01.denom_pos hM θ
    have hsp : 0 < Real.sqrt (1 - M ^ 2 * Real.sin θ ^ 2) :=
      AmgmInequalityOQ04OQ01.sqrt_denom_pos hM θ
    exact (mul_pos hp hsp).ne'

/-- For `M² < 1` the K-side bound is interval-integrable on `[0, π/2]`. -/
lemma boundDIntegrandK_integrable (hM : M ^ 2 < 1) :
    IntervalIntegrable (boundDIntegrandK M) MeasureTheory.volume 0 (π / 2) :=
  (boundDIntegrandK_continuous hM).intervalIntegrable 0 (π / 2)

/-- **Uniform bound** on `|dIntegrandK|` over the band `|κ| ≤ M`.

    For `0 ≤ M` with `M² < 1` and any `κ` with `κ² ≤ M²`,
    `|dIntegrandK κ θ| ≤ boundDIntegrandK M θ` for every `θ`.

    This is the pointwise content of the `h_bound` hypothesis of
    `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
    on the K-side, the analog of `dIntegrandE_abs_le_bound` (§9). -/
lemma dIntegrandK_abs_le_bound
    (hM : M ^ 2 < 1) (hM_nn : 0 ≤ M) (κ θ : ℝ) (hκ : κ ^ 2 ≤ M ^ 2) :
    |dIntegrandK κ θ| ≤ boundDIntegrandK M θ := by
  unfold dIntegrandK boundDIntegrandK
  have hsin2_nn : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hκ_sq_lt : κ ^ 2 < 1 := lt_of_le_of_lt hκ hM
  have hM_pos : 0 < 1 - M ^ 2 * Real.sin θ ^ 2 :=
    AmgmInequalityOQ04OQ01.denom_pos hM θ
  have hM_sqrt_pos : 0 < Real.sqrt (1 - M ^ 2 * Real.sin θ ^ 2) :=
    AmgmInequalityOQ04OQ01.sqrt_denom_pos hM θ
  have hκ_pos : 0 < 1 - κ ^ 2 * Real.sin θ ^ 2 :=
    AmgmInequalityOQ04OQ01.denom_pos hκ_sq_lt θ
  have hκ_sqrt_pos : 0 < Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) :=
    AmgmInequalityOQ04OQ01.sqrt_denom_pos hκ_sq_lt θ
  -- |κ| ≤ M from κ² ≤ M² and 0 ≤ M (via `Real.sqrt`).
  have habs_κ : |κ| ≤ M := by
    have h1 : Real.sqrt (κ ^ 2) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt hκ
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hM_nn] at h1
  -- Compute |·| on the LHS. Numerator = κ · sin²θ (no sign here, unlike §9).
  have h_num : |κ * Real.sin θ ^ 2| = |κ| * Real.sin θ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hsin2_nn]
  have h_denom_pos :
      0 < (1 - κ ^ 2 * Real.sin θ ^ 2)
        * Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) :=
    mul_pos hκ_pos hκ_sqrt_pos
  have h_denom :
      |(1 - κ ^ 2 * Real.sin θ ^ 2)
            * Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2)|
          = (1 - κ ^ 2 * Real.sin θ ^ 2)
              * Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) :=
    abs_of_pos h_denom_pos
  rw [abs_div, h_num, h_denom]
  -- Goal:
  --   |κ| · sin²θ / [(1 − κ²sin²θ)·√(1 − κ²sin²θ)]
  --     ≤ M · sin²θ / [(1 − M²sin²θ)·√(1 − M²sin²θ)].
  apply div_le_div
  · -- 0 ≤ numerator on RHS
    exact mul_nonneg hM_nn hsin2_nn
  · -- numerator inequality: |κ|·sin²θ ≤ M·sin²θ
    exact mul_le_mul_of_nonneg_right habs_κ hsin2_nn
  · -- 0 < denominator on RHS
    exact mul_pos hM_pos hM_sqrt_pos
  · -- denominator inequality:
    -- (1 − M²sin²θ) · √(1 − M²sin²θ) ≤ (1 − κ²sin²θ) · √(1 − κ²sin²θ).
    have h_inner_le : 1 - M ^ 2 * Real.sin θ ^ 2 ≤ 1 - κ ^ 2 * Real.sin θ ^ 2 := by
      have hmono : κ ^ 2 * Real.sin θ ^ 2 ≤ M ^ 2 * Real.sin θ ^ 2 :=
        mul_le_mul_of_nonneg_right hκ hsin2_nn
      linarith
    have h_sqrt_le :
        Real.sqrt (1 - M ^ 2 * Real.sin θ ^ 2)
          ≤ Real.sqrt (1 - κ ^ 2 * Real.sin θ ^ 2) :=
      Real.sqrt_le_sqrt h_inner_le
    exact mul_le_mul h_inner_le h_sqrt_le hM_sqrt_pos.le hκ_pos.le

-- ============================================================================
-- § 12. K-side Algebraic Identities — Building Blocks for the IBP Step
-- ============================================================================

/-
The full K-side integral identity
  `∫₀^{π/2} dIntegrandK k θ dθ = (E(k) - (1-k²) K(k)) / (k (1-k²))`
is **not** pointwise (a difference from §8) — it requires integration by
parts via the auxiliary function `auxFnK k θ := sin θ · cos θ / √(1-k²sin²θ)`,
whose endpoint values vanish (`auxFnK k 0 = auxFnK k (π/2) = 0`) and whose
derivative satisfies
  `(d/dθ) auxFnK k θ = cos²θ / √(1-k²sin²θ)
       - (1-k²) · sin²θ / [(1-k²sin²θ) · √(1-k²sin²θ)]`.

This section provides the two **integral building blocks** that the IBP
step will combine with FTC on `auxFnK`:

* `integral_sin_sq_div_sqrt_denom` — the integral of `sin²θ / √(1-k²sin²θ)`
  expressed in terms of `K(k)` and `E(k)`. This is the **integrated form**
  of the algebraic split `dIntegrandE_mul_k` (§8).
* `integral_cos_sq_div_sqrt_denom` — the integral of `cos²θ / √(1-k²sin²θ)`
  expressed in terms of `E(k)` and `(1-k²) · K(k)`. Follows from the first
  via `cos²θ = 1 - sin²θ`.

Once the FTC of `auxFnK` is established (deferred to a follow-up session
because the chain-rule + algebraic-match work is substantial), combining
it with these two integrals yields the target K-side identity:
  `(1-k²) · ∫ k sin²θ / [(1-k²sin²θ)·√(1-k²sin²θ)] dθ
        = ∫ cos²θ / √(1-k²sin²θ) dθ - 0
        = (E - (1-k²) K) / k`.
-/

/-- **Building block for the K-side IBP step.**

    For `0 < k < 1`,
    `∫₀^{π/2} sin²θ / √(1-k²sin²θ) dθ = (K(k) - E(k)) / k²`.

    Proof: The pointwise identity
    `sin²θ / √(1-k²sin²θ) = (ellipticIntegrand k θ - ellipticIntegrandE k θ) / k²`
    follows from `dIntegrandE_mul_k` (§8). Integrating both sides over
    `[0, π/2]` and using linearity (`integral_div`, `integral_sub`) plus
    the definitions `ellipticK = ∫ ellipticIntegrand` and `ellipticE = ∫ ellipticIntegrandE`
    yields the stated identity. -/
lemma integral_sin_sq_div_sqrt_denom (hk_pos : 0 < k) (hk_lt : k < 1) :
    ∫ θ in (0 : ℝ)..π / 2,
        Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      = (AmgmInequalityOQ04OQ01.ellipticK k - ellipticE k) / k ^ 2 := by
  have hk_sq : k ^ 2 < 1 := by nlinarith
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  have hk_sq_ne : k ^ 2 ≠ 0 := pow_ne_zero 2 hk_ne
  -- Pointwise identity: sin²θ / √D = (K_int - E_int) / k².
  have h_pointwise : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) =
      (AmgmInequalityOQ04OQ01.ellipticIntegrand k θ
        - ellipticIntegrandE k θ) / k ^ 2 := by
    intro θ _
    have hs_pos : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
      AmgmInequalityOQ04OQ01.sqrt_denom_pos hk_sq θ
    have hs_ne : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := hs_pos.ne'
    have hs_sq : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
          = 1 - k ^ 2 * Real.sin θ ^ 2 :=
      Real.mul_self_sqrt
        (le_of_lt (AmgmInequalityOQ04OQ01.denom_pos hk_sq θ))
    unfold AmgmInequalityOQ04OQ01.ellipticIntegrand ellipticIntegrandE
    field_simp
    linear_combination hs_sq
  rw [intervalIntegral.integral_congr h_pointwise]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub
        (AmgmInequalityOQ04OQ01.ellipticK_integrable hk_sq)
        (ellipticE_integrable k)]
  rfl

/-- **Building block for the K-side IBP step.**

    For `0 < k < 1`,
    `∫₀^{π/2} cos²θ / √(1-k²sin²θ) dθ = (E(k) - (1-k²) · K(k)) / k²`.

    Proof: `cos²θ = 1 - sin²θ`, so
    `cos²θ / √D = 1/√D - sin²θ/√D = ellipticIntegrand - sin²θ/√D`.
    Integrating gives `K - (K - E)/k² = (k²·K - K + E)/k² = (E - (1-k²)·K)/k²`. -/
lemma integral_cos_sq_div_sqrt_denom (hk_pos : 0 < k) (hk_lt : k < 1) :
    ∫ θ in (0 : ℝ)..π / 2,
        Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      = (ellipticE k - (1 - k ^ 2) * AmgmInequalityOQ04OQ01.ellipticK k)
          / k ^ 2 := by
  have hk_sq : k ^ 2 < 1 := by nlinarith
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  have hk_sq_ne : k ^ 2 ≠ 0 := pow_ne_zero 2 hk_ne
  -- Pointwise identity: cos²θ / √D = ellipticIntegrand - sin²θ/√D
  -- via cos²θ = 1 - sin²θ and ellipticIntegrand = 1/√D.
  have h_pointwise : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) =
      AmgmInequalityOQ04OQ01.ellipticIntegrand k θ
        - Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) := by
    intro θ _
    have hs_pos : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
      AmgmInequalityOQ04OQ01.sqrt_denom_pos hk_sq θ
    have hs_ne : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := hs_pos.ne'
    have h_pyth : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
      linear_combination Real.sin_sq_add_cos_sq θ
    unfold AmgmInequalityOQ04OQ01.ellipticIntegrand
    rw [h_pyth, sub_div]
  rw [intervalIntegral.integral_congr h_pointwise]
  -- ∫ (K_int - sin²/√D) = K - (K - E)/k² = (E - (1-k²) K)/k²
  have h_sin_sq_int :
      ∫ θ in (0 : ℝ)..π / 2,
          Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        = (AmgmInequalityOQ04OQ01.ellipticK k - ellipticE k) / k ^ 2 :=
    integral_sin_sq_div_sqrt_denom hk_pos hk_lt
  have h_sin_int :
      IntervalIntegrable
        (fun θ => Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
        MeasureTheory.volume 0 (π / 2) := by
    apply Continuous.intervalIntegrable
    refine Continuous.div₀ ((continuous_sin.pow 2)) ?_ ?_
    · refine Real.continuous_sqrt.comp ?_
      exact Continuous.sub continuous_const
        (continuous_const.mul (continuous_sin.pow 2))
    · intro θ
      exact (AmgmInequalityOQ04OQ01.sqrt_denom_pos hk_sq θ).ne'
  rw [intervalIntegral.integral_sub
        (AmgmInequalityOQ04OQ01.ellipticK_integrable hk_sq) h_sin_int]
  -- ∫ K_int = ellipticK; the sin² integral is given by h_sin_sq_int.
  show AmgmInequalityOQ04OQ01.ellipticK k
        - ∫ θ in (0 : ℝ)..π / 2,
            Real.sin θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      = (ellipticE k - (1 - k ^ 2) * AmgmInequalityOQ04OQ01.ellipticK k)
          / k ^ 2
  rw [h_sin_sq_int]
  field_simp
  ring

-- ============================================================================
-- § 13. Auxiliary Function `auxFnK` for the K-side IBP Step
-- ============================================================================

/-
The full K-side integral identity
  `∫₀^{π/2} dIntegrandK k θ dθ = (E(k) - (1-k²) K(k)) / (k (1-k²))`
is established by integration by parts on the auxiliary function
  `auxFnK k θ := sin θ · cos θ / √(1 − k² sin²θ)`.

This section provides the **endpoint vanishing** layer of the IBP step:

* `auxFnK` — the definition.
* `auxFnK_zero` — `auxFnK k 0 = 0`  (because `sin 0 = 0`).
* `auxFnK_pi_div_two` — `auxFnK k (π/2) = 0`  (because `cos (π/2) = 0`).

The chain-rule computation `(d/dθ) auxFnK k θ` and the FTC closure
  `∫₀^{π/2} (auxFnK k)' dθ = auxFnK k (π/2) − auxFnK k 0 = 0`
are deferred to a follow-up session (S9 parts 2–4 in `state.md`).

The endpoint vanishings established here are precisely the reason the
IBP boundary terms drop out, leaving the clean identity
  `∫₀^{π/2} (auxFnK k)' dθ = 0`,
which combines with §12's `integral_cos_sq_div_sqrt_denom` to yield the
target K-side integral identity.
-/

/-- **Auxiliary function for the K-side IBP step.**

    `auxFnK k θ := sin θ · cos θ / √(1 − k² sin²θ)`.

    Its derivative in θ decomposes (via the standard chain rule on a
    quotient) into terms involving `cos²θ / √D` and
    `sin²θ / [(1 − k² sin²θ) · √D]` — both of which appear in the K-side
    integral algebra of §12. Pinning down that decomposition and applying
    the fundamental theorem of calculus on `[0, π/2]` is the next
    sub-step (S9 parts 2–4); the endpoint vanishings below close the
    boundary side of FTC. -/
noncomputable def auxFnK (k θ : ℝ) : ℝ :=
  Real.sin θ * Real.cos θ / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)

/-- **Left endpoint vanishing.** `auxFnK k 0 = 0`, because `sin 0 = 0`. -/
lemma auxFnK_zero (k : ℝ) : auxFnK k 0 = 0 := by
  unfold auxFnK
  rw [Real.sin_zero, zero_mul, zero_div]

/-- **Right endpoint vanishing.** `auxFnK k (π/2) = 0`, because
    `cos (π/2) = 0`. -/
lemma auxFnK_pi_div_two (k : ℝ) : auxFnK k (π / 2) = 0 := by
  unfold auxFnK
  rw [Real.cos_pi_div_two, mul_zero, zero_div]

-- ============================================================================
-- § 14. Pointwise Chain Rule for `auxFnK` in θ (S9 part 2)
-- ============================================================================

/-
With `auxFnK` and the endpoint vanishings in place (§13), the next sub-step
of the K-side IBP layer is the **pointwise chain rule** for `auxFnK` in θ.

This section computes
  `(d/dθ) auxFnK k θ
     = cos²θ / √(1 − k² sin²θ)
        − (1−k²) · sin²θ / [(1 − k² sin²θ) · √(1 − k² sin²θ)]`,
valid whenever `k² < 1`. The two terms on the right will be integrated
separately in the FTC closure (S9 part 3); the first matches the
integrand of `integral_cos_sq_div_sqrt_denom` (§12), and the second is
the IBP-driven term that combines with §12 to deliver the K-side
integral identity (S9 part 4).

The proof is the standard quotient/chain rule:
* `(sin · cos)' = cos²θ − sin²θ` from
  `Real.hasDerivAt_sin.mul Real.hasDerivAt_cos`.
* `(√(1 − k² sin²θ))' = −k² sin θ cos θ / √(1 − k² sin²θ)` via
  `HasDerivAt.sqrt` on the inner polynomial `1 − k² sin²θ` (whose
  derivative is `−2k² sin θ cos θ`).
* `HasDerivAt.div` on the quotient.
* Algebraic reduction of the raw quotient form to the target. The
  reduction uses the trig identity `sin²θ + cos²θ = 1` (substituted as
  `cos²θ = 1 − sin²θ`); see `auxFnK_deriv_form_eq` below.
-/

/-- **Algebraic equality of the two forms** of the `auxFnK` derivative.

    The chain rule on `auxFnK k θ = sin θ · cos θ / √(1 − k² sin²θ)`
    naturally produces a derivative with `cos²θ − sin²θ` in the
    numerator (from the product rule on `sin · cos`) and a
    `k² sin²θ cos²θ / (D · √D)` correction from the chain rule on the
    denominator. Algebraically this is equivalent to the cleaner
    `cos²θ / √D − (1−k²) sin²θ / (D · √D)` form needed downstream
    (where `D = 1 − k² sin²θ`); the conversion uses the trig identity
    `sin²θ + cos²θ = 1`. -/
lemma auxFnK_deriv_form_eq {k θ : ℝ} (hk : k ^ 2 < 1) :
    (Real.cos θ ^ 2 - Real.sin θ ^ 2)
        / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      + k ^ 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 /
        ((1 - k ^ 2 * Real.sin θ ^ 2)
          * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
    = Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
      - (1 - k ^ 2) * Real.sin θ ^ 2 /
        ((1 - k ^ 2 * Real.sin θ ^ 2)
          * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) := by
  have h_pos : 0 < 1 - k ^ 2 * Real.sin θ ^ 2 :=
    AmgmInequalityOQ04OQ01.denom_pos hk θ
  have h_pos_ne : (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := h_pos.ne'
  have hs_pos : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
    AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ
  have hs_ne : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := hs_pos.ne'
  have hcos_sq : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    have h := Real.sin_sq_add_cos_sq θ
    linarith
  rw [hcos_sq]
  field_simp [h_pos_ne, hs_ne]
  ring

/-- **Pointwise chain rule** for `auxFnK` in θ.

    For fixed `k` with `k² < 1`,
      `(d/dθ) auxFnK k θ
         = cos²θ / √(1 − k² sin²θ)
            − (1 − k²) · sin²θ /
              [(1 − k² sin²θ) · √(1 − k² sin²θ)]`,
    pointwise in θ.

    The two terms decompose along the lines of the K-side integral
    algebra of §12: the first integrates to
    `(E − (1−k²) K) / k²` (cf. `integral_cos_sq_div_sqrt_denom`), and
    the second is the IBP-driven term that the FTC closure (S9 part 3)
    combines with §13's endpoint vanishings to deliver the K-side
    integral identity (S9 part 4). -/
lemma auxFnK_hasDerivAt {k : ℝ} (hk : k ^ 2 < 1) (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => auxFnK k θ')
      (Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        - (1 - k ^ 2) * Real.sin θ ^ 2 /
          ((1 - k ^ 2 * Real.sin θ ^ 2)
            * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))) θ := by
  -- Positivity (uniform in θ since |k| < 1 and sin²θ ≤ 1).
  have h_pos : 0 < 1 - k ^ 2 * Real.sin θ ^ 2 :=
    AmgmInequalityOQ04OQ01.denom_pos hk θ
  have h_pos_ne : (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := h_pos.ne'
  have hs_pos : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
    AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ
  have hs_ne : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := hs_pos.ne'
  -- Numerator derivative: u(θ) = sin θ · cos θ; u'(θ) = cos²θ − sin²θ.
  have h_sin : HasDerivAt Real.sin (Real.cos θ) θ := Real.hasDerivAt_sin θ
  have h_cos : HasDerivAt Real.cos (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have h_num : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.cos θ')
      (Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ)) θ :=
    h_sin.mul h_cos
  -- sin² derivative: (sin θ' · sin θ')' = cos θ · sin θ + sin θ · cos θ.
  have h_sin_mul_sin : HasDerivAt (fun θ' : ℝ => Real.sin θ' * Real.sin θ')
      (Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ) θ :=
    h_sin.mul h_sin
  -- Convert to `sin θ' ^ 2` form via `pow_two`.
  have h_pow : HasDerivAt (fun θ' : ℝ => Real.sin θ' ^ 2)
      (2 * Real.sin θ * Real.cos θ) θ := by
    have h_eq_fun : (fun θ' : ℝ => Real.sin θ' ^ 2)
        = fun θ' : ℝ => Real.sin θ' * Real.sin θ' := by
      funext θ'; ring
    rw [h_eq_fun]
    have h_eq_deriv :
        Real.cos θ * Real.sin θ + Real.sin θ * Real.cos θ
          = 2 * Real.sin θ * Real.cos θ := by ring
    rw [← h_eq_deriv]
    exact h_sin_mul_sin
  -- Inner polynomial: g(θ) = 1 − k² sin²θ; g'(θ) = −(k² · 2 sin θ cos θ).
  have h_inner : HasDerivAt (fun θ' : ℝ => 1 - k ^ 2 * Real.sin θ' ^ 2)
      (-(k ^ 2 * (2 * Real.sin θ * Real.cos θ))) θ := by
    have h_mul : HasDerivAt (fun θ' : ℝ => k ^ 2 * Real.sin θ' ^ 2)
        (k ^ 2 * (2 * Real.sin θ * Real.cos θ)) θ :=
      h_pow.const_mul (k ^ 2)
    have h_sub : HasDerivAt (fun θ' : ℝ => 1 - k ^ 2 * Real.sin θ' ^ 2)
        (0 - k ^ 2 * (2 * Real.sin θ * Real.cos θ)) θ :=
      (hasDerivAt_const θ (1 : ℝ)).sub h_mul
    simpa using h_sub
  -- Sqrt of inner: HasDerivAt (θ' ↦ √(1 − k² sin²θ')) (...) θ.
  have h_sqrt := h_inner.sqrt h_pos_ne
  -- Quotient: HasDerivAt (θ' ↦ sin θ' · cos θ' / √(1 − k² sin²θ')) (...) θ.
  have h_div := h_num.div h_sqrt hs_ne
  -- Convert `(fun θ' => auxFnK k θ')` to its unfolded body.
  have h_fun_eq :
      (fun θ' : ℝ => auxFnK k θ')
        = fun θ' : ℝ =>
          Real.sin θ' * Real.cos θ' /
            Real.sqrt (1 - k ^ 2 * Real.sin θ' ^ 2) := by
    funext θ'; rfl
  rw [h_fun_eq]
  -- Reduce h_div's raw quotient derivative through an intermediate
  -- form, then to the target via `auxFnK_deriv_form_eq`.
  have h_eq_intermediate :
      ((Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ))
            * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        - Real.sin θ * Real.cos θ
            * (-(k ^ 2 * (2 * Real.sin θ * Real.cos θ))
                / (2 * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))))
        / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 2
      = (Real.cos θ ^ 2 - Real.sin θ ^ 2)
            / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
          + k ^ 2 * Real.sin θ ^ 2 * Real.cos θ ^ 2 /
            ((1 - k ^ 2 * Real.sin θ ^ 2)
              * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) := by
    have hsq : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 2
        = 1 - k ^ 2 * Real.sin θ ^ 2 := by
      rw [sq, Real.mul_self_sqrt h_pos.le]
    rw [hsq]
    field_simp [h_pos_ne, hs_ne]
    ring
  -- Compose: target → intermediate → raw, in reverse so `exact h_div` closes.
  rw [show
      Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        - (1 - k ^ 2) * Real.sin θ ^ 2 /
          ((1 - k ^ 2 * Real.sin θ ^ 2)
            * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
        = ((Real.cos θ * Real.cos θ + Real.sin θ * (-Real.sin θ))
              * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
            - Real.sin θ * Real.cos θ
                * (-(k ^ 2 * (2 * Real.sin θ * Real.cos θ))
                    / (2 * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))))
          / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ^ 2 from by
      rw [h_eq_intermediate, ← auxFnK_deriv_form_eq hk]]
  exact h_div

-- ============================================================================
-- § 15. FTC Closure for `auxFnK`: ∫₀^{π/2} (auxFnK k)' dθ = 0  (S9 part 3)
-- ============================================================================

/-
With §13 (`auxFnK` + endpoint vanishings) and §14 (pointwise chain rule for
`auxFnK` in θ) in place, the **fundamental theorem of calculus** yields
  `∫₀^{π/2} (auxFnK k)' dθ = auxFnK k (π/2) − auxFnK k 0 = 0`.
Substituting §14's chain-rule decomposition for `(auxFnK k)'`, this becomes
  `∫₀^{π/2} (cos²θ/√D − (1−k²)·sin²θ/(D·√D)) dθ = 0`,
where `D = 1 − k² sin²θ`. This is the **K-side IBP boundary identity** —
the S9 part 3 piece needed for the K-side integral identity. S9 part 4
will combine this with §12's `integral_cos_sq_div_sqrt_denom` to deliver
  `∫₀^{π/2} dIntegrandK k θ dθ = (E(k) − (1−k²) K(k)) / (k(1−k²))`.

The proof applies `intervalIntegral.integral_eq_sub_of_hasDerivAt` with
`f = auxFnK k`, `f' = (the §14 chain-rule RHS)`, using §14's unconditional
pointwise derivative for the `hderiv` hypothesis and continuity of the
integrand for `IntervalIntegrable` via `Continuous.intervalIntegrable`.
-/

/-- **Continuity of the `auxFnK` θ-derivative integrand.**

    The RHS of `auxFnK_hasDerivAt` (i.e., `(d/dθ) auxFnK k θ`) is
    continuous in θ for any fixed `k` with `k² < 1`. Used to discharge
    the `IntervalIntegrable` hypothesis of FTC in
    `integral_auxFnK_deriv_eq_zero`. Mirrors `dIntegrandE_continuous`
    (§8) and `dIntegrandK_continuous` (§10), with positivity of
    `D = 1 − k² sin²θ` and `√D` from
    `AmgmInequalityOQ04OQ01.denom_pos` and `sqrt_denom_pos`. -/
lemma auxFnK_deriv_continuous (hk : k ^ 2 < 1) :
    Continuous (fun θ : ℝ =>
      Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        - (1 - k ^ 2) * Real.sin θ ^ 2 /
          ((1 - k ^ 2 * Real.sin θ ^ 2)
            * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))) := by
  -- Continuous denominator helpers (mirror §8/§10 patterns).
  have h_denom_cont : Continuous (fun θ : ℝ => 1 - k ^ 2 * Real.sin θ ^ 2) :=
    Continuous.sub continuous_const
      (continuous_const.mul (continuous_sin.pow 2))
  have h_sqrt_cont :
      Continuous (fun θ : ℝ => Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)) :=
    Real.continuous_sqrt.comp h_denom_cont
  refine Continuous.sub ?_ ?_
  · -- cos²θ / √(1 − k² sin²θ)
    refine Continuous.div₀ (continuous_cos.pow 2) h_sqrt_cont ?_
    intro θ
    exact (AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ).ne'
  · -- (1 − k²) · sin²θ / [(1 − k² sin²θ) · √(1 − k² sin²θ)]
    refine Continuous.div₀
      (continuous_const.mul (continuous_sin.pow 2))
      (h_denom_cont.mul h_sqrt_cont) ?_
    intro θ
    have h1 : (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 :=
      (AmgmInequalityOQ04OQ01.denom_pos hk θ).ne'
    have h2 : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 :=
      (AmgmInequalityOQ04OQ01.sqrt_denom_pos hk θ).ne'
    exact mul_ne_zero h1 h2

/-- **FTC closure for `auxFnK`.** For `k² < 1`,
    `∫₀^{π/2} (cos²θ/√D − (1−k²)·sin²θ/(D·√D)) dθ = 0`,
    where `D = 1 − k² sin²θ`.

    Proof: apply `intervalIntegral.integral_eq_sub_of_hasDerivAt` to
    `f = auxFnK k`, with §14's `auxFnK_hasDerivAt` (unconditional in θ)
    discharging the pointwise-derivative hypothesis and
    `auxFnK_deriv_continuous` discharging integrability via
    `Continuous.intervalIntegrable`. The boundary
    `auxFnK k (π/2) − auxFnK k 0` reduces to `0 − 0 = 0` via §13
    (`auxFnK_pi_div_two` and `auxFnK_zero`).

    This identity is the IBP boundary-vanishing piece of the K-side
    integral identity (S9 part 4); combined with §12's
    `integral_cos_sq_div_sqrt_denom`, it pins down the
    `(1−k²) · ∫ sin²θ/(D·√D) dθ` term and hence
    `∫ dIntegrandK k θ dθ`. -/
theorem integral_auxFnK_deriv_eq_zero (hk : k ^ 2 < 1) :
    ∫ θ in (0 : ℝ)..π / 2,
      Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        - (1 - k ^ 2) * Real.sin θ ^ 2 /
          ((1 - k ^ 2 * Real.sin θ ^ 2)
            * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
      = 0 := by
  have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      HasDerivAt (fun θ' : ℝ => auxFnK k θ')
        (Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
          - (1 - k ^ 2) * Real.sin θ ^ 2 /
            ((1 - k ^ 2 * Real.sin θ ^ 2)
              * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))) θ :=
    fun θ _ => auxFnK_hasDerivAt hk θ
  have hint : IntervalIntegrable
      (fun θ : ℝ =>
        Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
          - (1 - k ^ 2) * Real.sin θ ^ 2 /
            ((1 - k ^ 2 * Real.sin θ ^ 2)
              * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)))
      MeasureTheory.volume 0 (π / 2) :=
    (auxFnK_deriv_continuous hk).intervalIntegrable 0 (π / 2)
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  -- Goal after FTC: `(fun θ' => auxFnK k θ') (π/2) - (fun θ' => auxFnK k θ') 0 = 0`.
  -- Beta-reduce, then apply §13's endpoint vanishings.
  show auxFnK k (π / 2) - auxFnK k 0 = 0
  rw [auxFnK_pi_div_two, auxFnK_zero, sub_zero]

-- ============================================================================
-- § 16. K-side Integral Identity (S9 part 4 — IBP closure for `dIntegrandK`)
-- ============================================================================

/-
Combining §15's `integral_auxFnK_deriv_eq_zero` (FTC closure on `auxFnK`)
with §12's `integral_cos_sq_div_sqrt_denom` discharges the K-side integral
identity:

    ∫₀^{π/2} dIntegrandK k θ dθ
      = (E(k) − (1 − k²) · K(k)) / (k · (1 − k²)).

This is the K-analog of §8's `integral_dIntegrandE_eq` and the final
ingredient for the S10 `dK_dk` assembly via the parametric-integral lemma
of Mathlib (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`).

Proof sketch.

  • S9 part 3 yields  ∫ cos²θ/√D − (1−k²) sin²θ/(D·√D) dθ = 0,
    i.e. ∫ cos²θ/√D dθ = (1−k²) ∫ sin²θ/(D·√D) dθ.
  • Pointwise, dIntegrandK k θ = k · sin²θ / (D·√D), so
    ∫ sin²θ/(D·√D) dθ = (∫ dIntegrandK k θ dθ) / k.
  • S8 (`integral_cos_sq_div_sqrt_denom`) yields
    ∫ cos²θ/√D dθ = (E − (1−k²) K) / k².
  • Combining: (1−k²) · (∫ dIntegrandK)/k = (E − (1−k²) K)/k², hence
    ∫ dIntegrandK = (E − (1−k²) K) / (k · (1−k²)).
-/

/-- **K-side integral identity** (S9 part 4 — IBP closure for `dIntegrandK`).

    For `0 < k < 1`,
    `∫₀^{π/2} dIntegrandK k θ dθ = (E(k) − (1 − k²) · K(k)) / (k · (1 − k²))`.

    Proof: apply `integral_auxFnK_deriv_eq_zero` (S9 part 3) to obtain the FTC
    boundary-vanishing identity; rewrite its `(1 − k²) · sin²θ / (D · √D)`
    term as `(1 − k²) / k · dIntegrandK k θ` (pointwise, via the definition of
    `dIntegrandK`); split via `intervalIntegral.integral_sub`; pull the
    constant `(1 − k²) / k` out via `intervalIntegral.integral_const_mul`;
    substitute `integral_cos_sq_div_sqrt_denom` (S8) for the `cos²θ / √D`
    integral; solve the resulting linear equation for `∫ dIntegrandK k θ dθ`.

    This is the K-analog of `integral_dIntegrandE_eq` (§8). The conclusion
    feeds the `h_int_eq` rewrite of the S10 `dK_dk` assembly. -/
theorem integral_dIntegrandK_eq (hk_pos : 0 < k) (hk_lt : k < 1) :
    ∫ θ in (0 : ℝ)..π / 2, dIntegrandK k θ
      = (ellipticE k - (1 - k ^ 2) * AmgmInequalityOQ04OQ01.ellipticK k)
          / (k * (1 - k ^ 2)) := by
  have hk_sq : k ^ 2 < 1 := by nlinarith
  have hk_ne : k ≠ 0 := ne_of_gt hk_pos
  have h1mk2_pos : 0 < 1 - k ^ 2 := by linarith
  have h1mk2_ne : (1 - k ^ 2) ≠ 0 := h1mk2_pos.ne'
  have hk_sq_ne : (k : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hk_ne
  -- Apply S9 part 3 (FTC closure for `auxFnK`).
  have h_ftc := integral_auxFnK_deriv_eq_zero (k := k) hk_sq
  -- Pointwise rewrite: the FTC integrand's second term equals
  -- `(1 - k²) / k * dIntegrandK k θ` (via the definition of `dIntegrandK`).
  have h_pw : ∀ θ ∈ Set.uIcc (0 : ℝ) (π / 2),
      Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        - (1 - k ^ 2) * Real.sin θ ^ 2 /
          ((1 - k ^ 2 * Real.sin θ ^ 2)
            * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
      = Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
          - (1 - k ^ 2) / k * dIntegrandK k θ := by
    intro θ _
    have hp : 0 < 1 - k ^ 2 * Real.sin θ ^ 2 :=
      AmgmInequalityOQ04OQ01.denom_pos hk_sq θ
    have hsp : 0 < Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) :=
      AmgmInequalityOQ04OQ01.sqrt_denom_pos hk_sq θ
    have hp_ne : (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := hp.ne'
    have hsp_ne : Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2) ≠ 0 := hsp.ne'
    unfold dIntegrandK
    field_simp
    ring
  rw [intervalIntegral.integral_congr h_pw] at h_ftc
  -- Split the integral and pull the constant `(1-k²)/k` outside.
  have h_cos_int : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
      MeasureTheory.volume 0 (π / 2) := by
    apply Continuous.intervalIntegrable
    refine Continuous.div₀ (continuous_cos.pow 2) ?_ ?_
    · exact Real.continuous_sqrt.comp
        (Continuous.sub continuous_const
          (continuous_const.mul (continuous_sin.pow 2)))
    · intro θ
      exact (AmgmInequalityOQ04OQ01.sqrt_denom_pos hk_sq θ).ne'
  have h_dK_int : IntervalIntegrable (dIntegrandK k) MeasureTheory.volume 0 (π / 2) :=
    dIntegrandK_integrable hk_sq
  rw [intervalIntegral.integral_sub h_cos_int
        (h_dK_int.const_mul ((1 - k ^ 2) / k))] at h_ftc
  rw [intervalIntegral.integral_const_mul] at h_ftc
  -- Substitute the S8 cos² integral identity.
  rw [integral_cos_sq_div_sqrt_denom hk_pos hk_lt] at h_ftc
  -- h_ftc: (E - (1-k²)·K) / k² - (1-k²)/k · ∫ dIntegrandK = 0
  -- Solve for ∫ dIntegrandK = (E - (1-k²)·K) / (k·(1-k²)).
  rw [eq_div_iff (mul_ne_zero hk_ne h1mk2_ne)]
  -- Clear denominators in h_ftc (multiply by k²) to obtain a polynomial form,
  -- then close by `linear_combination` (which uses `ring` for commutativity).
  field_simp at h_ftc
  linear_combination -h_ftc

-- ============================================================================
-- § 17. K-side Differentiation Under the Integral: dK/dk = (E − (1−k²)K) / (k(1−k²))
-- ============================================================================

/-
With the K-side chain rule (§10), uniform bound (§11), and integral identity
(§16) in hand, we apply Mathlib's
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` to obtain
the K-analog of `dE_dk`:

    dK/dk = (E(k) − (1 − k²) · K(k)) / (k · (1 − k²))     for 0 < k < 1.

Strategy mirrors the §10-of-PR-#17371 dE_dk template (now superseded by
intermediate K-side merges; that PR's §10 will become §18 on rebase). The
seven hypotheses of the parametric-integral lemma are discharged with:

  • `hs_nhds`     : `Set.Ioo (-M) M ∈ 𝓝 k` for `M := (k+1)/2` (open band).
  • `hF_meas`     : `(integrand_continuous _).aestronglyMeasurable`
                    over the band — F at every parameter is ae-measurable.
  • `hF_int`      : `ellipticK_integrable hk_sq_lt_one`
                    — F at x₀ = k is interval-integrable.
  • `hF'_meas`    : `(dIntegrandK_continuous _).aestronglyMeasurable`
                    — F' at x₀ is ae-measurable.
  • `h_bound`     : `dIntegrandK_abs_le_bound` (§11) lifted to `∀ᵐ` via
                    `MeasureTheory.ae_of_all`.
  • `h_bound_int` : `boundDIntegrandK_integrable hM_sq_lt_one` (§11).
  • `h_diff`      : `integrandK_hasDerivAt_in_k` (§10) lifted similarly.

The lemma yields `HasDerivAt (κ ↦ ∫ ellipticIntegrand κ θ dθ)
(∫ dIntegrandK k θ dθ) k`. Definitional unfolding identifies the function
with `ellipticK`. The §16 integral identity then rewrites the conclusion
to the desired closed form.

This is the K-side companion to the (still-open) `dE_dk` theorem PRs
(#17371, #17445). Once `dE_dk` lands, S11 will combine the two derivatives
with the chain rule for `complModulus` (§4) to discharge the
`legendre_relation` axiom by the Wronskian-vanishing argument.
-/

/-- **Differentiation under the integral sign** for `ellipticK`.

    For `0 < k < 1`,
    `dK/dk = (E(k) − (1 − k²) · K(k)) / (k · (1 − k²))`.

    Proof: apply `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
    on the open neighborhood `Set.Ioo (-M) M` with `M := (k+1)/2 ∈ (k, 1)`.
    Discharge the seven hypotheses with the §10 chain rule and integrability
    facts (`integrandK_hasDerivAt_in_k`, `dIntegrandK_continuous`), the §11
    uniform bound (`dIntegrandK_abs_le_bound` plus `boundDIntegrandK_integrable`),
    and `Filter.eventually_of_forall` / `MeasureTheory.ae_of_all` to lift
    pointwise statements to ae-statements. The lemma yields
    `HasDerivAt ellipticK (∫₀^{π/2} dIntegrandK k θ dθ) k`, and the §16
    integral identity `integral_dIntegrandK_eq` rewrites the integral to
    `(E(k) − (1 − k²) · K(k)) / (k · (1 − k²))`. -/
theorem dK_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticK
      ((ellipticE k - (1 - k ^ 2) * ellipticK k) / (k * (1 - k ^ 2))) k := by
  -- Pick the band M = (k+1)/2 ∈ (k, 1); note M² < 1.
  set M : ℝ := (k + 1) / 2 with hM_def
  have hM_pos : 0 < M := by simp only [hM_def]; linarith
  have hk_lt_M : k < M := by simp only [hM_def]; linarith
  have hM_lt_one : M < 1 := by simp only [hM_def]; linarith
  have hM_sq_lt_one : M ^ 2 < 1 := by nlinarith
  have hM_nn : (0 : ℝ) ≤ M := le_of_lt hM_pos
  have hk_sq_lt_one : k ^ 2 < 1 := by nlinarith
  -- The open neighborhood s := Set.Ioo (-M) M of k.
  set s : Set ℝ := Set.Ioo (-M) M with hs_def
  have hk_mem_s : k ∈ s := ⟨by linarith, hk_lt_M⟩
  have hs_nhds : s ∈ 𝓝 k := isOpen_Ioo.mem_nhds hk_mem_s
  -- For κ ∈ s, κ² ≤ M² (and a fortiori κ² < 1).
  have h_kappa_sq_le : ∀ κ ∈ s, κ ^ 2 ≤ M ^ 2 := by
    intro κ hκ
    obtain ⟨hκ_low, hκ_hi⟩ := hκ
    exact le_of_lt (sq_lt_sq' hκ_low hκ_hi)
  have h_kappa_sq_lt_one : ∀ κ ∈ s, κ ^ 2 < 1 := fun κ hκ =>
    lt_of_le_of_lt (h_kappa_sq_le κ hκ) hM_sq_lt_one
  -- B1 fix per S11c §4.4: pick ε so Metric.ball k ε ⊆ s. Then the
  -- parametric-integral lemma's first arg `0 < ε` is matched, and the
  -- ∀-over-ball hypotheses are lifted from the existing ∀-over-s ones.
  set ε : ℝ := min (M - k) (k + M) with hε_def
  have hε_pos : 0 < ε := by
    simp only [hε_def]
    exact lt_min (by linarith) (by linarith)
  have h_ball_eq_s : Metric.ball k ε ⊆ s := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    obtain ⟨hx_low, hx_hi⟩ := hx
    have hε_le_Mk : ε ≤ M - k := by simp only [hε_def]; exact min_le_left _ _
    have hε_le_kM : ε ≤ k + M := by simp only [hε_def]; exact min_le_right _ _
    exact ⟨by linarith, by linarith⟩
  -- Hypothesis: F is ae-strongly-measurable in a neighborhood of k.
  -- (We use `s` as the neighborhood — every κ ∈ s has κ² < 1, so the
  -- K-integrand is continuous and hence ae-measurable.)
  have hF_meas : ∀ᶠ x in 𝓝 k,
      MeasureTheory.AEStronglyMeasurable
        (fun θ => AmgmInequalityOQ04OQ01.ellipticIntegrand x θ)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) := by
    refine Filter.eventually_of_mem hs_nhds ?_
    intro x hx
    exact (AmgmInequalityOQ04OQ01.integrand_continuous
      (h_kappa_sq_lt_one x hx)).aestronglyMeasurable
  -- Hypothesis: F at x₀ = k is interval-integrable.
  have hF_int : IntervalIntegrable
      (fun θ => AmgmInequalityOQ04OQ01.ellipticIntegrand k θ)
      MeasureTheory.volume 0 (π / 2) :=
    AmgmInequalityOQ04OQ01.ellipticK_integrable hk_sq_lt_one
  -- Hypothesis: F' at x₀ = k is ae-strongly-measurable on the restriction.
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun θ => dIntegrandK k θ)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) :=
    (dIntegrandK_continuous hk_sq_lt_one).aestronglyMeasurable
  -- Hypothesis: pointwise majorization on Metric.ball k ε (lifted from s).
  have h_bound : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ Metric.ball k ε, ‖dIntegrandK κ θ‖ ≤ boundDIntegrandK M θ := by
    refine MeasureTheory.ae_of_all _ ?_
    intro θ _ κ hκ
    rw [Real.norm_eq_abs]
    have hκs : κ ∈ s := h_ball_eq_s hκ
    exact dIntegrandK_abs_le_bound hM_sq_lt_one hM_nn κ θ (h_kappa_sq_le κ hκs)
  -- Hypothesis: bound is interval-integrable.
  have h_bound_int : IntervalIntegrable (boundDIntegrandK M)
      MeasureTheory.volume 0 (π / 2) :=
    boundDIntegrandK_integrable hM_sq_lt_one
  -- Hypothesis: pointwise differentiability on Metric.ball k ε (lifted from s).
  have h_diff : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ Metric.ball k ε, HasDerivAt
        (fun x => AmgmInequalityOQ04OQ01.ellipticIntegrand x θ)
        (dIntegrandK κ θ) κ := by
    refine MeasureTheory.ae_of_all _ ?_
    intro θ _ κ hκ
    have hκs : κ ∈ s := h_ball_eq_s hκ
    exact integrandK_hasDerivAt_in_k (h_kappa_sq_lt_one κ hκs) θ
  -- Apply the parametric integral derivative lemma and extract the deriv.
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε_pos hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  have h_deriv :
      HasDerivAt
        (fun κ => ∫ θ in (0 : ℝ)..π / 2,
          AmgmInequalityOQ04OQ01.ellipticIntegrand κ θ)
        (∫ θ in (0 : ℝ)..π / 2, dIntegrandK k θ) k := h.2
  -- Rewrite the integral via the §16 integral identity.
  rw [integral_dIntegrandK_eq hk_pos hk_lt] at h_deriv
  -- The function fun κ ↦ ∫ ellipticIntegrand κ is ellipticK by definition.
  exact h_deriv

end AmgmInequalityOQ04OQ02

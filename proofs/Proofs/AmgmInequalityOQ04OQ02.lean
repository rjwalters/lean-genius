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
- [x] Integrand continuous and integrable for all k
- [x] E(k) > 0 for k² < 1 (proved via lower bound)
- [x] complModulus defined; (k')² = 1 − k², k' ≥ 0
- [x] Symmetric Legendre relation derived from the general form
- [ ] General Legendre relation: axiomatized (deep — proof requires Mathlib
      derivative-under-the-integral plus Legendre ODE Wronskian; future session)

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
      (intervalIntegrable_const)
      (ellipticE_integrable k)
      (fun θ _ => integrandE_lower_bound hk θ)
    simpa [ellipticE, intervalIntegral.integral_const, smul_eq_mul,
      sub_zero] using this
  have hpos : 0 < Real.sqrt (1 - k ^ 2) * (π / 2 - 0) := by
    have : 0 < Real.sqrt (1 - k ^ 2) * (π / 2) := mul_pos hsqrt_pos hπ
    simpa [sub_zero] using this
  exact lt_of_lt_of_le hpos hlb

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

end AmgmInequalityOQ04OQ02

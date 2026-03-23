# Knowledge Base: fourier-series-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Prove that Fourier coefficients of α-Hölder continuous functions on AddCircle T decay at rate O(1/|n|^α). The proof uses the half-period translation trick: shifting x → x + T/(2n) negates the n-th Fourier monomial, giving a difference formula that bounds the coefficient.

---

## Insights

### Proof Architecture (12 → 8 axioms)
- **fourier_norm_one**: `‖fourier n x‖ = 1` — trivial from `simp [fourier_apply]`, toCircle maps to unit circle
- **fourier_translate_halfperiod**: `fourier(-n)(x + T/(2n)) = -fourier(-n)(x)` — key identity via `fourier_neg + fourier_add_half_inv_index + map_neg`
- **holder_translation_bound**: `‖f(x) - f(x + T/(2n))‖ ≤ C·(T/(2|n|))^α` — via `HolderWith.dist_le_of_le` + `quotient_norm_mk_le'`
- **integral_product_bound**: `‖∫ (f(x)-f(x+s))·e_{-n}(x) dx‖ ≤ C·(T/(2|n|))^α` — via `norm_integral_le_integral_norm` + `integral_mono_of_nonneg` + `IsProbabilityMeasure`

### Key Mathlib Lemmas Used
- `quotient_norm_mk_le' : ‖(s : M ⧸ S)‖ ≤ ‖s‖` — quotient norm ≤ original norm, gives `dist(x, x+↑s) ≤ |s|` on AddCircle
- `HolderWith.dist_le_of_le : dist x y ≤ d → dist (f x) (f y) ≤ C * d ^ α` — core Hölder bound
- `norm_integral_le_integral_norm : ‖∫ f ∂μ‖ ≤ ∫ ‖f‖ ∂μ` — triangle inequality for integrals
- `integral_mono_of_nonneg : 0 ≤ f → Integrable g → f ≤ g a.e. → ∫ f ≤ ∫ g` — monotonicity
- `IsProbabilityMeasure.measure_univ` — haarAddCircle total mass = 1
- `integral_add_right_eq_self` — Haar measure translation invariance (works without integrability)

### Distance on AddCircle
- `dist(x, x + ↑s) = ‖(x + ↑s) - x‖ = ‖↑s‖` (via `dist_comm + dist_eq_norm + add_sub_cancel_right`)
- `‖↑s : AddCircle T‖ ≤ |s|` (via `quotient_norm_mk_le'`)
- For exact computation: `AddCircle.norm_coe_eq_abs_iff` gives `‖↑s‖ = |s|` when `|s| ≤ |T|/2`
- `|T/(2n)| = T/(2|n|)` via `abs_div + abs_of_pos`

---

## Dead Ends

### fourierCoeff_difference_formula via integral_sub
- **Problem**: `integral_sub` requires `Integrable` for both terms, but the axiom has no integrability hypothesis
- **Impact**: Cannot decompose `∫ (a - b) = ∫ a - ∫ b` without proving integrability
- **Partial workaround**: `integral_add_right_eq_self` works without integrability, so translation invariance is available
- **Possible fix**: Case-split on integrability of `fun x => fourier (-n) x • f x`. If integrable, use integral_sub. If not, both sides are 0.

---

## Remaining Axioms (8)
1. `fourierCoeff_difference_formula` — difference formula via Haar translation (NEXT TARGET)
2. `fourierCoeff_sq_summable_of_holder` — square-summability for α > 1/2
3. `riemannLebesgue_of_holder` — Riemann-Lebesgue from Hölder
4. `holder_decay_is_optimal` — optimality (constructive, hard)
5. `decay_implies_regularity` — partial converse (Sobolev embedding, hard)
6. `fourierCoeff_smooth_decay` — C^k decay
7. `fourierCoeff_Cinfty_rapid_decay` — C^∞ rapid decay
8. `fourierCoeff_analytic_decay` — analytic exponential decay

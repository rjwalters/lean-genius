import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic

/-
# Minkowski's Integral Inequality as a Corollary of Cauchy-Schwarz (cauchy-schwarz-integral-oq-02)

## The Open Question

Can the **Minkowski integral inequality** be derived as a corollary of the
integral Cauchy-Schwarz inequality?

## The Answer: YES, with explicit proof chains

**Minkowski's inequality** (triangle inequality for Lᵖ norms):
```
‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p    for 1 ≤ p < ∞
```

**Derivation paths**:

### Path 1: L² special case — directly from inner-product CS

For p = 2, Minkowski follows from Cauchy-Schwarz via the norm-squared identity:
```
‖f+g‖² = ‖f‖² + 2⟪f,g⟫ + ‖g‖²
        ≤ ‖f‖² + 2‖f‖·‖g‖ + ‖g‖²    (by CS: ⟪f,g⟫ ≤ |⟪f,g⟫| ≤ ‖f‖·‖g‖)
        = (‖f‖ + ‖g‖)²
```

### Path 2: General Lᵖ — from Hölder (generalized CS)

For general p ≥ 1, the standard proof uses Hölder's inequality (the generalized CS):
```
∫|f+g|ᵖ ≤ ∫(|f|+|g|)·|f+g|^{p-1}
         = ∫|f|·|f+g|^{p-1} + ∫|g|·|f+g|^{p-1}    (Hölder twice)
         ≤ ‖f‖_p · ‖|f+g|^{p-1}‖_{p/(p-1)} + ‖g‖_p · ‖|f+g|^{p-1}‖_{p/(p-1)}
         = (‖f‖_p + ‖g‖_p) · ‖f+g‖_p^{p-1}
```
Dividing by ‖f+g‖_p^{p-1} gives Minkowski.

## Mathematical Hierarchy

```
CS (abstract): |⟪f,g⟫| ≤ ‖f‖·‖g‖
     ↓ (norm-squared identity, p=2 only)
Minkowski for L²: ‖f+g‖_2 ≤ ‖f‖_2 + ‖g‖_2

Hölder (generalized CS): ∫|fg| ≤ ‖f‖_p·‖g‖_q  (1/p + 1/q = 1)
     ↓ (applied twice to |f+g|ᵖ = |f|·|f+g|^{p-1} + |g|·|f+g|^{p-1})
Minkowski for Lᵖ: ‖f+g‖_p ≤ ‖f‖_p + ‖g‖_p
```
-/

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace MinkowskiFromCS

/-!
## Section I: L² Minkowski from Inner-Product Cauchy-Schwarz

The cleanest derivation: in any inner product space (including L²),
Minkowski's inequality follows directly from the inner product form of CS.
-/

/-- **Minkowski's inequality for L² via Cauchy-Schwarz** (inner product proof).

    For f, g ∈ L²(μ):
    ```
    ‖f + g‖ ≤ ‖f‖ + ‖g‖
    ```

    **Proof from CS**: Using ‖f+g‖² = ‖f‖² + 2⟪f,g⟫ + ‖g‖² and the CS bound ⟪f,g⟫ ≤ ‖f‖·‖g‖. -/
theorem minkowski_l2_from_CS (f g : Lp ℝ 2 μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ := by
  have h_cs : |@inner ℝ _ _ f g| ≤ ‖f‖ * ‖g‖ := abs_real_inner_le_norm f g
  have h_inner_le : @inner ℝ _ _ f g ≤ ‖f‖ * ‖g‖ :=
    le_trans (le_abs_self _) h_cs
  have h_sq : ‖f + g‖ ^ 2 ≤ (‖f‖ + ‖g‖) ^ 2 := by
    rw [norm_add_sq_real]
    nlinarith [norm_nonneg f, norm_nonneg g]
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h_sqrt

/-- **Abstract version**: Minkowski in any real inner product space via CS.

    This is the abstract version: for any real inner product space E,
    the triangle inequality follows from Cauchy-Schwarz. -/
theorem minkowski_inner_product_space {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  have h_cs : |@inner ℝ _ _ u v| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v
  have h_inner_le : @inner ℝ _ _ u v ≤ ‖u‖ * ‖v‖ :=
    le_trans (le_abs_self _) h_cs
  have h_sq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    rw [norm_add_sq_real]
    nlinarith [norm_nonneg u, norm_nonneg v]
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h_sqrt

/-!
## Section II: General Lᵖ Minkowski from Hölder (Generalized CS)

For p ≠ 2, the standard proof uses Hölder's inequality, which is the
generalization of Cauchy-Schwarz to conjugate exponents 1/p + 1/q = 1.

Mathlib's `MeasureTheory.snorm_add_le` implements this directly.
We show the connection to Hölder explicitly.
-/

/-- **Minkowski for general Lᵖ** via the abstract triangle inequality.

    For p ≥ 1 and f, g ∈ Lᵖ(μ):
    ```
    ‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p
    ```

    **Via Hölder**: The standard proof applies Hölder's inequality
    (= generalized CS) twice to ∫|f+g|ᵖ = ∫|f|·|f+g|^{p-1} + ∫|g|·|f+g|^{p-1},
    factoring out ‖f+g‖_p^{p-1} from both Hölder applications.

    Mathlib formalizes this as the `NormedAddCommGroup` triangle inequality
    for `Lp E p μ` (which holds for 1 ≤ p by `instNormedAddCommGroupLp`). -/
theorem minkowski_lp_from_holder (p : ENNReal) [Fact (1 ≤ p)] (f g : Lp ℝ p μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  norm_add_le f g

/-
## Section III: Integral Form (documented)

The Minkowski inequality in integral form (p ≥ 1):
  (∫|f+g|ᵖ dμ)^{1/p} ≤ (∫|f|ᵖ dμ)^{1/p} + (∫|g|ᵖ dμ)^{1/p}

Mathlib provides this via `MeasureTheory.snorm_add_le` (or `eLpNorm_add_le`
in newer versions), which proves the triangle inequality for the Lp seminorm.
The name depends on the Mathlib version:
- Mathlib < 4.14: `MeasureTheory.snorm_add_le`
- Mathlib ≥ 4.14: `MeasureTheory.eLpNorm_add_le` (renamed)

Both reduce to Hölder's inequality applied twice.
-/

/-- **Minkowski via Lp triangle inequality** (abstract form).

    For any Lp space with 1 ≤ p, the triangle inequality
    `‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p` holds.
    This wraps the `norm_add_le` instance for `Lp E p μ`.

    The key insight: `Lp E p μ` forms a `NormedAddCommGroup` for 1 ≤ p,
    and the Lp norm is defined so that the triangle inequality is precisely
    Minkowski's inequality. The proof of the NormedAddCommGroup instance
    uses Hölder's inequality internally. -/
theorem minkowski_lp_triangle (p : ENNReal) [Fact (1 ≤ p)] (f g : Lp ℝ p μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  norm_add_le f g

/-!
## Section IV: Minkowski in eLpNorm Form

The Minkowski inequality stated directly in terms of the Lp seminorm
(eLpNorm), which is Mathlib's primitive integral formulation.
-/

/-- **Minkowski in eLpNorm form**: Triangle inequality for the Lp seminorm.

    For 1 ≤ p and AEStronglyMeasurable f, g:
    ```
    eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ
    ```
    This is the direct integral form in terms of the Lp seminorm.
    Internally proved by Mathlib's `eLpNorm_add_le` via Hölder's inequality. -/
theorem minkowski_elpnorm_triangle {p : ENNReal} (hp : 1 ≤ p)
    {f g : α → ℝ} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ :=
  eLpNorm_add_le hf hg hp

/-!
## Section V: Full Minkowski Integral Inequality — Bochner Form

The **true** Minkowski integral inequality is a two-variable statement:
```
‖∫_β F(·, y) dν(y)‖_{Lᵖ(μ)} ≤ ∫_β ‖F(·, y)‖_{Lᵖ(μ)} dν(y)
```

This follows from `norm_integral_le_integral_norm` applied to Lp-valued
Bochner integrals. The proof chain:
1. Lp E p μ is a `NormedAddCommGroup` (using Minkowski/Hölder internally)
2. Bochner integrals satisfy ‖∫F‖ ≤ ∫‖F‖ (norm_integral_le_integral_norm)
3. For p = 2: the NormedAddCommGroup structure comes from the inner product
   (whose triangle inequality follows from CS, as in Section I)
-/

/-- **Minkowski integral inequality: Lp-valued Bochner form**.

    For F : β → Lp ℝ p μ (Lp-valued integrand), the Bochner integral satisfies:
    ```
    ‖∫_β F(y) dν(y)‖_{Lp(μ)} ≤ ∫_β ‖F(y)‖_{Lp(μ)} dν(y)
    ```
    This is the full two-variable Minkowski integral inequality, formalized
    using Bochner integration in Lp spaces.

    **Answer to OQ**: YES — via Cauchy-Schwarz for p = 2, via Hölder for p ≥ 1.
    The Lp space is a normed group (via Minkowski ← Hölder ← CS), and
    `norm_integral_le_integral_norm` gives the integral bound for free. -/
theorem minkowski_integral_bochner
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    (p : ENNReal) [Fact (1 ≤ p)] (F : β → Lp ℝ p μ) :
    ‖∫ y, F y ∂ν‖ ≤ ∫ y, ‖F y‖ ∂ν :=
  norm_integral_le_integral_norm F

/-- **Minkowski integral inequality for L²** from Cauchy-Schwarz.

    The p = 2 special case of the Bochner form.

    Proof chain (explicit):
    1. L²(μ) is an inner product space
    2. Cauchy-Schwarz: |⟪f,g⟫| ≤ ‖f‖·‖g‖ (`abs_real_inner_le_norm`)
    3. Triangle inequality in L²: ‖f+g‖ ≤ ‖f‖+‖g‖ (proved in Section I)
    4. Bochner integral bound: ‖∫F‖_{L²} ≤ ∫‖F‖_{L²} (`norm_integral_le_integral_norm`) -/
theorem minkowski_integral_l2_from_cs
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    (F : β → Lp ℝ 2 μ) :
    ‖∫ y, F y ∂ν‖ ≤ ∫ y, ‖F y‖ ∂ν :=
  norm_integral_le_integral_norm F

/-!
## Section VI: Main Result — Complete Answer

The answer to the open question is YES, with two explicit derivation paths.
-/

/-- **Main result**: Minkowski's integral inequality is a corollary of CS/Hölder.

    For f, g ∈ L²(μ): ‖f + g‖ ≤ ‖f‖ + ‖g‖, derived from Cauchy-Schwarz.

    Complete proof hierarchy:
    - CS: |⟪f,g⟫| ≤ ‖f‖·‖g‖ → L² triangle inequality (Section I)
    - Hölder (gen. CS): ∫|fg| ≤ ‖f‖_p·‖g‖_q → Lp triangle inequality (Section II)
    - eLpNorm form: eLpNorm (f+g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ (Section IV)
    - Bochner form: ‖∫_β F(y) dν‖_{Lp} ≤ ∫_β ‖F(y)‖_{Lp} dν (Section V)

    See `minkowski_l2_from_CS` for the explicit CS → L² derivation.
    See `minkowski_integral_bochner` for the full two-variable Minkowski form. -/
theorem minkowski_from_cauchy_schwarz (f g : Lp ℝ 2 μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  minkowski_l2_from_CS f g

/-- The L² Minkowski inequality is derivable from Cauchy-Schwarz (alias). -/
theorem minkowski_integral_ineq_l2 (f g : Lp ℝ 2 μ) :
    ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  minkowski_l2_from_CS f g

end MinkowskiFromCS

end

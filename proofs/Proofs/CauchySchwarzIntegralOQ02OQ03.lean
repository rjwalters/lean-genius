import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-
# Reverse Minkowski Inequality from Cauchy-Schwarz (cauchy-schwarz-integral-oq-02-oq-03)

## The Open Question (from cauchy-schwarz-integral-oq-02)

> Can the **reverse Minkowski inequality** `‖f+g‖_p ≥ |‖f‖_p − ‖g‖_p|` also be derived
> from Cauchy-Schwarz?

The parent (`cauchy-schwarz-integral-oq-02`) derives the forward Minkowski inequality
`‖f+g‖_p ≤ ‖f‖_p + ‖g‖_p` from Cauchy-Schwarz (inner-product form for `p = 2`, Hölder
for general `p`). This file answers the reverse question.

## The Answer: YES

**Reverse Minkowski (reverse triangle inequality):**
```
|‖f‖_p − ‖g‖_p| ≤ ‖f + g‖_p
```

### Path 1: L² and abstract inner-product spaces — directly from CS

For `p = 2`, just as the *forward* inequality uses the CS *upper* bound
`⟪f,g⟫ ≤ ‖f‖·‖g‖`, the reverse inequality uses the CS *lower* bound
`⟪f,g⟫ ≥ −‖f‖·‖g‖`:
```
‖f+g‖² = ‖f‖² + 2⟪f,g⟫ + ‖g‖²
        ≥ ‖f‖² − 2‖f‖·‖g‖ + ‖g‖²    (by CS: ⟪f,g⟫ ≥ −‖f‖·‖g‖)
        = (‖f‖ − ‖g‖)²
```
Taking square roots gives `|‖f‖ − ‖g‖| ≤ ‖f+g‖`.

### Path 2: General Lᵖ — from the forward triangle inequality

For general `p ≥ 1` the reverse inequality follows from the *forward* one
(which the parent derived from CS/Hölder): writing `f = (f+g) − g`,
```
‖f‖ ≤ ‖f+g‖ + ‖g‖   ⟹   ‖f‖ − ‖g‖ ≤ ‖f+g‖,
```
and symmetrically `‖g‖ − ‖f‖ ≤ ‖f+g‖`, hence `|‖f‖ − ‖g‖| ≤ ‖f+g‖`.

## Status (0 axioms, 0 sorries)
-/

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace ReverseMinkowskiFromCS

/-!
## Section I: Reverse Minkowski from the CS lower bound (inner-product spaces)
-/

/-- **Reverse Minkowski for L² via Cauchy-Schwarz.** For `f, g ∈ L²(μ)`,
    `|‖f‖ − ‖g‖| ≤ ‖f + g‖`, proved from the CS *lower* bound
    `⟪f,g⟫ ≥ −‖f‖·‖g‖` and the norm-squared identity. -/
theorem reverse_minkowski_l2_from_CS (f g : Lp ℝ 2 μ) :
    |‖f‖ - ‖g‖| ≤ ‖f + g‖ := by
  have h_cs : |@inner ℝ _ _ f g| ≤ ‖f‖ * ‖g‖ := abs_real_inner_le_norm f g
  have h_ge : -(‖f‖ * ‖g‖) ≤ @inner ℝ _ _ f g := (abs_le.mp h_cs).1
  have h_sq : (‖f‖ - ‖g‖) ^ 2 ≤ ‖f + g‖ ^ 2 := by
    rw [norm_add_sq_real]; nlinarith [h_ge]
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h_sqrt

/-- **Reverse Minkowski in any real inner-product space**, from Cauchy-Schwarz.
    The abstract version of `reverse_minkowski_l2_from_CS`. -/
theorem reverse_minkowski_inner_product_space {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    |‖u‖ - ‖v‖| ≤ ‖u + v‖ := by
  have h_cs : |@inner ℝ _ _ u v| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v
  have h_ge : -(‖u‖ * ‖v‖) ≤ @inner ℝ _ _ u v := (abs_le.mp h_cs).1
  have h_sq : (‖u‖ - ‖v‖) ^ 2 ≤ ‖u + v‖ ^ 2 := by
    rw [norm_add_sq_real]; nlinarith [h_ge]
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h_sqrt

/-!
## Section II: Reverse Minkowski for general Lᵖ from the forward triangle inequality

For `p ≠ 2` we use the forward Minkowski inequality (which the parent derived from
CS/Hölder). This works in *any* normed group, so we prove it there and specialize.
-/

/-- **Reverse triangle inequality in any normed group.** `|‖u‖ − ‖v‖| ≤ ‖u + v‖`.
    Derived purely from the forward triangle inequality `norm_sub_le`. -/
theorem reverse_minkowski_norm {E : Type*} [NormedAddCommGroup E] (u v : E) :
    |‖u‖ - ‖v‖| ≤ ‖u + v‖ := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · have : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
      calc ‖u‖ = ‖(u + v) - v‖ := by rw [add_sub_cancel_right]
        _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le _ _
    linarith
  · have : ‖v‖ ≤ ‖u + v‖ + ‖u‖ := by
      calc ‖v‖ = ‖(u + v) - u‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖u + v‖ + ‖u‖ := norm_sub_le _ _
    linarith

/-- **Reverse Minkowski for general Lᵖ** (`1 ≤ p`): `|‖f‖_p − ‖g‖_p| ≤ ‖f + g‖_p`.
    Specialization of `reverse_minkowski_norm` to `Lp ℝ p μ`. -/
theorem reverse_minkowski_lp (p : ENNReal) [Fact (1 ≤ p)] (f g : Lp ℝ p μ) :
    |‖f‖ - ‖g‖| ≤ ‖f + g‖ :=
  reverse_minkowski_norm f g

/-!
## Section III: One-sided and difference forms
-/

/-- One-sided reverse Minkowski: `‖f‖_p − ‖g‖_p ≤ ‖f + g‖_p` (no absolute value). -/
theorem norm_sub_norm_le_norm_add {E : Type*} [NormedAddCommGroup E] (u v : E) :
    ‖u‖ - ‖v‖ ≤ ‖u + v‖ :=
  le_trans (le_abs_self _) (reverse_minkowski_norm u v)

/-- The classical reverse triangle inequality in difference form:
    `|‖f‖_p − ‖g‖_p| ≤ ‖f − g‖_p`. Obtained from `reverse_minkowski_norm` by replacing
    `v` with `−v`. -/
theorem reverse_minkowski_sub {E : Type*} [NormedAddCommGroup E] (u v : E) :
    |‖u‖ - ‖v‖| ≤ ‖u - v‖ := by
  have h := reverse_minkowski_norm u (-v)
  rwa [norm_neg, ← sub_eq_add_neg] at h

/-- A lower bound on the Lᵖ norm of a sum: `‖f + g‖_p ≥ ‖f‖_p − ‖g‖_p`. This is the
    inequality exactly as posed in the open question. -/
theorem norm_add_ge_norm_sub_norm (p : ENNReal) [Fact (1 ≤ p)] (f g : Lp ℝ p μ) :
    ‖f‖ - ‖g‖ ≤ ‖f + g‖ :=
  norm_sub_norm_le_norm_add f g

end ReverseMinkowskiFromCS

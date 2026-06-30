/-
# Minkowski's Inequality in L^p (OQ-01)

The triangle inequality for the L^p norm — **Minkowski's inequality**:

  ‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p

is the genuinely infinite-dimensional generalization of the elementary
triangle inequality `‖x + y‖ ≤ ‖x‖ + ‖y‖`. It is the statement that makes
`L^p` a *normed* space: without it the L^p "norm" would only be a
seminorm-shaped functional with no guarantee that the unit ball is convex.

This OQ assembles the Minkowski toolkit at three levels:

- **Seminorm level** (`eLpNorm`): the raw inequality on the extended
  nonnegative reals `ℝ≥0∞`, valid for any a.e.-strongly-measurable
  functions and any exponent `1 ≤ p ≤ ∞`. This is the analytic heart.
- **Closure level** (`MemLp`): `L^p` is closed under addition and finite
  sums — exactly what Minkowski guarantees (`f, g ∈ L^p ⇒ f + g ∈ L^p`).
- **Bundled level** (`Lp E p μ`): the inequality for the honest real-valued
  norm on the quotient Banach space, together with its metric and
  finite-sum consequences.

We also record the **sub-additive failure for `p < 1`**: there Minkowski
holds only up to a constant `2^(1/p − 1) > 1`, witnessing that `L^p` is a
genuine normed space precisely on the range `1 ≤ p`.

**Status**: Complete — 0 sorries, 0 axioms
**Extends**: TriangleInequality.lean (the elementary normed/metric forms)
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

open scoped ENNReal NNReal

namespace TriangleInequalityOQ01

open MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E]
variable {p : ℝ≥0∞} {f g : α → E}

-- ══════════════════════════════════════════════════════════════════
-- § Part I: Minkowski for the L^p seminorm (the analytic heart)
-- ══════════════════════════════════════════════════════════════════

/-
`eLpNorm f p μ : ℝ≥0∞` is the L^p seminorm, valued in the extended
nonnegative reals so that it is always defined (possibly `∞`) without a
membership hypothesis. Minkowski's inequality at this level is the
statement from which every other form below is derived.
-/

/-- **Minkowski's inequality** for the `L^p` seminorm: for `1 ≤ p`,
    the seminorm of a sum is bounded by the sum of the seminorms.
    This is the core analytic estimate underlying the triangle inequality
    on `L^p`. -/
theorem eLpNorm_add_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp1 : 1 ≤ p) :
    eLpNorm (f + g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ :=
  MeasureTheory.eLpNorm_add_le hf hg hp1

/-- The subtractive Minkowski inequality: `‖f − g‖_p ≤ ‖f‖_p + ‖g‖_p`.
    Follows from the additive form since negation preserves the seminorm. -/
theorem eLpNorm_sub_le (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hp1 : 1 ≤ p) :
    eLpNorm (f - g) p μ ≤ eLpNorm f p μ + eLpNorm g p μ :=
  MeasureTheory.eLpNorm_sub_le hf hg hp1

/-- **Iterated Minkowski**: the seminorm of a finite sum is bounded by the
    sum of the seminorms. This is the `n`-fold triangle inequality on `L^p`. -/
theorem eLpNorm_sum_le {ι : Type*} {F : ι → α → E} {s : Finset ι}
    (hF : ∀ i ∈ s, AEStronglyMeasurable (F i) μ) (hp1 : 1 ≤ p) :
    eLpNorm (∑ i ∈ s, F i) p μ ≤ ∑ i ∈ s, eLpNorm (F i) p μ :=
  MeasureTheory.eLpNorm_sum_le hF hp1

-- ══════════════════════════════════════════════════════════════════
-- § Part II: Minkowski below the convex range (p < 1)
-- ══════════════════════════════════════════════════════════════════

/-
For `0 < p < 1` the L^p "norm" is **not** subadditive: the triangle
inequality fails and is replaced by a quasi-triangle inequality with a
constant `LpAddConst p = 2^(1/p − 1) > 1`. The two results below make
precise that `1 ≤ p` is exactly the threshold at which Minkowski (constant
`= 1`) holds. This is why `L^p` is a normed space precisely for `p ≥ 1`.
-/

/-- The general quasi-triangle inequality valid for **every** exponent `p`:
    `‖f + g‖_p ≤ C_p · (‖f‖_p + ‖g‖_p)` where `C_p = LpAddConst p`. -/
theorem eLpNorm_add_le_const (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f + g) p μ ≤ LpAddConst p * (eLpNorm f p μ + eLpNorm g p μ) :=
  MeasureTheory.eLpNorm_add_le' hf hg p

/-- On the Minkowski range `1 ≤ p` the constant collapses to `1`, recovering
    the honest triangle inequality. This pins down `1 ≤ p` as the exact
    convexity threshold. -/
theorem LpAddConst_eq_one (hp1 : 1 ≤ p) : LpAddConst p = 1 :=
  MeasureTheory.LpAddConst_of_one_le hp1

-- ══════════════════════════════════════════════════════════════════
-- § Part III: L^p is closed under addition (Minkowski as closure)
-- ══════════════════════════════════════════════════════════════════

/-
The membership predicate `MemLp f p μ` says `f` is a.e.-strongly-measurable
with finite `L^p` seminorm. Minkowski's inequality is precisely what shows
this predicate is closed under addition and finite sums, so that `L^p` is a
vector subspace of the measurable functions.
-/

/-- `L^p` is closed under addition: if `f, g ∈ L^p` then `f + g ∈ L^p`.
    This is the structural consequence of Minkowski's inequality that makes
    `L^p` a vector space. -/
theorem memLp_add (hf : MemLp f p μ) (hg : MemLp g p μ) : MemLp (f + g) p μ :=
  hf.add hg

/-- `L^p` is closed under finite sums. -/
theorem memLp_finset_sum {ι : Type*} (s : Finset ι) {F : ι → α → E}
    (hF : ∀ i ∈ s, MemLp (F i) p μ) : MemLp (fun a => ∑ i ∈ s, F i a) p μ :=
  MeasureTheory.memLp_finset_sum s hF

-- ══════════════════════════════════════════════════════════════════
-- § Part IV: Minkowski on the bundled Banach space `Lp E p μ`
-- ══════════════════════════════════════════════════════════════════

/-
`Lp E p μ` is the quotient Banach space: equivalence classes of `L^p`
functions modulo a.e.-equality, equipped with the genuine real-valued norm
`‖f‖ = (eLpNorm f p μ).toReal`. For `Fact (1 ≤ p)` this norm satisfies the
triangle inequality — i.e. Minkowski — making `Lp E p μ` a normed (indeed
Banach) space. We expose Minkowski and its standard consequences here.
-/

variable [hp : Fact (1 ≤ p)]

/-- **Minkowski's inequality on the bundled space** `Lp E p μ`: the real
    L^p norm is subadditive. This is the triangle inequality witnessing that
    `Lp E p μ` is a normed space. -/
theorem lp_norm_add_le (f g : Lp E p μ) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  norm_add_le f g

/-- The L^p norm relates to the seminorm by `‖f‖ = (eLpNorm f p μ).toReal`. -/
omit hp in
theorem lp_norm_def (f : Lp E p μ) : ‖f‖ = (eLpNorm f p μ).toReal :=
  Lp.norm_def f

/-- **Reverse triangle inequality** on `Lp E p μ`: `|‖f‖ − ‖g‖| ≤ ‖f − g‖`.
    A direct consequence of Minkowski for the bundled norm. -/
theorem lp_abs_norm_sub_norm_le (f g : Lp E p μ) : |‖f‖ - ‖g‖| ≤ ‖f - g‖ :=
  abs_norm_sub_norm_le f g

/-- The **metric triangle inequality** on `Lp E p μ`, the distance-form of
    Minkowski: `dist f h ≤ dist f g + dist g h`. -/
theorem lp_dist_triangle (f g h : Lp E p μ) : dist f h ≤ dist f g + dist g h :=
  dist_triangle f g h

/-- **Iterated Minkowski on the bundled space**: the norm of a finite sum is
    bounded by the sum of the norms. -/
theorem lp_norm_sum_le {ι : Type*} (s : Finset ι) (F : ι → Lp E p μ) :
    ‖∑ i ∈ s, F i‖ ≤ ∑ i ∈ s, ‖F i‖ :=
  norm_sum_le s F

-- ══════════════════════════════════════════════════════════════════
-- § Part V: Named instances p = 1 and p = 2
-- ══════════════════════════════════════════════════════════════════

/-
The two most important exponents instantiate the general theorem. `p = 1`
is the `L¹` (integrable) case; `p = 2` is the Hilbert space `L²` whose
Minkowski inequality is the triangle inequality for the inner-product norm.
-/

/-- Minkowski for `L¹`: `‖f + g‖₁ ≤ ‖f‖₁ + ‖g‖₁`. -/
theorem l1_norm_add_le (f g : Lp E 1 μ) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  norm_add_le f g

/-- Minkowski for `L²` (the Hilbert-space triangle inequality):
    `‖f + g‖₂ ≤ ‖f‖₂ + ‖g‖₂`. -/
theorem l2_norm_add_le (f g : Lp E 2 μ) : ‖f + g‖ ≤ ‖f‖ + ‖g‖ :=
  norm_add_le f g

/-
## Why Minkowski Holds

The seminorm inequality `eLpNorm_add_le` reduces, after stripping the outer
`(·)^(1/p)`, to the integral form

  (∫ ‖f + g‖^p)^(1/p) ≤ (∫ ‖f‖^p)^(1/p) + (∫ ‖g‖^p)^(1/p),

which Mathlib proves from `ENNReal.lintegral_Lp_add_le` — itself a
consequence of Hölder's inequality applied to the splitting

  ‖f + g‖^p ≤ (‖f‖ + ‖g‖)·‖f + g‖^{p−1}.

The pointwise triangle inequality `‖(f + g) a‖ ≤ ‖f a‖ + ‖g a‖` (Part I of
the parent `TriangleInequality` entry) seeds the argument; Hölder converts
it into the integral bound; and `1 ≤ p` is exactly what makes the dual
exponent `p/(p−1)` admissible. For `p < 1` the dual exponent is negative,
Hölder reverses, and only the weaker constant-`2^(1/p−1)` bound of Part II
survives.
-/

end TriangleInequalityOQ01

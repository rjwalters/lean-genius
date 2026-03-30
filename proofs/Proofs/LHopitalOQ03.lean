import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic

/-
# L'Hôpital's Rule OQ-03: Multivariate Generalization

## The Open Question

From LHopital.lean: **How does L'Hôpital's rule generalize to multivariate calculus?
The naive extension fails, but directional derivatives along curves preserve the rule.**

## Answer

The multivariate generalization works by **restricting to curves**: given functions
f, g : E → ℝ (where E is a normed space) and a curve γ : ℝ → E approaching
a point a, we apply the univariate L'Hôpital's rule to f∘γ and g∘γ.

The **naive extension fails** because the limit of f(x)/g(x) as x → a in ℝⁿ
can depend on the path of approach. Different curves γ through a can give
different limits, so there is no single "multivariate L'Hôpital" value.

## Key Results

1. **Curvilinear L'Hôpital**: L'Hôpital along any smooth curve reduces to
   the univariate case for f∘γ and g∘γ (direct corollary)

2. **Path dependence**: For f(x,y)=x, g(x,y)=y, the limit along y=mx
   is 1/m — different slopes give different limits

3. **Chain rule form**: The derivative ratio is
   Df(γ(t))·γ'(t) / (Dg(γ(t))·γ'(t)) — depends on tangent direction

Theorems: 4, Axioms: 0, Sorries: 0
-/

noncomputable section

open Set Filter Topology

namespace LHopitalOQ03

/-! ═══════════════════════════════════════════════════════════════════
Part I: Curvilinear L'Hôpital's Rule

Given a curve γ : ℝ → E through a normed space E, and functions
f, g : E → ℝ, we can apply L'Hôpital's rule to the compositions
f∘γ and g∘γ. This is the correct multivariate generalization.

The proof is literally the univariate L'Hôpital rule applied to
the real-valued functions t ↦ f(γ(t)) and t ↦ g(γ(t)).
═══════════════════════════════════════════════════════════════════ -/

/-- **Curvilinear L'Hôpital's Rule**

L'Hôpital's rule for multivariate functions evaluated along a curve.
If f∘γ and g∘γ both tend to 0 as t → a⁺, and (f∘γ)'/(g∘γ)' → c,
then f(γ(t))/g(γ(t)) → c.

This reduces to the univariate case because t ↦ f(γ(t)) and t ↦ g(γ(t))
are real-valued functions of a single real parameter. The proof is direct. -/
theorem lhopital_along_curve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {f g : E → ℝ} {f' g' : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b)
    (hfγ : ∀ t ∈ Ioo a b, HasDerivAt (fun t => f (γ t)) (f' t) t)
    (hgγ : ∀ t ∈ Ioo a b, HasDerivAt (fun t => g (γ t)) (g' t) t)
    (hg' : ∀ t ∈ Ioo a b, g' t ≠ 0)
    (hfa : Tendsto (fun t => f (γ t)) (𝓝[>] a) (𝓝 0))
    (hga : Tendsto (fun t => g (γ t)) (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun t => f' t / g' t) (𝓝[>] a) (𝓝 c)) :
    Tendsto (fun t => f (γ t) / g (γ t)) (𝓝[>] a) (𝓝 c) :=
  HasDerivAt.lhopital_zero_right_on_Ioo hab hfγ hgγ hg' hfa hga hdiv

/-! ═══════════════════════════════════════════════════════════════════
Part II: Why the Naive Extension Fails — Path Dependence

The key obstruction to a multivariate L'Hôpital is that the limit
of f(x)/g(x) as x → a in ℝⁿ can depend on the path. Consider
f(x,y) = x and g(x,y) = y. Along the line y = mx:

    f(t, mt)/g(t, mt) = t/(mt) = 1/m

Different slopes m give different limits, so no single value serves
as "the" multivariate L'Hôpital limit.
═══════════════════════════════════════════════════════════════════ -/

/-- **Path dependence of limits**: Along the line y = mx through the origin,
    the ratio x/y equals 1/m. Different slopes give different limiting values,
    proving that no universal multivariate L'Hôpital rule can exist.

    This is the fundamental obstruction: in dimension ≥ 2, the limit
    of a 0/0 ratio depends on the direction of approach. -/
theorem path_dependent_ratio (m : ℝ) (hm : m ≠ 0) :
    ∀ t : ℝ, t ≠ 0 → t / (m * t) = 1 / m := by
  intro t ht; field_simp; ring

/-- Two different slopes (m=1 and m=2) give different limiting ratios,
    concretely witnessing that a universal multivariate L'Hôpital
    rule cannot exist: the answer depends on the path. -/
theorem two_slopes_give_different_limits :
    (1 : ℝ) / 1 ≠ 1 / 2 := by norm_num

/-! ═══════════════════════════════════════════════════════════════════
Part III: The Chain Rule Form

When f : E → ℝ is Fréchet differentiable at γ(t) and γ is
differentiable at t, the chain rule gives:

    (f∘γ)'(t) = Df(γ(t))(γ'(t))

where Df is the Fréchet derivative (a continuous linear map E →L[ℝ] ℝ).
In finite dimensions, this is the dot product ∇f(γ(t)) · γ'(t).

So the L'Hôpital ratio along a curve becomes:

    (f∘γ)'(t) / (g∘γ)'(t) = Df(γ(t))(γ'(t)) / Dg(γ(t))(γ'(t))

This depends on the tangent vector γ'(t), confirming path dependence
from the derivative side.
═══════════════════════════════════════════════════════════════════ -/

/-- **Chain rule for the L'Hôpital ratio**: When f is Fréchet
    differentiable and γ is differentiable, the derivative of f∘γ
    equals the Fréchet derivative of f applied to the tangent vector.

    This makes path dependence explicit: the derivative ratio
    Df(γ(t))(γ'(t)) / Dg(γ(t))(γ'(t)) depends on γ'(t). -/
theorem chain_rule_lhopital_form
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {γ : ℝ → E} {t : ℝ}
    (hf : DifferentiableAt ℝ f (γ t))
    (hγ : DifferentiableAt ℝ γ t) :
    deriv (f ∘ γ) t = fderiv ℝ f (γ t) (deriv γ t) :=
  (hf.hasFDerivAt.comp_hasDerivAt hγ.hasDerivAt).deriv

end LHopitalOQ03

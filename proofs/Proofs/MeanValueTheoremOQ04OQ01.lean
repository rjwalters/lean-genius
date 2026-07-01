/-
Mean Value Theorem OQ-04-OQ-01: The Gradient Theorem — Multivariable FTC from 1D FTC

**Question (parent `mean-value-theorem-oq-04`, open question 1).** Can a
multivariable fundamental theorem of calculus — the differential-forms Stokes'
theorem `∫_M dω = ∫_{∂M} ω` — be *derived* from the one-dimensional FTC?

**Answer (this entry).** The full differential-forms Stokes' theorem for
`k`-manifolds is far beyond a single formalization step (it requires an
oriented-manifold / differential-forms library). But the honestly-scaled,
directly-derivable case is the **gradient theorem** (a.k.a. the *fundamental
theorem for line integrals* / the fundamental theorem of calculus for line
integrals): the `0`-form / `1`-form instance of Stokes on a curve. It says that
the line integral of a gradient (exact) field along a path depends only on the
endpoints,
$$
  \int_a^b \langle \nabla g(\gamma(t)),\, \gamma'(t)\rangle \, dt
    = g(\gamma(b)) - g(\gamma(a)),
$$
and it is a *one-line corollary* of the 1D FTC composed with the chain rule:
setting `h := g ∘ γ`, the chain rule gives `h'(t) = Dg(γ(t))[γ'(t)]`, and the 1D
FTC `∫_a^b h' = h(b) - h(a)` finishes.

This file formalizes exactly that derivation, in two flavors:

1. A general **Fréchet-derivative** form `line_integral_fderiv_eq_sub` over an
   arbitrary real normed space `E`, where the "gradient" is the Fréchet
   derivative `Dg t : E →L[ℝ] ℝ` and the integrand is `Dg t (γ' t)`. The proof
   is `HasFDerivAt.comp_hasDerivAt` (chain rule) piped into
   `intervalIntegral.integral_eq_sub_of_hasDerivAt` (the 1D FTC).

2. The classical **inner-product / gradient** form `gradient_theorem` over a
   real Hilbert space, where the integrand is the genuine inner product
   `⟪∇g(γ(t)), γ'(t)⟫`. This is obtained from the Fréchet form by identifying
   `HasGradientAt g (grad t) (γ t)` with `HasFDerivAt g (toDual ℝ F (grad t))`
   and rewriting `toDual ℝ F v w = ⟪v, w⟫` (`InnerProductSpace.toDual_apply_apply`).

From each we read off the two structural corollaries that make "exact field ⇒
path only depends on endpoints" precise: the circulation of a gradient field
around any **closed** loop vanishes (`*_closed`), and the line integral is
**path-independent** (`*_path_independent`). These are the conservative-field
laws of vector calculus, here proved as pure consequences of the 1D FTC.

No axioms, no sorries; every result is a corollary of Mathlib's 1D FTC and the
chain rule.
-/
import Mathlib

open MeasureTheory intervalIntegral
open scoped RealInnerProductSpace

namespace MeanValueTheoremOQ04OQ01

/-! ## Part I: The gradient theorem in Fréchet-derivative form

Over an arbitrary real normed space `E`, the "gradient field" of `g : E → ℝ` is
its Fréchet derivative `Dg t : E →L[ℝ] ℝ` at the point `γ t`, and the line
integral of the field along `γ` is `∫ Dg t (γ' t)`. -/

section FDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Gradient theorem (Fréchet form) / fundamental theorem for line integrals.**

For `g : E → ℝ` with Fréchet derivative `Dg t` at `γ t`, along a path `γ` with
velocity `γ' t`, the line integral of the exact `1`-form `Dg` pulls back to the
endpoint difference:
`∫_a^b Dg(t)[γ'(t)] dt = g(γ b) - g(γ a)`.

**This is the `0`-form case of Stokes' theorem** `∫_M dω = ∫_{∂M} ω`: the curve
`γ : [a,b] → E` is the `1`-chain `M`, its oriented boundary `∂M` is the point
pair `{γ b} - {γ a}`, and `ω = g` is a `0`-form with `dω = Dg`.

*Proof.* The composite `g ∘ γ` has derivative `t ↦ Dg(t)[γ'(t)]` by the chain
rule (`HasFDerivAt.comp_hasDerivAt`); the claim is then the 1D FTC
(`intervalIntegral.integral_eq_sub_of_hasDerivAt`) applied to `g ∘ γ`. -/
theorem line_integral_fderiv_eq_sub
    {g : E → ℝ} {Dg : ℝ → (E →L[ℝ] ℝ)} {γ γ' : ℝ → E} {a b : ℝ}
    (hg : ∀ t ∈ Set.uIcc a b, HasFDerivAt g (Dg t) (γ t))
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hint : IntervalIntegrable (fun t => Dg t (γ' t)) volume a b) :
    ∫ t in a..b, Dg t (γ' t) = g (γ b) - g (γ a) := by
  have hcomp : ∀ t ∈ Set.uIcc a b, HasDerivAt (g ∘ γ) (Dg t (γ' t)) t :=
    fun t ht => (hg t ht).comp_hasDerivAt t (hγ t ht)
  have h := integral_eq_sub_of_hasDerivAt hcomp hint
  simpa only [Function.comp] using h

/-- **Vanishing circulation of a gradient field around a closed loop.** If the
path is closed (`γ a = γ b`), the line integral of the exact `1`-form `Dg`
vanishes: a conservative field does no net work around any loop. -/
theorem line_integral_fderiv_closed
    {g : E → ℝ} {Dg : ℝ → (E →L[ℝ] ℝ)} {γ γ' : ℝ → E} {a b : ℝ}
    (hg : ∀ t ∈ Set.uIcc a b, HasFDerivAt g (Dg t) (γ t))
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hint : IntervalIntegrable (fun t => Dg t (γ' t)) volume a b)
    (hclosed : γ a = γ b) :
    ∫ t in a..b, Dg t (γ' t) = 0 := by
  rw [line_integral_fderiv_eq_sub hg hγ hint, hclosed, sub_self]

/-- **Path independence of the line integral of a gradient field.** Two paths
`γ₁`, `γ₂` with matching endpoints (`γ₁ a = γ₂ c`, `γ₁ b = γ₂ d`) give the same
line integral of the exact `1`-form `Dg` of the *same* potential `g` — because
each integral equals the endpoint difference `g(end) - g(start)`. -/
theorem line_integral_fderiv_path_independent
    {g : E → ℝ} {Dg₁ Dg₂ : ℝ → (E →L[ℝ] ℝ)} {γ₁ γ₁' γ₂ γ₂' : ℝ → E} {a b c d : ℝ}
    (hg₁ : ∀ t ∈ Set.uIcc a b, HasFDerivAt g (Dg₁ t) (γ₁ t))
    (hγ₁ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ₁ (γ₁' t) t)
    (hint₁ : IntervalIntegrable (fun t => Dg₁ t (γ₁' t)) volume a b)
    (hg₂ : ∀ t ∈ Set.uIcc c d, HasFDerivAt g (Dg₂ t) (γ₂ t))
    (hγ₂ : ∀ t ∈ Set.uIcc c d, HasDerivAt γ₂ (γ₂' t) t)
    (hint₂ : IntervalIntegrable (fun t => Dg₂ t (γ₂' t)) volume c d)
    (hstart : γ₁ a = γ₂ c) (hend : γ₁ b = γ₂ d) :
    ∫ t in a..b, Dg₁ t (γ₁' t) = ∫ t in c..d, Dg₂ t (γ₂' t) := by
  rw [line_integral_fderiv_eq_sub hg₁ hγ₁ hint₁,
      line_integral_fderiv_eq_sub hg₂ hγ₂ hint₂, hstart, hend]

end FDeriv

/-! ## Part II: The classical gradient theorem (inner-product form)

Over a real Hilbert space `F`, the gradient `grad t = ∇g(γ t) : F` and the
integrand is the genuine inner product `⟪grad t, γ' t⟫`. This is the vector
calculus statement `∫ ∇g · dr = g(end) - g(start)`. -/

section Inner

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- **The gradient theorem** (fundamental theorem for line integrals, classical
inner-product form). Over a real Hilbert space `F`, for a potential `g : F → ℝ`
with gradient `grad t = ∇g(γ t)` along a path `γ` with velocity `γ' t`,
`∫_a^b ⟪∇g(γ t), γ'(t)⟫ dt = g(γ b) - g(γ a)`.

*Proof.* `HasGradientAt g (grad t) (γ t)` is by definition
`HasFDerivAt g (toDual ℝ F (grad t)) (γ t)`, and
`toDual ℝ F (grad t) (γ' t) = ⟪grad t, γ' t⟫`
(`InnerProductSpace.toDual_apply_apply`), so this is
`line_integral_fderiv_eq_sub` with `Dg t = toDual ℝ F (grad t)`. -/
theorem gradient_theorem
    {g : F → ℝ} {grad γ γ' : ℝ → F} {a b : ℝ}
    (hg : ∀ t ∈ Set.uIcc a b, HasGradientAt g (grad t) (γ t))
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hint : IntervalIntegrable (fun t => ⟪grad t, γ' t⟫) volume a b) :
    ∫ t in a..b, ⟪grad t, γ' t⟫ = g (γ b) - g (γ a) := by
  have hg' : ∀ t ∈ Set.uIcc a b,
      HasFDerivAt g (InnerProductSpace.toDual ℝ F (grad t)) (γ t) :=
    fun t ht => hasGradientAt_iff_hasFDerivAt.mp (hg t ht)
  have hint' : IntervalIntegrable
      (fun t => InnerProductSpace.toDual ℝ F (grad t) (γ' t)) volume a b := by
    simpa only [InnerProductSpace.toDual_apply_apply] using hint
  have h := line_integral_fderiv_eq_sub hg' hγ hint'
  simpa only [InnerProductSpace.toDual_apply_apply] using h

/-- **Zero circulation of a conservative field.** The line integral of a gradient
field `∇g` around a closed loop (`γ a = γ b`) is zero. -/
theorem gradient_theorem_closed
    {g : F → ℝ} {grad γ γ' : ℝ → F} {a b : ℝ}
    (hg : ∀ t ∈ Set.uIcc a b, HasGradientAt g (grad t) (γ t))
    (hγ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ (γ' t) t)
    (hint : IntervalIntegrable (fun t => ⟪grad t, γ' t⟫) volume a b)
    (hclosed : γ a = γ b) :
    ∫ t in a..b, ⟪grad t, γ' t⟫ = 0 := by
  rw [gradient_theorem hg hγ hint, hclosed, sub_self]

/-- **Path independence of a gradient (conservative) field.** Two paths with
matching endpoints give equal line integrals of `∇g`. -/
theorem gradient_theorem_path_independent
    {g : F → ℝ} {grad₁ γ₁ γ₁' grad₂ γ₂ γ₂' : ℝ → F} {a b c d : ℝ}
    (hg₁ : ∀ t ∈ Set.uIcc a b, HasGradientAt g (grad₁ t) (γ₁ t))
    (hγ₁ : ∀ t ∈ Set.uIcc a b, HasDerivAt γ₁ (γ₁' t) t)
    (hint₁ : IntervalIntegrable (fun t => ⟪grad₁ t, γ₁' t⟫) volume a b)
    (hg₂ : ∀ t ∈ Set.uIcc c d, HasGradientAt g (grad₂ t) (γ₂ t))
    (hγ₂ : ∀ t ∈ Set.uIcc c d, HasDerivAt γ₂ (γ₂' t) t)
    (hint₂ : IntervalIntegrable (fun t => ⟪grad₂ t, γ₂' t⟫) volume c d)
    (hstart : γ₁ a = γ₂ c) (hend : γ₁ b = γ₂ d) :
    ∫ t in a..b, ⟪grad₁ t, γ₁' t⟫ = ∫ t in c..d, ⟪grad₂ t, γ₂' t⟫ := by
  rw [gradient_theorem hg₁ hγ₁ hint₁, gradient_theorem hg₂ hγ₂ hint₂, hstart, hend]

end Inner

end MeanValueTheoremOQ04OQ01

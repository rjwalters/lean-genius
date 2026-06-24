import Mathlib

/-
# Banach Fixed Point OQ-01-OQ-02: Lipschitz Perturbations of the Identity are Homeomorphisms

## Research Problem: banach-fixed-point-oq-01-oq-02

The parent entry `banach-fixed-point-oq-01` poses (open question #2):

  *Formalize the global Newton/Banach perturbation result: if g is a small
  Lipschitz perturbation of the identity, then id + g is a homeomorphism
  (a step toward the inverse function theorem).*

This is the third pillar of the contraction-mapping circle of ideas, alongside the
quantitative fixed-point theorem (parent OQ-01) and Picard–Lindelöf (sibling
OQ-01-OQ-01). Where those *find* a fixed point, this entry *inverts a map*.

## Mathematical Content

Let E be a complete normed (additive) group and let g : E → E be Lipschitz with
constant k < 1. Set

  f(x) = x + g(x).

Then f is a homeomorphism of E onto itself, and its inverse is Lipschitz with the
sharp constant 1/(1 − k). The three ingredients:

1. **Lower bound (antilipschitz).**
     ‖f(x) − f(y)‖ ≥ ‖x − y‖ − ‖g(x) − g(y)‖ ≥ (1 − k)‖x − y‖,
   so f is `AntilipschitzWith (1 − k)⁻¹` — immediately injective, and the bound
   1/(1 − k) is exactly the Lipschitz constant of f⁻¹.

2. **Surjectivity via the contraction principle.** To solve f(x) = y, i.e.
   x + g(x) = y, rewrite it as the fixed-point equation x = y − g(x). The map
   φ_y(x) = y − g(x) is a k-contraction (k < 1), so on the complete space E it has a
   (unique) fixed point x*, and then f(x*) = y. **This is precisely where the parent
   Banach fixed-point theorem powers the inverse.**

3. **Upper bound (Lipschitz).** ‖f(x) − f(y)‖ ≤ (1 + k)‖x − y‖, so f is continuous;
   combined with surjectivity + antilipschitz it is a homeomorphism, and the inverse
   inherits continuity from the antilipschitz lower bound.

The same computation underlies Hadamard's global inverse function theorem and the
local inverse function theorem (where g is the nonlinear remainder of f after
subtracting its derivative); Mathlib's `ApproximatesLinearOn` development is the
abstract linear-model version of exactly this argument.

## References
- S. Banach (1922): contraction mapping principle
- J. Hadamard (1906): global inverse function theorems
- Mathlib: `AntilipschitzWith.add_lipschitzWith`, `ContractingWith.fixedPoint`,
  `AntilipschitzWith.to_rightInverse`, `Equiv.ofBijective`
-/

open scoped NNReal

namespace BanachFixedPointOQ01OQ02

variable {E : Type*} [NormedAddCommGroup E] {k : ℝ≥0} {g : E → E}

/-- The perturbation of the identity by `g`: `f(x) = x + g(x)`. -/
def perturbId (g : E → E) : E → E := fun x => x + g x

@[simp] theorem perturbId_apply (g : E → E) (x : E) : perturbId g x = x + g x := rfl

/-! ## Part I: the two-sided Lipschitz estimates -/

/-- **Upper bound.** `f = id + g` is Lipschitz with constant `1 + k`
    (hence continuous). -/
theorem perturbId_lipschitz (hg : LipschitzWith k g) :
    LipschitzWith (1 + k) (perturbId g) :=
  (LipschitzWith.id.add hg : LipschitzWith (1 + k) fun x => id x + g x)

/-- **Lower bound (antilipschitz).** If `k < 1` then `f = id + g` is
    `AntilipschitzWith (1 − k)⁻¹`. The constant `1/(1 − k)` is the Lipschitz
    constant of the inverse. -/
theorem perturbId_antilipschitz (hg : LipschitzWith k g) (hk : k < 1) :
    AntilipschitzWith (1 - k)⁻¹ (perturbId g) := by
  have hK : k < (1 : ℝ≥0)⁻¹ := by rwa [inv_one]
  have h := (AntilipschitzWith.id (α := E)).add_lipschitzWith hg hK
  rwa [inv_one] at h

/-- f is injective (consequence of the antilipschitz lower bound). -/
theorem perturbId_injective (hg : LipschitzWith k g) (hk : k < 1) :
    Function.Injective (perturbId g) :=
  (perturbId_antilipschitz hg hk).injective

/-! ## Part II: surjectivity via the contraction principle -/

/-- **Surjectivity.** On a complete space, `f = id + g` is surjective: for every
    target `y`, the map `x ↦ y − g(x)` is a `k`-contraction (`k < 1`), so it has a
    fixed point `x*`, and then `f(x*) = x* + g(x*) = y`. This is the Banach
    fixed-point theorem (parent OQ-01) supplying the inverse image. -/
theorem perturbId_surjective [CompleteSpace E] (hg : LipschitzWith k g) (hk : k < 1) :
    Function.Surjective (perturbId g) := by
  haveI : Nonempty E := ⟨0⟩
  intro y
  -- φ_y(x) = y − g(x) is a k-contraction
  have hφ : LipschitzWith k (fun x => y - g x) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      have h : dist (y - g a) (y - g b) = dist (g a) (g b) := by
        rw [dist_eq_norm, dist_eq_norm, show y - g a - (y - g b) = -(g a - g b) by abel,
          norm_neg]
      rw [h]; exact hg.dist_le_mul a b
  have hcon : ContractingWith k (fun x => y - g x) := ⟨hk, hφ⟩
  -- the fixed point x₀ solves x₀ + g x₀ = y
  refine ⟨ContractingWith.fixedPoint _ hcon, ?_⟩
  have hfix : y - g (ContractingWith.fixedPoint _ hcon) = ContractingWith.fixedPoint _ hcon :=
    hcon.fixedPoint_isFixedPt
  rw [perturbId_apply]
  exact (sub_eq_iff_eq_add.mp hfix).symm

/-- **Bijectivity.** On a complete space, `f = id + g` is a bijection. -/
theorem perturbId_bijective [CompleteSpace E] (hg : LipschitzWith k g) (hk : k < 1) :
    Function.Bijective (perturbId g) :=
  ⟨perturbId_injective hg hk, perturbId_surjective hg hk⟩

/-! ## Part III: the homeomorphism and the sharp inverse bound -/

/-- The bijection `f = id + g` as an `Equiv`. -/
noncomputable def perturbIdEquiv [CompleteSpace E] (hg : LipschitzWith k g) (hk : k < 1) :
    E ≃ E :=
  Equiv.ofBijective (perturbId g) (perturbId_bijective hg hk)

@[simp] theorem perturbIdEquiv_apply [CompleteSpace E] (hg : LipschitzWith k g) (hk : k < 1)
    (x : E) : perturbIdEquiv hg hk x = x + g x := rfl

/-- **Sharp inverse bound.** The inverse of `f = id + g` is Lipschitz with constant
    `1/(1 − k)`: `‖f⁻¹(a) − f⁻¹(b)‖ ≤ (1 − k)⁻¹ ‖a − b‖`. Obtained from the
    antilipschitz lower bound on `f` and the fact that `f⁻¹` is a right inverse. -/
theorem perturbIdEquiv_symm_lipschitz [CompleteSpace E] (hg : LipschitzWith k g) (hk : k < 1) :
    LipschitzWith (1 - k)⁻¹ (perturbIdEquiv hg hk).symm :=
  (perturbId_antilipschitz hg hk).to_rightInverse (perturbIdEquiv hg hk).apply_symm_apply

/-- **Headline.** A Lipschitz perturbation `f = id + g` of the identity, with
    Lipschitz constant `k < 1` of `g`, is a homeomorphism of the complete normed
    space `E` onto itself. -/
noncomputable def perturbIdHomeomorph [CompleteSpace E] (hg : LipschitzWith k g) (hk : k < 1) :
    E ≃ₜ E where
  toEquiv := perturbIdEquiv hg hk
  continuous_toFun := (perturbId_lipschitz hg).continuous
  continuous_invFun := (perturbIdEquiv_symm_lipschitz hg hk).continuous

@[simp] theorem perturbIdHomeomorph_apply [CompleteSpace E] (hg : LipschitzWith k g) (hk : k < 1)
    (x : E) : perturbIdHomeomorph hg hk x = x + g x := rfl

/-- The homeomorphism's inverse is Lipschitz with constant `1/(1 − k)`. -/
theorem perturbIdHomeomorph_symm_lipschitz [CompleteSpace E]
    (hg : LipschitzWith k g) (hk : k < 1) :
    LipschitzWith (1 - k)⁻¹ (perturbIdHomeomorph hg hk).symm :=
  perturbIdEquiv_symm_lipschitz hg hk

/-! ## Part IV: a worked instance on ℝ -/

-- g(x) = (1/2)·sin x is (1/2)-Lipschitz, so x ↦ x + (1/2)·sin x is a homeomorphism of ℝ.
example : LipschitzWith (1/2 : ℝ≥0) (fun x : ℝ => (1/2 : ℝ) * Real.sin x) := by
  refine LipschitzWith.of_dist_le_mul fun a b => ?_
  have hsin := Real.lipschitzWith_sin.dist_le_mul a b
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hsin
  rw [Real.dist_eq, Real.dist_eq,
    show (1/2 : ℝ) * Real.sin a - (1/2) * Real.sin b = (1/2) * (Real.sin a - Real.sin b) by ring,
    abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  push_cast
  nlinarith [hsin, abs_nonneg (a - b), abs_nonneg (Real.sin a - Real.sin b)]

/-! ## Part V: Summary -/

/-- **Banach Fixed Point OQ-01-OQ-02 Summary.** For a complete normed space `E` and
    `g : E → E` Lipschitz with constant `k < 1`, the perturbation `f = id + g`:
    (1) is `(1 + k)`-Lipschitz (continuous);
    (2) is `AntilipschitzWith (1 − k)⁻¹` (in particular injective);
    (3) is bijective (surjectivity via the contraction principle on `x ↦ y − g x`);
    (4) is therefore a homeomorphism whose inverse is `(1 − k)⁻¹`-Lipschitz. -/
theorem banach_oq01_oq02_summary [CompleteSpace E] (hg : LipschitzWith k g) (hk : k < 1) :
    LipschitzWith (1 + k) (perturbId g) ∧
    AntilipschitzWith (1 - k)⁻¹ (perturbId g) ∧
    Function.Bijective (perturbId g) ∧
    LipschitzWith (1 - k)⁻¹ (perturbIdHomeomorph hg hk).symm :=
  ⟨perturbId_lipschitz hg,
   perturbId_antilipschitz hg hk,
   perturbId_bijective hg hk,
   perturbIdHomeomorph_symm_lipschitz hg hk⟩

end BanachFixedPointOQ01OQ02

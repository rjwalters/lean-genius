/-
# Euler's Formula as a Smooth Lie Group Exponential Map (OQ-01-OQ-01-OQ-01-OQ-01)

## Open Question

> Can the homomorphism property be packaged as a smooth (i.e. C∞) Lie group
> exponential map in Mathlib's `LieGroup` framework, with the imaginary axis
> `iℝ` identified as the Lie algebra?

## Answer

YES — and Mathlib already supplies the entire framework, so the work is one of
*packaging* rather than building new analysis.

The parent entry `EulerIdentityOQ01OQ01OQ01` proved that `circleMap : t ↦ exp(it)`
is a *continuous* group homomorphism `(ℝ, +) → (ℂˣ, ·)` onto the unit circle.
This file upgrades that to the full Lie-theoretic statement:

1. **The genuine Lie group.** Mathlib's `Circle = {z : ℂ // ‖z‖ = 1}` carries an
   *analytic* Lie group structure `LieGroup (𝓡 1) ω Circle`
   (`Mathlib.Geometry.Manifold.Instances.Sphere`).

2. **Bridge.** Our parent `circleMap` is, on the nose, the coercion of Mathlib's
   Lie group exponential map `Circle.exp : C(ℝ, Circle)`
   (`circleMap_eq_coe_circleExp`).

3. **Smoothness (the requested C∞ property).** `Circle.exp` is `ContMDiff` of
   *every* order `m : WithTop ℕ∞` — in particular C∞ (`m = ∞`) and even analytic
   (`m = ω`) — via `contMDiff_circleExp` (`contMDiff_circleExp_packaged`).

4. **Homomorphism in the genuine group.** `Circle.exp (x + y) = Circle.exp x * Circle.exp y`
   (`circleExp_homomorphism`), packaged abstractly as `Circle.expHom : ℝ →+ Additive Circle`.
   This agrees with the parent's `circleHom` (`circleHom_coe_eq_circleExp`).

5. **Lie algebra `iℝ`.** The one-parameter subgroup satisfies the defining ODE of
   the Lie group exponential, `γ'(t) = γ(t) · I` (`hasDerivAt_circleExp`); at the
   identity the velocity vector is exactly `I` (`hasDerivAt_circleExp_zero`). Thus
   the Lie algebra `T₁ S¹` is the imaginary axis `iℝ ⊆ ℂ`, with generator `i`.

## Status

0 axioms, 0 sorries. Builds on the verified parent `EulerIdentityOQ01OQ01OQ01`
and standard Mathlib manifold/calculus infrastructure.
-/

import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic
import Proofs.EulerIdentityOQ01OQ01OQ01

open Complex Real
open scoped Manifold

namespace EulerIdentityOQ01OQ01OQ01OQ01

/-! ## §1. Bridge: the parent map is Mathlib's Lie group exponential

The parent's `circleMap t = exp(it)` coincides with the coercion of Mathlib's
canonical circle exponential `Circle.exp : C(ℝ, Circle)`. -/

/-- The parent proof's `circleMap` is exactly Mathlib's circle exponential map,
viewed in `ℂ`. This identifies the gallery construction with the object that
Mathlib equips with a smooth Lie group structure. -/
theorem circleMap_eq_coe_circleExp (t : ℝ) :
    EulerIdentityOQ01OQ01OQ01.circleMap t = (Circle.exp t : ℂ) := by
  unfold EulerIdentityOQ01OQ01OQ01.circleMap
  rw [Circle.coe_exp]

/-! ## §2. Smoothness: the C∞ (in fact analytic) Lie group exponential map

`Circle.exp` is `ContMDiff` of every order. The requested "smooth (C∞)" property
is the case `m = ∞`; analyticity is `m = ω`. Stating it for all orders is the
strongest possible answer. -/

/-- **The requested property.** `Circle.exp : ℝ → Circle` is `C^m` for *every*
order `m : WithTop ℕ∞` between the model `𝓘(ℝ, ℝ)` on the source and the
1-dimensional real manifold model `𝓡 1` on the circle. In particular it is
C∞ (`m = ∞`) and analytic (`m = ω`). -/
theorem contMDiff_circleExp_packaged (m : WithTop ℕ∞) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) m Circle.exp :=
  contMDiff_circleExp

/-! ## §3. Homomorphism in the genuine circle group -/

/-- The Lie group exponential is a homomorphism `(ℝ, +) → (Circle, ·)`. -/
theorem circleExp_homomorphism (x y : ℝ) :
    Circle.exp (x + y) = Circle.exp x * Circle.exp y :=
  Circle.exp_add x y

/-- The parent's homomorphism `circleHom : Multiplicative ℝ →* ℂˣ` agrees with
Mathlib's Lie group exponential `Circle.exp`, confirming they package the same
map into different (but compatible) algebraic targets. -/
theorem circleHom_coe_eq_circleExp (t : ℝ) :
    (EulerIdentityOQ01OQ01OQ01.circleHom (Multiplicative.ofAdd t) : ℂ)
      = (Circle.exp t : ℂ) := by
  rw [EulerIdentityOQ01OQ01OQ01.circleHom_apply, circleMap_eq_coe_circleExp]

/-! ## §4. Lie algebra `iℝ`: the left-invariant velocity field

The one-parameter subgroup `t ↦ Circle.exp t` solves the defining ODE of a Lie
group exponential, `γ'(t) = γ(t) · X`, with infinitesimal generator `X = I`. The
velocity at the identity is therefore `I`, exhibiting the Lie algebra of `S¹` as
the imaginary axis `iℝ ⊆ ℂ`. -/

/-- **Defining ODE of the exponential.** The derivative of `t ↦ Circle.exp t`
(in `ℂ`) at any point `t` equals `Circle.exp t · I` — the value times the
Lie-algebra generator `I`. -/
theorem hasDerivAt_circleExp (t : ℝ) :
    HasDerivAt (fun s : ℝ => (Circle.exp s : ℂ)) ((Circle.exp t : ℂ) * Complex.I) t := by
  have hbase : HasDerivAt (fun s : ℝ => (↑s : ℂ)) 1 t := by
    simpa using (hasDerivAt_id t).ofReal_comp
  have hexp := (hbase.mul_const Complex.I).cexp
  simpa using hexp

/-- **Lie algebra generator.** At the identity `t = 0`, the velocity of the
one-parameter subgroup is exactly the imaginary unit `I`. This identifies the
tangent space `T₁ S¹` (the Lie algebra) with the imaginary axis `iℝ`, generated
by `i`. -/
theorem hasDerivAt_circleExp_zero :
    HasDerivAt (fun s : ℝ => (Circle.exp s : ℂ)) Complex.I 0 := by
  simpa using hasDerivAt_circleExp 0

/-- The generator lies on the imaginary axis: `Re(I) = 0` and `Im(I) = 1`,
i.e. the Lie algebra direction is `iℝ`. -/
theorem generator_mem_imaginary_axis : (Complex.I).re = 0 ∧ (Complex.I).im = 1 :=
  ⟨Complex.I_re, Complex.I_im⟩

/-! ## §4b. The integral lattice `2πℤ`: kernel of the exponential

The Lie group exponential `Circle.exp : ℝ → S¹` is surjective with a discrete
kernel. Identifying that kernel is the last structural ingredient of the
ℝ → S¹ picture: it is the *integral lattice* `2πℤ ⊆ iℝ` inside the Lie algebra,
and the induced isomorphism `S¹ ≅ ℝ / 2πℤ` realises the circle as the quotient
of its Lie algebra by this lattice. -/

/-- **Kernel of the exponential = the lattice `2πℤ`.** `Circle.exp t` is the
identity exactly when `t` is an integer multiple of `2π`. This is the period
lattice of the one-parameter subgroup; in Lie-theoretic terms it is the integral
lattice of `S¹` sitting inside the Lie algebra `iℝ`. -/
theorem circleExp_eq_one_iff (t : ℝ) :
    (Circle.exp t : ℂ) = 1 ↔ ∃ n : ℤ, t = n * (2 * π) := by
  rw [Circle.coe_exp, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hI : (t : ℂ) * Complex.I = ((n : ℂ) * (2 * π)) * Complex.I := by
      rw [hn]; ring
    have ht : (t : ℂ) = (n : ℂ) * (2 * π) := mul_right_cancel₀ Complex.I_ne_zero hI
    have : (t : ℂ) = (((n : ℝ) * (2 * π) : ℝ) : ℂ) := by rw [ht]; push_cast; ring
    exact_mod_cast this
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]; push_cast; ring

/-! ## §5. Summary -/

/-- **Packaging complete.** Euler's formula presents `t ↦ exp(it)` as the smooth
Lie group exponential map of the circle group `S¹`:

- it is a homomorphism `(ℝ, +) → (Circle, ·)`;
- it is `C^m` for every order (C∞ and analytic) in Mathlib's `LieGroup` framework;
- its velocity at the identity is the imaginary unit `I`, so the Lie algebra is `iℝ`. -/
theorem main :
    (∀ x y : ℝ, Circle.exp (x + y) = Circle.exp x * Circle.exp y) ∧
    (∀ m : WithTop ℕ∞, ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) m Circle.exp) ∧
    HasDerivAt (fun s : ℝ => (Circle.exp s : ℂ)) Complex.I 0 :=
  ⟨Circle.exp_add, fun m => contMDiff_circleExp_packaged m, hasDerivAt_circleExp_zero⟩

#check @contMDiff_circleExp_packaged
#check @circleMap_eq_coe_circleExp
#check @hasDerivAt_circleExp_zero
#check @circleExp_eq_one_iff
#check @main

end EulerIdentityOQ01OQ01OQ01OQ01

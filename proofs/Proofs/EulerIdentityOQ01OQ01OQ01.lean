/-
# Euler's Formula as a Lie Group Homomorphism (OQ-01-OQ-01-OQ-01)

## Open Question

> Can the proof be extended to prove the Lie group exponential map ℝ → S¹
> is a homomorphism, viewing Euler's formula as the statement that exp(i·)
> is a group homomorphism from (ℝ, +) to (S¹, ×)?

## Answer

YES. Euler's formula `exp(it) = cos t + i·sin t`, combined with the
exponential addition law `exp(z + w) = exp z · exp w`, makes the map
`circleHom : t ↦ exp(it)` from (ℝ, +) to (ℂˣ, ×) a continuous group
homomorphism whose image is exactly the unit circle S¹ = {z : ℂ | ‖z‖ = 1}.

This file proves:
1. `circleHom` is a group homomorphism `Multiplicative ℝ →* ℂˣ`
2. `circleHom` is continuous (so it's a topological group hom)
3. `‖circleHom t‖ = 1` for all t (image lies in S¹)
4. The kernel of `circleHom` is exactly `2π·ℤ`
5. The image of `circleHom` is exactly the unit circle (surjective onto S¹)
6. As a bonus: the homomorphism law gives a one-line proof of de Moivre

## Connection to Lie Theory

`circleHom` is the canonical Lie group exponential map for the circle
group S¹: it is the unique continuous homomorphism `ℝ → S¹` whose
derivative at 0 sends 1 to the imaginary unit i (the Lie algebra of S¹
is `iℝ ⊆ ℂ`). The kernel description `2π·ℤ` exhibits S¹ as the quotient
ℝ/2πℤ as a topological group.

## Foundation

Builds on `EulerIdentityOQ01OQ01.euler_formula`, which proves
`exp(↑x · I) = ↑(cos x) + ↑(sin x) · I` axiom-free. The homomorphism
properties then follow from `Complex.exp_add` and standard real analysis.

## Status

0 axioms, 0 sorries.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Tactic
import Proofs.EulerIdentityOQ01OQ01

open Complex Real

namespace EulerIdentityOQ01OQ01OQ01

/-! ## §1. The Underlying Map: t ↦ exp(it) -/

/-- The complex map `t ↦ exp(it)`, the prototype of a circle parametrization. -/
noncomputable def circleMap (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * I)

@[simp] theorem circleMap_zero : circleMap 0 = 1 := by
  simp [circleMap]

theorem circleMap_add (a b : ℝ) :
    circleMap (a + b) = circleMap a * circleMap b := by
  simp only [circleMap, ofReal_add]
  rw [add_mul, Complex.exp_add]

@[simp] theorem circleMap_neg (t : ℝ) :
    circleMap (-t) = (circleMap t)⁻¹ := by
  have h : circleMap t * circleMap (-t) = 1 := by
    rw [← circleMap_add, add_neg_cancel, circleMap_zero]
  field_simp
  linear_combination h

theorem circleMap_sub (a b : ℝ) :
    circleMap (a - b) = circleMap a * (circleMap b)⁻¹ := by
  rw [sub_eq_add_neg, circleMap_add, circleMap_neg]

/-- **Connection to Euler's formula** (from OQ-01-OQ-01).

`circleMap t = cos t + i · sin t`, the trigonometric form of `exp(it)`. -/
theorem circleMap_eq_cos_add_sin_I (t : ℝ) :
    circleMap t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I := by
  unfold circleMap
  exact EulerIdentityOQ01OQ01.euler_formula t

/-! ## §2. Image Lies on the Unit Circle -/

/-- `circleMap` lands on the unit circle: `|exp(it)| = 1`. -/
theorem norm_circleMap (t : ℝ) : ‖circleMap t‖ = 1 := by
  rw [circleMap_eq_cos_add_sin_I]
  exact Complex.norm_cos_add_sin_mul_I t

/-- `circleMap t` is a unit in ℂ. -/
theorem circleMap_ne_zero (t : ℝ) : circleMap t ≠ 0 := by
  intro h
  have : ‖circleMap t‖ = 0 := by rw [h, norm_zero]
  rw [norm_circleMap] at this
  norm_num at this

/-! ## §3. Group Homomorphism Structure -/

/-- **Main theorem**: `circleMap` packaged as a multiplicative monoid hom
from `Multiplicative ℝ` to `ℂˣ`, the units of ℂ.

This is the formal Lie-group statement: `(ℝ, +) → (ℂˣ, ·)` is a group
homomorphism via the exponential map. -/
noncomputable def circleHom : Multiplicative ℝ →* ℂˣ where
  toFun t := Units.mk0 (circleMap (Multiplicative.toAdd t)) (circleMap_ne_zero _)
  map_one' := by
    ext
    show circleMap (Multiplicative.toAdd (1 : Multiplicative ℝ)) = 1
    show circleMap 0 = 1
    simp
  map_mul' a b := by
    ext
    show circleMap (Multiplicative.toAdd (a * b)) =
         circleMap (Multiplicative.toAdd a) * circleMap (Multiplicative.toAdd b)
    show circleMap (Multiplicative.toAdd a + Multiplicative.toAdd b) =
         circleMap (Multiplicative.toAdd a) * circleMap (Multiplicative.toAdd b)
    exact circleMap_add _ _

@[simp] theorem circleHom_apply (t : ℝ) :
    (circleHom (Multiplicative.ofAdd t) : ℂ) = circleMap t := by
  rfl

/-- Equivalent additive-style statement: `circleMap` is an additive→multiplicative
homomorphism, expressed as the composition of `Multiplicative.ofAdd` and `circleHom`. -/
theorem circleMap_homomorphism (a b : ℝ) :
    (circleMap (a + b) : ℂ) = (circleMap a : ℂ) * (circleMap b : ℂ) :=
  circleMap_add a b

/-! ## §4. Continuity (Topological Group Homomorphism) -/

/-- `circleMap` is continuous as a function `ℝ → ℂ`. -/
theorem continuous_circleMap : Continuous circleMap := by
  unfold circleMap
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

/-- `circleHom` is continuous when ℂˣ has the subspace topology of ℂ.
Combined with the homomorphism property, this exhibits `circleHom` as a
continuous group homomorphism — the Lie group exponential map. -/
theorem continuous_circleHom :
    Continuous (fun t : ℝ => (circleHom (Multiplicative.ofAdd t) : ℂ)) := by
  simpa using continuous_circleMap

/-! ## §5. Kernel: `circleMap t = 1 ↔ t ∈ 2π·ℤ` -/

/-- **Kernel of the Lie group exponential**: `circleMap t = 1` exactly when
`t = 2π·n` for some integer `n`. This identifies the kernel of the
homomorphism `ℝ → S¹` and exhibits S¹ ≅ ℝ/2πℤ. -/
theorem circleMap_eq_one_iff (t : ℝ) :
    circleMap t = 1 ↔ ∃ n : ℤ, t = 2 * π * n := by
  unfold circleMap
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- hn : (t : ℂ) * I = n * (2 * π * I)
    -- Cancel I from both sides, then unwrap reals
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hcomp : (t : ℂ) = (n : ℂ) * (2 * π) := by
      have := hn
      have h2 : (n : ℂ) * (2 * π * Complex.I) = (n * (2 * π)) * Complex.I := by ring
      rw [h2] at this
      exact mul_right_cancel₀ hI this
    have : (t : ℝ) = ((n : ℝ) * (2 * π) : ℝ) := by exact_mod_cast hcomp
    linarith
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    push_cast
    ring

/-! ## §6. Surjectivity onto the Unit Circle -/

/-- **Image of the Lie group exponential** is the entire unit circle.

Every complex number on the unit circle has the form `exp(it)` for some
real `t` (in fact, for any `t = arg z`). This makes S¹ a homogeneous
space under the additive translation action of ℝ. -/
theorem circleMap_surjective_unit_circle (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ t : ℝ, circleMap t = z := by
  refine ⟨Complex.arg z, ?_⟩
  rw [circleMap_eq_cos_add_sin_I]
  -- z = cos(arg z) + sin(arg z) i  when |z| = 1
  have habs : Complex.abs z = 1 := by
    rwa [show Complex.abs z = ‖z‖ from rfl]
  -- Use Complex.abs_mul_cos_add_sin_mul_I-style identity
  have := Complex.abs_mul_cos_add_sin_mul_I z
  rw [habs] at this
  rw [show ((1 : ℝ) : ℂ) * (Real.cos (Complex.arg z) + Real.sin (Complex.arg z) * I) =
        Real.cos (Complex.arg z) + Real.sin (Complex.arg z) * I from by ring] at this
  -- this : 1 * (cos (arg z) + sin (arg z) * I) = z
  exact this.symm

/-! ## §7. Bonus: De Moivre's Theorem in One Line -/

/-- **De Moivre's theorem** as an immediate consequence of the homomorphism
property: `(circleMap t)^n = circleMap (n·t)` for all `n : ℕ`. -/
theorem circleMap_npow (t : ℝ) (n : ℕ) :
    (circleMap t) ^ n = circleMap (n * t) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← circleMap_add]
    congr 1
    push_cast
    ring

/-- **De Moivre's theorem (integer version)**: `(circleMap t)^n = circleMap (n·t)`
for all `n : ℤ`. The negative-exponent case follows from `circleMap_neg`. -/
theorem circleMap_zpow (t : ℝ) (n : ℤ) :
    (circleMap t) ^ n = circleMap ((n : ℝ) * t) := by
  cases n with
  | ofNat k =>
    show (circleMap t) ^ (k : ℕ) = circleMap ((k : ℝ) * t)
    rw [circleMap_npow]
  | negSucc k =>
    show (circleMap t) ^ (-(k + 1 : ℤ)) = circleMap ((-(k + 1) : ℝ) * t)
    rw [zpow_neg, zpow_natCast, circleMap_npow]
    have : ((-(k + 1 : ℤ) : ℝ) * t) = -((k + 1 : ℕ) * t) := by push_cast; ring
    rw [this, circleMap_neg]

/-! ## §8. Summary -/

/-- The Lie group exponential map `ℝ → S¹` is precisely `circleMap`.

Key properties (proved above):
- `circleMap_add`: homomorphism `(ℝ, +) → (ℂˣ, ·)`
- `norm_circleMap`: image lies in the unit circle
- `continuous_circleMap`: continuous (so this is a Lie group hom)
- `circleMap_eq_one_iff`: kernel is `2π·ℤ` (so S¹ ≅ ℝ/2πℤ)
- `circleMap_surjective_unit_circle`: surjective onto S¹

This is the rigorous form of "Euler's formula identifies S¹ as a 1-parameter
Lie group with Lie algebra `iℝ`." -/
theorem main : ∀ t : ℝ, circleMap t = (Real.cos t : ℂ) + (Real.sin t : ℂ) * I :=
  circleMap_eq_cos_add_sin_I

#check @circleMap_add
#check @norm_circleMap
#check @continuous_circleMap
#check @circleMap_surjective_unit_circle
#check @circleMap_npow

end EulerIdentityOQ01OQ01OQ01

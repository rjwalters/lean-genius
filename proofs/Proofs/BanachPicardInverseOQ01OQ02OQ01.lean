import Mathlib

/-
# Explicit Picard Iteration and Geometric Error Bounds for the Inverse of `id + g`

Open-question extension `oq-01-oq-02-oq-01` of the Banach Fixed Point chain.

The parent result (`oq-01-oq-02`) proves that a `k`-Lipschitz perturbation of the
identity `f x = x + g x` (with `k < 1`, on a complete normed group `E`) is a
homeomorphism whose inverse is `(1-k)⁻¹`-Lipschitz.  That argument is *existential*:
it produces `f⁻¹` from the contraction-mapping theorem but says nothing about how to
**compute** it or how fast an iteration converges.

This file supplies the missing *constructive / quantitative* layer.  To solve
`f x = y`, i.e. `x + g x = y`, rewrite it as the fixed-point equation

  `x = y - g x`,   the **Picard operator**  `T_y x = y - g x`.

`T_y` is a `k`-contraction (same constant as `g`), so its unique fixed point is the
preimage `f⁻¹ y`, reached by the iteration `xₙ₊₁ = y - g xₙ` from *any* starting
point `x₀`.  We package:

* `inverse`            — the inverse `f⁻¹ y`, defined as the fixed point of `T_y`;
* `inverse_solves`     — it really solves `x + g x = y`;
* `inverse_unique`     — it is the *only* solution;
* `tendsto_picard`     — Picard iterates converge to `f⁻¹ y` from any seed `x₀`;
* `apriori_error`      — a priori geometric bound `‖xₙ - f⁻¹ y‖ ≤ ‖x₀ - x₁‖·kⁿ/(1-k)`;
* `aposteriori_error`  — a posteriori bound `‖xₙ - f⁻¹ y‖ ≤ ‖xₙ - xₙ₊₁‖/(1-k)`;
* `linear_rate`        — one-step linear (geometric) contraction of the error;
* `apriori_error_seed_target` — the clean specialisation with seed `x₀ = y`:
                          `‖(T_y)ⁿ y - f⁻¹ y‖ ≤ ‖g y‖·kⁿ/(1-k)`.

The contraction machinery (`ContractingWith.fixedPoint`, its error estimates, and the
convergence theorem) is the Mathlib input; the new content is identifying the fixed
point with the inverse of `id + g` and turning the generic estimates into explicit,
computable error bounds for inverting a Lipschitz perturbation of the identity.

Everything is fully machine-checked: `0` `sorry`s and `0` `axiom`s.  The file is
self-contained — it re-introduces the perturbed map `f = id + g` locally rather than
importing the parent module.
-/

namespace BanachPicardInverseOQ01OQ02OQ01

set_option linter.unusedSectionVars false

open Metric Function Filter Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
variable {k : ℝ≥0} {g : E → E}

/-- The perturbed map `f = id + g` whose inverse we compute. -/
def pmap (g : E → E) : E → E := fun x => x + g x

@[simp] theorem pmap_apply (g : E → E) (x : E) : pmap g x = x + g x := rfl

/-- The **Picard operator** for the target `y`: `T_y x = y - g x`.  A point `x`
solves `f x = y` iff it is a fixed point of `T_y`. -/
def picard (g : E → E) (y : E) : E → E := fun x => y - g x

@[simp] theorem picard_apply (g : E → E) (y x : E) : picard g y x = y - g x := rfl

/-- `T_y` is `k`-Lipschitz: it inherits `g`'s Lipschitz constant. -/
theorem picard_lipschitz (hg : LipschitzWith k g) (y : E) :
    LipschitzWith k (picard g y) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have hd := hg.dist_le_mul a b
  simp only [dist_eq_norm, picard_apply]
  calc ‖(y - g a) - (y - g b)‖ = ‖g a - g b‖ := by
          rw [show (y - g a) - (y - g b) = -(g a - g b) by abel, norm_neg]
    _ ≤ (k : ℝ) * ‖a - b‖ := by simpa [dist_eq_norm] using hd

/-- `T_y` is a `k`-contraction (`k < 1`). -/
theorem picard_contracting (hg : LipschitzWith k g) (hk : k < 1) (y : E) :
    ContractingWith k (picard g y) :=
  ⟨hk, picard_lipschitz hg y⟩

/-- The **inverse** `f⁻¹ y`, defined constructively as the unique fixed point of the
Picard operator `T_y`. -/
noncomputable def inverse (hg : LipschitzWith k g) (hk : k < 1) (y : E) : E :=
  haveI : Nonempty E := ⟨0⟩
  ContractingWith.fixedPoint (picard g y) (picard_contracting hg hk y)

/-- `inverse` is genuinely the fixed point of the Picard operator. -/
theorem isFixedPt_inverse (hg : LipschitzWith k g) (hk : k < 1) (y : E) :
    IsFixedPt (picard g y) (inverse hg hk y) := by
  haveI : Nonempty E := ⟨0⟩
  exact (picard_contracting hg hk y).fixedPoint_isFixedPt

/-- **The inverse solves the equation.**  `f (f⁻¹ y) = y`, i.e.
`inverse y + g (inverse y) = y`. -/
theorem inverse_solves (hg : LipschitzWith k g) (hk : k < 1) (y : E) :
    pmap g (inverse hg hk y) = y := by
  have h := isFixedPt_inverse hg hk y
  rw [IsFixedPt, picard_apply, sub_eq_iff_eq_add] at h
  rw [pmap_apply]
  -- `h : y = inverse + g inverse`
  exact h.symm

/-- **Uniqueness.**  Any solution of `x + g x = y` equals the constructed inverse;
in particular `id + g` is injective and `inverse` is its honest two-sided inverse. -/
theorem inverse_unique (hg : LipschitzWith k g) (hk : k < 1) {y x : E}
    (hx : pmap g x = y) : x = inverse hg hk y := by
  haveI : Nonempty E := ⟨0⟩
  have hfix : IsFixedPt (picard g y) x := by
    rw [IsFixedPt, picard_apply, pmap_apply] at *
    -- from `x + g x = y` deduce `y - g x = x`
    rw [← hx]; abel
  exact (picard_contracting hg hk y).fixedPoint_unique hfix

/-- **Convergence of Picard iteration.**  From *any* seed `x₀`, the iterates
`xₙ₊₁ = y - g xₙ` converge to the inverse `f⁻¹ y`. -/
theorem tendsto_picard (hg : LipschitzWith k g) (hk : k < 1) (y x₀ : E) :
    Tendsto (fun n => (picard g y)^[n] x₀) atTop (𝓝 (inverse hg hk y)) := by
  haveI : Nonempty E := ⟨0⟩
  exact (picard_contracting hg hk y).tendsto_iterate_fixedPoint x₀

/-- **A priori geometric error bound.**  After `n` Picard steps from seed `x₀`,
`‖xₙ - f⁻¹ y‖ ≤ ‖x₀ - x₁‖ · kⁿ / (1 - k)`. -/
theorem apriori_error (hg : LipschitzWith k g) (hk : k < 1) (y x₀ : E) (n : ℕ) :
    dist ((picard g y)^[n] x₀) (inverse hg hk y)
      ≤ dist x₀ (picard g y x₀) * (k : ℝ) ^ n / (1 - k) := by
  haveI : Nonempty E := ⟨0⟩
  exact (picard_contracting hg hk y).apriori_dist_iterate_fixedPoint_le x₀ n

/-- **A posteriori error bound.**  The error is controlled by the last increment:
`‖xₙ - f⁻¹ y‖ ≤ ‖xₙ - xₙ₊₁‖ / (1 - k)`. -/
theorem aposteriori_error (hg : LipschitzWith k g) (hk : k < 1) (y x₀ : E) (n : ℕ) :
    dist ((picard g y)^[n] x₀) (inverse hg hk y)
      ≤ dist ((picard g y)^[n] x₀) ((picard g y)^[n + 1] x₀) / (1 - k) := by
  haveI : Nonempty E := ⟨0⟩
  exact (picard_contracting hg hk y).aposteriori_dist_iterate_fixedPoint_le x₀ n

/-- **Linear (geometric) convergence rate.**  One Picard step shrinks the error by
the factor `k`: `‖T_y x - f⁻¹ y‖ ≤ k · ‖x - f⁻¹ y‖`. -/
theorem linear_rate (hg : LipschitzWith k g) (hk : k < 1) (y x : E) :
    dist (picard g y x) (inverse hg hk y) ≤ (k : ℝ) * dist x (inverse hg hk y) := by
  have hfix := isFixedPt_inverse hg hk y
  calc dist (picard g y x) (inverse hg hk y)
      = dist (picard g y x) (picard g y (inverse hg hk y)) := by rw [hfix.eq]
    _ ≤ (k : ℝ) * dist x (inverse hg hk y) :=
        (picard_lipschitz hg y).dist_le_mul x (inverse hg hk y)

/-- **Clean specialisation with the natural seed `x₀ = y`.**  Since the first
increment is `‖y - T_y y‖ = ‖g y‖`, the a priori bound reads
`‖(T_y)ⁿ y - f⁻¹ y‖ ≤ ‖g y‖ · kⁿ / (1 - k)`. -/
theorem apriori_error_seed_target (hg : LipschitzWith k g) (hk : k < 1) (y : E) (n : ℕ) :
    dist ((picard g y)^[n] y) (inverse hg hk y)
      ≤ ‖g y‖ * (k : ℝ) ^ n / (1 - k) := by
  have h := apriori_error hg hk y y n
  have hseed : dist y (picard g y y) = ‖g y‖ := by
    rw [dist_eq_norm, picard_apply, show y - (y - g y) = g y by abel]
  rwa [hseed] at h

end BanachPicardInverseOQ01OQ02OQ01

import Mathlib

/-
# Lipschitz Perturbation of the Identity is a Homeomorphism

Open-question extension `oq-01-oq-02` of the Banach Fixed Point chain.

Let `E` be a complete normed (additive) group and let `g : E → E` be
`k`-Lipschitz with `k < 1`.  Then the perturbed map

  `f x = x + g x`

is a **homeomorphism of `E` onto itself**, with a quantitative two-sided
Lipschitz control:

  `(1 - k) ‖x - y‖ ≤ ‖f x - f y‖`        (expansion / antilipschitz bound)
  `‖f⁻¹ a - f⁻¹ b‖ ≤ (1 - k)⁻¹ ‖a - b‖`  (the inverse is `(1-k)⁻¹`-Lipschitz)

This is the analytic core of the inverse function theorem: a small
(Lipschitz) perturbation of the identity remains invertible, and one controls
the modulus of continuity of the inverse explicitly.  Surjectivity is the
prototypical application of the Banach contraction principle: solving
`f x = y` is the fixed-point equation `x = y - g x` for the contraction
`x ↦ y - g x`.

Everything below is fully machine-checked with `0` `sorry`s and `0` `axiom`s.
The only nontrivial Mathlib input is the contraction-mapping fixed-point
theorem (`ContractingWith.fixedPoint`); the expansion estimate and the
homeomorphism packaging are proved from the triangle inequality.
-/

namespace BanachPerturbationOQ01OQ02

set_option linter.unusedSectionVars false

open Metric Function
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
variable {k : ℝ≥0} {g : E → E}

/-- The perturbed map `f = id + g`. -/
def pmap (g : E → E) : E → E := fun x => x + g x

@[simp] theorem pmap_apply (g : E → E) (x : E) : pmap g x = x + g x := rfl

/-- **Expansion estimate.**  A `k`-Lipschitz perturbation of the identity
expands distances by at least the factor `1 - k`:
`(1 - k) ‖x - y‖ ≤ ‖f x - f y‖`. -/
theorem norm_sub_perturb_ge (hg : LipschitzWith k g) (x y : E) :
    (1 - (k : ℝ)) * ‖x - y‖ ≤ ‖pmap g x - pmap g y‖ := by
  have hgle : ‖g x - g y‖ ≤ (k : ℝ) * ‖x - y‖ := by
    have := hg.dist_le_mul x y
    simpa [dist_eq_norm] using this
  have hsplit : x - y = (pmap g x - pmap g y) - (g x - g y) := by
    simp only [pmap]; abel
  have htri : ‖x - y‖ ≤ ‖pmap g x - pmap g y‖ + ‖g x - g y‖ := by
    calc ‖x - y‖ = ‖(pmap g x - pmap g y) - (g x - g y)‖ := by rw [hsplit]
      _ ≤ ‖pmap g x - pmap g y‖ + ‖g x - g y‖ := norm_sub_le _ _
  nlinarith [htri, hgle]

/-- **Antilipschitz bound.**  `f = id + g` is `(1-k)⁻¹`-antilipschitz, i.e.
`dist x y ≤ (1-k)⁻¹ · dist (f x) (f y)`. -/
theorem perturb_antilipschitz (hg : LipschitzWith k g) (hk : k < 1) :
    AntilipschitzWith (1 - k)⁻¹ (pmap g) := by
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have hk0 : (0 : ℝ) < 1 - (k : ℝ) := by
    have : (k : ℝ) < 1 := by exact_mod_cast hk
    linarith
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_inv, NNReal.coe_sub hk.le, NNReal.coe_one,
    inv_mul_eq_div, le_div_iff₀ hk0, mul_comm]
  exact norm_sub_perturb_ge hg x y

/-- `f = id + g` is injective. -/
theorem perturb_injective (hg : LipschitzWith k g) (hk : k < 1) :
    Injective (pmap g) :=
  (perturb_antilipschitz hg hk).injective

/-- `f = id + g` is continuous (sum of the identity and the Lipschitz `g`). -/
theorem perturb_continuous (hg : LipschitzWith k g) : Continuous (pmap g) :=
  continuous_id.add hg.continuous

/-- **Surjectivity via Banach's contraction principle.**  For each target `y`,
the map `x ↦ y - g x` is a `k`-contraction; its fixed point `x` satisfies
`x = y - g x`, i.e. `f x = x + g x = y`. -/
theorem perturb_surjective (hg : LipschitzWith k g) (hk : k < 1) :
    Surjective (pmap g) := by
  intro y
  have hTL : LipschitzWith k (fun x => y - g x) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    have hd := hg.dist_le_mul a b
    simp only [dist_eq_norm]
    calc ‖(y - g a) - (y - g b)‖ = ‖g a - g b‖ := by
            rw [show (y - g a) - (y - g b) = -(g a - g b) by abel, norm_neg]
      _ ≤ (k : ℝ) * ‖a - b‖ := by simpa [dist_eq_norm] using hd
  have hContr : ContractingWith k (fun x => y - g x) := ⟨hk, hTL⟩
  haveI : Nonempty E := ⟨0⟩
  set fp := ContractingWith.fixedPoint (fun x => y - g x) hContr with hfpdef
  have hfp : y - g fp = fp := hContr.fixedPoint_isFixedPt
  refine ⟨fp, ?_⟩
  rw [sub_eq_iff_eq_add] at hfp
  rw [pmap_apply]
  exact hfp.symm

/-- `f = id + g` is bijective. -/
theorem perturb_bijective (hg : LipschitzWith k g) (hk : k < 1) :
    Bijective (pmap g) :=
  ⟨perturb_injective hg hk, perturb_surjective hg hk⟩

/-- **Main theorem.**  A `k`-Lipschitz perturbation of the identity (`k < 1`)
on a complete normed group is a homeomorphism of `E` onto itself. -/
noncomputable def perturbHomeo (hg : LipschitzWith k g) (hk : k < 1) : E ≃ₜ E where
  toEquiv := Equiv.ofBijective (pmap g) (perturb_bijective hg hk)
  continuous_toFun := perturb_continuous hg
  continuous_invFun :=
    ((perturb_antilipschitz hg hk).to_rightInverse
      (Equiv.ofBijective (pmap g) (perturb_bijective hg hk)).right_inv).continuous

@[simp] theorem perturbHomeo_apply (hg : LipschitzWith k g) (hk : k < 1) (x : E) :
    perturbHomeo hg hk x = x + g x := rfl

/-- The inverse homeomorphism is `(1-k)⁻¹`-Lipschitz. -/
theorem symm_lipschitz (hg : LipschitzWith k g) (hk : k < 1) :
    LipschitzWith (1 - k)⁻¹ (perturbHomeo hg hk).symm :=
  (perturb_antilipschitz hg hk).to_rightInverse
    (Equiv.ofBijective (pmap g) (perturb_bijective hg hk)).right_inv

/-- **Quantitative inverse bound.**  The inverse of `id + g` satisfies the
sharp Lipschitz estimate `‖f⁻¹ a - f⁻¹ b‖ ≤ (1-k)⁻¹ ‖a - b‖`. -/
theorem symm_norm_sub_le (hg : LipschitzWith k g) (hk : k < 1) (a b : E) :
    ‖(perturbHomeo hg hk).symm a - (perturbHomeo hg hk).symm b‖
      ≤ (1 - (k : ℝ))⁻¹ * ‖a - b‖ := by
  have hk0 : (0 : ℝ) < 1 - (k : ℝ) := by
    have : (k : ℝ) < 1 := by exact_mod_cast hk
    linarith
  have hb := norm_sub_perturb_ge hg
    ((perturbHomeo hg hk).symm a) ((perturbHomeo hg hk).symm b)
  have ha : (perturbHomeo hg hk).symm a + g ((perturbHomeo hg hk).symm a) = a := by
    have := (perturbHomeo hg hk).apply_symm_apply a
    rwa [perturbHomeo_apply] at this
  have hb' : (perturbHomeo hg hk).symm b + g ((perturbHomeo hg hk).symm b) = b := by
    have := (perturbHomeo hg hk).apply_symm_apply b
    rwa [perturbHomeo_apply] at this
  rw [pmap_apply, pmap_apply, ha, hb'] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hk0, mul_comm]
  exact hb

end BanachPerturbationOQ01OQ02

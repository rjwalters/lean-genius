/-
  Lipschitz Perturbation of the Identity is a Homeomorphism.

  Let `E` be a (real) Banach space — a complete normed additive commutative
  group — and let `g : E → E` be a CONTRACTION: `LipschitzWith k g` with
  `k < 1`.  Consider the perturbed-identity map

        f : E → E,    f x = x + g x.

  This file proves that `f` is a HOMEOMORPHISM of `E` onto itself with a
  Lipschitz inverse, and pins down the quantitative constants:

    * (lower bound / antilipschitz)  `(1 − k)·‖x − y‖ ≤ ‖f x − f y‖`, i.e.
      `AntilipschitzWith (1 − k)⁻¹ f`;
    * (injectivity)                  `f` is injective;
    * (surjectivity)                 every `y` has a preimage — obtained as the
      Banach fixed point of the contraction `x ↦ y − g x`;
    * (homeomorphism)                `f` packages into `E ≃ₜ E`;
    * (inverse bound)                `LipschitzWith (1 − k)⁻¹ f⁻¹`, i.e. the
      inverse is Lipschitz with constant `1/(1 − k)`.

  This is the workhorse behind the Banach/Newton form of the inverse function
  theorem: a `C¹` map whose derivative is invertible looks, after composing
  with the inverse derivative, like "identity + contraction", and this lemma
  turns that local picture into a genuine local homeomorphism.

  Relation to the gallery.  The parent entry (`banach-fixed-point-oq-01`)
  packages Mathlib's `ContractingWith` fixed-point API, and the sibling
  (`-oq-01-oq-01`) applies it to Picard–Lindelöf.  This entry is the third
  pillar: it feeds the same fixed-point principle into the *global* inversion
  of identity-plus-contraction.  Mathlib has `ContractingWith.fixedPoint` and
  `AntilipschitzWith`, but does NOT package the perturbation-of-identity
  homeomorphism itself; that assembly is the contribution here.

  Everything is fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open scoped NNReal
open Function

namespace BanachFixedPointOQ01OQ02

variable {E : Type*} [NormedAddCommGroup E]
variable {k : ℝ≥0} {g : E → E}

/-- The perturbed identity `f x = x + g x`. -/
def perturbId (g : E → E) : E → E := fun x => x + g x

/-! ### Lower Lipschitz bound (antilipschitz)

For a `k`-Lipschitz `g` with `k < 1`, the perturbed identity expands distances
by at least the factor `1 − k`:  `‖f x − f y‖ ≥ (1 − k)‖x − y‖`. -/

/-- **Antilipschitz bound.**  `f = id + g` is antilipschitz with constant
`(1 − k)⁻¹`: `dist x y ≤ (1 − k)⁻¹ · dist (f x) (f y)`. -/
theorem antilipschitz (hk : k < 1) (hg : LipschitzWith k g) :
    AntilipschitzWith (1 - k)⁻¹ (perturbId g) := by
  have hkR : (k : ℝ) < 1 := by exact_mod_cast hk
  have hpos : (0 : ℝ) < 1 - (k : ℝ) := by linarith
  apply AntilipschitzWith.of_le_mul_dist
  intro x y
  have hcoe : (((1 - k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ) = (1 - (k : ℝ))⁻¹ := by
    rw [NNReal.coe_inv, NNReal.coe_sub hk.le, NNReal.coe_one]
  rw [hcoe]
  have hgd : ‖g x - g y‖ ≤ (k : ℝ) * ‖x - y‖ := by
    have := hg.dist_le_mul x y
    rwa [dist_eq_norm, dist_eq_norm] at this
  have e1 : dist (perturbId g x) (perturbId g y) = ‖(x - y) + (g x - g y)‖ := by
    simp only [perturbId, dist_eq_norm]
    congr 1
    abel
  have e2 : ‖x - y‖ - ‖g x - g y‖ ≤ ‖(x - y) + (g x - g y)‖ := by
    have h := norm_sub_norm_le (x - y) (-(g x - g y))
    rw [norm_neg, sub_neg_eq_add] at h
    exact h
  have key : (1 - (k : ℝ)) * dist x y ≤ dist (perturbId g x) (perturbId g y) := by
    rw [e1, dist_eq_norm]
    calc (1 - (k : ℝ)) * ‖x - y‖ = ‖x - y‖ - (k : ℝ) * ‖x - y‖ := by ring
      _ ≤ ‖x - y‖ - ‖g x - g y‖ := by linarith
      _ ≤ ‖(x - y) + (g x - g y)‖ := e2
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  linarith [key, mul_comm (dist x y) (1 - (k : ℝ))]

/-- **Injectivity.**  A contraction-perturbed identity is injective. -/
theorem injective (hk : k < 1) (hg : LipschitzWith k g) :
    Function.Injective (perturbId g) :=
  (antilipschitz hk hg).injective

/-- **Continuity.**  `f = id + g` is continuous (indeed Lipschitz). -/
theorem continuous (hg : LipschitzWith k g) : Continuous (perturbId g) :=
  continuous_id.add hg.continuous

/-! ### Surjectivity via the contraction `x ↦ y − g x`

To invert `f` at a target `y` we solve `x + g x = y`, i.e. `x = y − g x`.  The
right-hand side `x ↦ y − g x` is a `k`-Lipschitz self-map of the complete space
`E`, hence a contraction, and its Banach fixed point is exactly the preimage. -/

/-- **Surjectivity.**  On a complete space every point is hit: the preimage of
`y` is the fixed point of the contraction `x ↦ y − g x`. -/
theorem surjective [CompleteSpace E] (hk : k < 1) (hg : LipschitzWith k g) :
    Function.Surjective (perturbId g) := by
  intro y
  haveI : Nonempty E := ⟨0⟩
  have hT : ContractingWith k (fun x => y - g x) := by
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    calc dist (y - g a) (y - g b) = dist (g b) (g a) := by
            rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
      _ = dist (g a) (g b) := dist_comm _ _
      _ ≤ ↑k * dist a b := hg.dist_le_mul a b
  set p := ContractingWith.fixedPoint (fun x => y - g x) hT with hp
  have hfix : y - g p = p := hT.fixedPoint_isFixedPt
  refine ⟨p, ?_⟩
  have hy : y = p + g p := sub_eq_iff_eq_add.mp hfix
  simp only [perturbId]
  exact hy.symm

/-- **Bijectivity.** -/
theorem bijective [CompleteSpace E] (hk : k < 1) (hg : LipschitzWith k g) :
    Function.Bijective (perturbId g) :=
  ⟨injective hk hg, surjective hk hg⟩

/-! ### The homeomorphism -/

/-- **Perturbation of the identity is a homeomorphism.**  For a contraction `g`
(`k < 1`) on a Banach space, `f x = x + g x` is a homeomorphism `E ≃ₜ E`. -/
noncomputable def homeomorph [CompleteSpace E] (hk : k < 1) (hg : LipschitzWith k g) :
    E ≃ₜ E :=
  { toEquiv := Equiv.ofBijective (perturbId g) (bijective hk hg)
    continuous_toFun := continuous hg
    continuous_invFun := by
      have hL : LipschitzWith (1 - k)⁻¹
          (Equiv.ofBijective (perturbId g) (bijective hk hg)).symm :=
        (antilipschitz hk hg).to_rightInverse
          (Equiv.ofBijective (perturbId g) (bijective hk hg)).right_inv
      exact hL.continuous }

/-- The homeomorphism is, as a function, exactly the perturbed identity. -/
@[simp] theorem coe_homeomorph [CompleteSpace E] (hk : k < 1) (hg : LipschitzWith k g) :
    ⇑(homeomorph hk hg) = perturbId g := rfl

/-- **Inverse bound.**  The inverse homeomorphism is Lipschitz with constant
`(1 − k)⁻¹ = 1/(1 − k)`. -/
theorem lipschitzWith_symm [CompleteSpace E] (hk : k < 1) (hg : LipschitzWith k g) :
    LipschitzWith (1 - k)⁻¹ (homeomorph hk hg).symm :=
  (antilipschitz hk hg).to_rightInverse (homeomorph hk hg).apply_symm_apply

end BanachFixedPointOQ01OQ02

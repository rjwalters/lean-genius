import Mathlib
import Proofs.PtolemysTheoremOQ01
import Proofs.PtolemysComplexProofOQ01

/-!
# Discharging the unit-circle converse axiom of Ptolemy's theorem

## What this proves

The parent leaf `ptolemys-theorem-oq-01-oq-01` (`PtolemysTheoremOQ01OQ01.lean`) proves the
converse of Ptolemy's theorem for four points on the unit circle —
"Ptolemy equality ⇔ cyclic (CCW or CW) order" — but seals the angular step behind an
`axiom positive_ratio_implies_cyclic_order`: positive real proportionality of the
opposite-side products forces a counterclockwise or clockwise order of the four points.

This file **discharges that axiom**, proving it as a theorem
(`positive_ratio_implies_cyclic_order_thm`), so the unit-circle converse becomes 0-axiom.
(`IsCCWOrder` is imported from `PtolemysTheoremOQ01`; `IsCWOrder`/`FourDistinct` are restated
locally — see the note below — so the file does not depend on the parent leaf, which currently
has unrelated Mathlib-`v4.26.0` drift in a sanity-`example`.)

## How the proof works

Each unit-circle point is `exp(iθ)`. Anchoring at `z₁ = exp(iθ₁)`, every other point is
`zⱼ = z₁·exp(iφⱼ)` with `φⱼ ∈ (0, 2π)` (`ratio_angle`), so `zⱼ = exp(i(θ₁+φⱼ))`. The
half-angle factorisation `exp(iα) - exp(iβ) = 2i·sin((α-β)/2)·exp(i(α+β)/2)`
(`exp_diff_factor`) turns the complex proportionality hypothesis into the **real** equation

  `t · sin((θ₁-θ₂)/2)·sin((θ₃-θ₄)/2) = sin((θ₂-θ₃)/2)·sin((θ₁-θ₄)/2)`

(`reduce_to_sines`): the four exponential phase factors all combine to
`exp(i(θ₁+θ₂+θ₃+θ₄)/2)` and cancel, as do the two `(2i)²` factors.

Substituting `θⱼ = θ₁+φⱼ`, the half-angles `(θ₁-θ₂)/2 = -φ₂/2` and `(θ₁-θ₄)/2 = -φ₄/2`
have negative sine (their arguments lie in `(-π,0)`). With `t > 0` this forces
`sin((φ₃-φ₄)/2)` and `sin((φ₂-φ₃)/2)` to share a sign, which by the monotonicity of `sin`
on `(-π,π)` means `φ₃` lies strictly between `φ₂` and `φ₄`:

* `φ₂ < φ₃ < φ₄` ⟹ counterclockwise order `IsCCWOrder z₁ z₂ z₃ z₄`;
* `φ₄ < φ₃ < φ₂` ⟹ clockwise order `IsCWOrder z₁ z₂ z₃ z₄` (= `IsCCWOrder z₁ z₄ z₃ z₂`).

No trigonometric ordering axiom is used — only the elementary sign analysis the parent's
axiom comment promised.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open Real

namespace Ptolemy.ConverseDischarge

/-! ## Local restatements of the parent's definitions

`IsCCWOrder` is imported from `PtolemysTheoremOQ01`. The parent leaf `PtolemysTheoremOQ01OQ01`
(where `IsCWOrder`, `FourDistinct` and the `axiom` live) currently fails to elaborate under
Mathlib `v4.26.0` because of unrelated API drift in a numerical sanity-`example`
(`Complex.abs_apply`, `Real.sqrt_eq_iff_sq_eq` were removed). To keep this file robust we restate
those small definitions verbatim here; the discharged statement is identical to the parent's
`axiom positive_ratio_implies_cyclic_order`. -/

/-- Four unit-circle points in clockwise order (the reverse labelling is CCW). Identical to the
parent's `IsCWOrder`. -/
def IsCWOrder (z₁ z₂ z₃ z₄ : ℂ) : Prop := IsCCWOrder z₁ z₄ z₃ z₂

/-- All six pairwise distinctness conditions for four points (identical to the parent's). -/
structure FourDistinct (z₁ z₂ z₃ z₄ : ℂ) : Prop where
  h12 : z₁ ≠ z₂
  h13 : z₁ ≠ z₃
  h14 : z₁ ≠ z₄
  h23 : z₂ ≠ z₃
  h24 : z₂ ≠ z₄
  h34 : z₃ ≠ z₄

/-- For four distinct points, `(z₁-z₂)·(z₃-z₄) ≠ 0`. -/
lemma FourDistinct.denom_ne {z₁ z₂ z₃ z₄ : ℂ} (hd : FourDistinct z₁ z₂ z₃ z₄) :
    (z₁ - z₂) * (z₃ - z₄) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hd.h12) (sub_ne_zero.mpr hd.h34)

/-- For four distinct points, `(z₂-z₃)·(z₁-z₄) ≠ 0`. -/
lemma FourDistinct.numer_ne {z₁ z₂ z₃ z₄ : ℂ} (hd : FourDistinct z₁ z₂ z₃ z₄) :
    (z₂ - z₃) * (z₁ - z₄) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hd.h23) (sub_ne_zero.mpr hd.h14)

/-- Ptolemy equality forces positive proportionality of the opposite-side products (the equality
case of the triangle inequality in the strictly convex space `ℂ`). Wrapper around
`ptolemy_equality_implies_proportional`. -/
lemma ptolemy_eq_implies_pos_prop (z₁ z₂ z₃ z₄ : ℂ) (hd : FourDistinct z₁ z₂ z₃ z₄)
    (hptolemy : ‖z₁ - z₃‖ * ‖z₂ - z₄‖ =
                ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) :
    ∃ t : ℝ, 0 < t ∧ t • ((z₁ - z₂) * (z₃ - z₄)) = (z₂ - z₃) * (z₁ - z₄) :=
  ptolemy_equality_implies_proportional z₁ z₂ z₃ z₄ hptolemy hd.denom_ne hd.numer_ne

/-! ## Trig helpers (re-derived; the originals are `private` in `PtolemysTheoremOQ01`) -/

/-- `exp(iα) - exp(iβ) = 2i·sin((α-β)/2)·exp(i(α+β)/2)`. -/
private lemma exp_diff_factor (α β : ℝ) :
    Complex.exp (↑α * Complex.I) - Complex.exp (↑β * Complex.I) =
    2 * Complex.I * ↑(Real.sin ((α - β) / 2)) *
    Complex.exp (↑((α + β) / 2) * Complex.I) := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re]
    have hrhs : (2 * Complex.I * ↑(Real.sin ((α - β) / 2)) *
        Complex.exp (↑((α + β) / 2) * Complex.I)).re =
        -2 * Real.sin ((α - β) / 2) * Real.sin ((α + β) / 2) := by
      have h1 : (2 * Complex.I * ↑(Real.sin ((α - β) / 2))).re = 0 := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]; ring
      have h2 : (2 * Complex.I * ↑(Real.sin ((α - β) / 2))).im =
          2 * Real.sin ((α - β) / 2) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]; ring
      rw [Complex.mul_re, h1, h2, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]; ring
    rw [hrhs]
    have hca : Real.cos α = Real.cos ((α + β) / 2 + (α - β) / 2) := by congr 1; ring
    have hcb : Real.cos β = Real.cos ((α + β) / 2 - (α - β) / 2) := by congr 1; ring
    rw [hca, hcb, Real.cos_add, Real.cos_sub]; ring
  · rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_im]
    have hrhs : (2 * Complex.I * ↑(Real.sin ((α - β) / 2)) *
        Complex.exp (↑((α + β) / 2) * Complex.I)).im =
        2 * Real.sin ((α - β) / 2) * Real.cos ((α + β) / 2) := by
      have h1 : (2 * Complex.I * ↑(Real.sin ((α - β) / 2))).re = 0 := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]; ring
      have h2 : (2 * Complex.I * ↑(Real.sin ((α - β) / 2))).im =
          2 * Real.sin ((α - β) / 2) := by
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
              Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]; ring
      rw [Complex.mul_im, h1, h2, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]; ring
    rw [hrhs]
    have hsa : Real.sin α = Real.sin ((α + β) / 2 + (α - β) / 2) := by congr 1; ring
    have hsb : Real.sin β = Real.sin ((α + β) / 2 - (α - β) / 2) := by congr 1; ring
    rw [hsa, hsb, Real.sin_add, Real.sin_sub]; ring

/-- `sin` is negative on `(-π, 0)`. -/
private lemma sin_neg_aux {x : ℝ} (hx : x < 0) (hx' : -Real.pi < x) : Real.sin x < 0 := by
  have hpos : 0 < -x := by linarith
  have hlt : -x < Real.pi := by linarith
  have := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  rwa [Real.sin_neg, neg_pos] at this

/-- For `x ∈ (-2π, 2π)`, `sin(x/2) > 0 ↔ x > 0`. -/
private lemma half_sin_pos_iff {x : ℝ} (h1 : -(2 * Real.pi) < x) (h2 : x < 2 * Real.pi) :
    0 < Real.sin (x / 2) ↔ 0 < x := by
  constructor
  · intro hs
    by_contra hle
    push_neg at hle
    rcases lt_or_eq_of_le hle with h | h
    · have : Real.sin (x / 2) < 0 := sin_neg_aux (by linarith) (by linarith)
      linarith
    · rw [h] at hs; simp at hs
  · intro hx
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)

/-- For `x ∈ (-2π, 2π)`, `sin(x/2) < 0 ↔ x < 0`. -/
private lemma half_sin_neg_iff {x : ℝ} (h1 : -(2 * Real.pi) < x) (h2 : x < 2 * Real.pi) :
    Real.sin (x / 2) < 0 ↔ x < 0 := by
  constructor
  · intro hs
    by_contra hle
    push_neg at hle
    rcases lt_or_eq_of_le hle with h | h
    · have : 0 < Real.sin (x / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
      linarith
    · rw [← h] at hs; simp at hs
  · intro hx
    exact sin_neg_aux (by linarith) (by linarith)

/-! ## Reducing the complex proportionality to a real sine equation -/

/-- The half-angle factorisation collapses the complex proportionality
`t·(z₁-z₂)(z₃-z₄) = (z₂-z₃)(z₁-z₄)` (with `zⱼ = exp(iθⱼ)`) to a real equation in the
half-angle sines. -/
private lemma reduce_to_sines (θ₁ θ₂ θ₃ θ₄ t : ℝ)
    (heq : (↑t : ℂ) * ((Complex.exp (↑θ₁ * Complex.I) - Complex.exp (↑θ₂ * Complex.I)) *
                       (Complex.exp (↑θ₃ * Complex.I) - Complex.exp (↑θ₄ * Complex.I)))
         = (Complex.exp (↑θ₂ * Complex.I) - Complex.exp (↑θ₃ * Complex.I)) *
           (Complex.exp (↑θ₁ * Complex.I) - Complex.exp (↑θ₄ * Complex.I))) :
    t * (Real.sin ((θ₁ - θ₂) / 2) * Real.sin ((θ₃ - θ₄) / 2))
      = Real.sin ((θ₂ - θ₃) / 2) * Real.sin ((θ₁ - θ₄) / 2) := by
  -- abbreviations for the four exponential phase factors
  set E₁₂ := Complex.exp (↑((θ₁ + θ₂) / 2) * Complex.I)
  set E₃₄ := Complex.exp (↑((θ₃ + θ₄) / 2) * Complex.I)
  set E₂₃ := Complex.exp (↑((θ₂ + θ₃) / 2) * Complex.I)
  set E₁₄ := Complex.exp (↑((θ₁ + θ₄) / 2) * Complex.I)
  have hphase : E₁₂ * E₃₄ = E₂₃ * E₁₄ := by
    simp only [E₁₂, E₃₄, E₂₃, E₁₄, ← Complex.exp_add]; congr 1; push_cast; ring
  have hEne : E₂₃ * E₁₄ ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
  rw [exp_diff_factor θ₁ θ₂, exp_diff_factor θ₃ θ₄, exp_diff_factor θ₂ θ₃,
      exp_diff_factor θ₁ θ₄] at heq
  -- rewrite both products into  scalar · (-4) · (E₂₃·E₁₄)
  have hL : (↑t : ℂ) * ((2 * Complex.I * ↑(Real.sin ((θ₁ - θ₂) / 2)) * E₁₂) *
              (2 * Complex.I * ↑(Real.sin ((θ₃ - θ₄) / 2)) * E₃₄))
          = (↑t * ↑(Real.sin ((θ₁ - θ₂) / 2)) * ↑(Real.sin ((θ₃ - θ₄) / 2))) * (-4)
            * (E₂₃ * E₁₄) := by
    have e : (↑t : ℂ) * ((2 * Complex.I * ↑(Real.sin ((θ₁ - θ₂) / 2)) * E₁₂) *
              (2 * Complex.I * ↑(Real.sin ((θ₃ - θ₄) / 2)) * E₃₄))
           = (↑t * ↑(Real.sin ((θ₁ - θ₂) / 2)) * ↑(Real.sin ((θ₃ - θ₄) / 2)))
             * (4 * Complex.I ^ 2) * (E₁₂ * E₃₄) := by ring
    rw [e, Complex.I_sq, hphase]; ring
  have hR : (2 * Complex.I * ↑(Real.sin ((θ₂ - θ₃) / 2)) * E₂₃) *
              (2 * Complex.I * ↑(Real.sin ((θ₁ - θ₄) / 2)) * E₁₄)
          = (↑(Real.sin ((θ₂ - θ₃) / 2)) * ↑(Real.sin ((θ₁ - θ₄) / 2))) * (-4)
            * (E₂₃ * E₁₄) := by
    have e : (2 * Complex.I * ↑(Real.sin ((θ₂ - θ₃) / 2)) * E₂₃) *
              (2 * Complex.I * ↑(Real.sin ((θ₁ - θ₄) / 2)) * E₁₄)
           = (↑(Real.sin ((θ₂ - θ₃) / 2)) * ↑(Real.sin ((θ₁ - θ₄) / 2)))
             * (4 * Complex.I ^ 2) * (E₂₃ * E₁₄) := by ring
    rw [e, Complex.I_sq]; ring
  rw [hL, hR] at heq
  -- cancel the common nonzero factor (-4)·(E₂₃·E₁₄)
  have hcancel : (↑t * ↑(Real.sin ((θ₁ - θ₂) / 2)) * ↑(Real.sin ((θ₃ - θ₄) / 2)) : ℂ)
               = ↑(Real.sin ((θ₂ - θ₃) / 2)) * ↑(Real.sin ((θ₁ - θ₄) / 2)) := by
    have hfac : ((-4 : ℂ) * (E₂₃ * E₁₄)) ≠ 0 := mul_ne_zero (by norm_num) hEne
    have hF : (↑t * ↑(Real.sin ((θ₁ - θ₂) / 2)) * ↑(Real.sin ((θ₃ - θ₄) / 2)) : ℂ)
                * ((-4) * (E₂₃ * E₁₄))
            = (↑(Real.sin ((θ₂ - θ₃) / 2)) * ↑(Real.sin ((θ₁ - θ₄) / 2)))
                * ((-4) * (E₂₃ * E₁₄)) := by linear_combination heq
    exact mul_right_cancel₀ hfac hF
  -- descend to ℝ
  have : ((t * (Real.sin ((θ₁ - θ₂) / 2) * Real.sin ((θ₃ - θ₄) / 2)) : ℝ) : ℂ)
       = ((Real.sin ((θ₂ - θ₃) / 2) * Real.sin ((θ₁ - θ₄) / 2) : ℝ) : ℂ) := by
    push_cast; push_cast at hcancel; linear_combination hcancel
  exact_mod_cast this

/-! ## Angle extraction -/

/-- A unit complex number `≠ 1` equals `exp(iφ)` for a unique `φ ∈ (0, 2π)`. -/
private lemma unit_to_angle (w : ℂ) (hw : ‖w‖ = 1) (hw1 : w ≠ 1) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 2 * Real.pi ∧ w = Complex.exp (↑φ * Complex.I) := by
  have key : w = Complex.exp (↑(Complex.arg w) * Complex.I) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I w]
    rw [hw]; simp
  have hargne : Complex.arg w ≠ 0 := by
    intro h0; apply hw1; rw [key, h0]; simp
  have hub := Complex.arg_le_pi w
  have hlb := Complex.neg_pi_lt_arg w
  rcases lt_or_gt_of_ne hargne with hneg | hpos
  · refine ⟨Complex.arg w + 2 * Real.pi, by linarith, by linarith, ?_⟩
    rw [show (↑(Complex.arg w + 2 * Real.pi) * Complex.I)
          = ↑(Complex.arg w) * Complex.I + (2 * ↑Real.pi * Complex.I) from by push_cast; ring,
        Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
    exact key
  · exact ⟨Complex.arg w, hpos, by linarith [Real.pi_pos], key⟩

/-- Anchored angle: a unit point `z ≠ z₁` (both on the unit circle) is `z₁·exp(iφ)` with
`φ ∈ (0, 2π)`. -/
private lemma ratio_angle (z₁ z : ℂ) (h₁ : ‖z₁‖ = 1) (hz : ‖z‖ = 1) (hne : z ≠ z₁) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 2 * Real.pi ∧ z = z₁ * Complex.exp (↑φ * Complex.I) := by
  have hz1ne : z₁ ≠ 0 := by intro h; rw [h, norm_zero] at h₁; norm_num at h₁
  have hwabs : ‖z / z₁‖ = 1 := by rw [norm_div, h₁, hz]; norm_num
  have hwne1 : z / z₁ ≠ 1 := by
    intro h
    apply hne
    field_simp [hz1ne] at h
    exact h
  obtain ⟨φ, hpos, hlt, hwφ⟩ := unit_to_angle (z / z₁) hwabs hwne1
  refine ⟨φ, hpos, hlt, ?_⟩
  rw [← hwφ]; field_simp

/-! ## The main theorem: the parent's axiom, proved -/

/-- **The discharged axiom.** For four distinct unit-circle points, positive real
proportionality of the opposite-side products `t·(z₁-z₂)(z₃-z₄) = (z₂-z₃)(z₁-z₄)` (`t > 0`)
forces counterclockwise or clockwise cyclic order. This is exactly the statement the parent
leaf assumed as `axiom positive_ratio_implies_cyclic_order`; here it is a theorem. -/
theorem positive_ratio_implies_cyclic_order_thm (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hd : FourDistinct z₁ z₂ z₃ z₄)
    (t : ℝ) (ht : 0 < t)
    (heq : t • ((z₁ - z₂) * (z₃ - z₄)) = (z₂ - z₃) * (z₁ - z₄)) :
    IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCWOrder z₁ z₂ z₃ z₄ := by
  -- anchor angle for z₁
  obtain ⟨θ₁, hz1⟩ : ∃ θ₁ : ℝ, z₁ = Complex.exp (↑θ₁ * Complex.I) := by
    refine ⟨Complex.arg z₁, ?_⟩
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z₁]
    rw [h₁]; simp
  -- relative angles for z₂, z₃, z₄
  obtain ⟨φ₂, hφ2p, hφ2l, hz2⟩ := ratio_angle z₁ z₂ h₁ h₂ hd.h12.symm
  obtain ⟨φ₃, hφ3p, hφ3l, hz3⟩ := ratio_angle z₁ z₃ h₁ h₃ hd.h13.symm
  obtain ⟨φ₄, hφ4p, hφ4l, hz4⟩ := ratio_angle z₁ z₄ h₁ h₄ hd.h14.symm
  -- absolute angles θ₁+φⱼ
  have ez2 : z₂ = Complex.exp (↑(θ₁ + φ₂) * Complex.I) := by
    rw [hz2, hz1, ← Complex.exp_add]; congr 1; push_cast; ring
  have ez3 : z₃ = Complex.exp (↑(θ₁ + φ₃) * Complex.I) := by
    rw [hz3, hz1, ← Complex.exp_add]; congr 1; push_cast; ring
  have ez4 : z₄ = Complex.exp (↑(θ₁ + φ₄) * Complex.I) := by
    rw [hz4, hz1, ← Complex.exp_add]; congr 1; push_cast; ring
  -- distinctness of relative angles (from distinctness of points)
  have hφ23 : φ₂ ≠ φ₃ := by
    intro h; apply hd.h23; rw [ez2, ez3, h]
  have hφ34 : φ₃ ≠ φ₄ := by
    intro h; apply hd.h34; rw [ez3, ez4, h]
  -- reduce the complex hypothesis to the real sine equation
  have hsmul : (↑t : ℂ) * ((z₁ - z₂) * (z₃ - z₄)) = (z₂ - z₃) * (z₁ - z₄) := by
    rw [← Complex.real_smul]; exact heq
  rw [hz1, ez2, ez3, ez4] at hsmul
  have hsin := reduce_to_sines θ₁ (θ₁ + φ₂) (θ₁ + φ₃) (θ₁ + φ₄) t hsmul
  -- simplify the half-angle arguments to ±φ/2 and φ-differences
  have a12 : (θ₁ - (θ₁ + φ₂)) / 2 = -(φ₂ / 2) := by ring
  have a34 : ((θ₁ + φ₃) - (θ₁ + φ₄)) / 2 = (φ₃ - φ₄) / 2 := by ring
  have a23 : ((θ₁ + φ₂) - (θ₁ + φ₃)) / 2 = (φ₂ - φ₃) / 2 := by ring
  have a14 : (θ₁ - (θ₁ + φ₄)) / 2 = -(φ₄ / 2) := by ring
  rw [a12, a34, a23, a14, Real.sin_neg, Real.sin_neg] at hsin
  -- A = sin(φ₂/2) > 0, D = sin(φ₄/2) > 0
  have hA : 0 < Real.sin (φ₂ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hD : 0 < Real.sin (φ₄ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- the real equation now reads  t·A·C = B·D  with the negatives folded in:
  --   t·(-A)·C = B·(-D)  ⟹  t·A·C = B·D
  set B := Real.sin ((φ₂ - φ₃) / 2) with hBdef
  set C := Real.sin ((φ₃ - φ₄) / 2) with hCdef
  have hABCD : t * (Real.sin (φ₂ / 2) * C) = B * Real.sin (φ₄ / 2) := by linarith [hsin]
  -- C ≠ 0 and B ≠ 0 (distinct angles)
  have hCne : C ≠ 0 := by
    rw [hCdef]; intro h
    rcases (Real.sin_eq_zero_iff_of_lt_of_lt (x := (φ₃ - φ₄) / 2)
        (by linarith) (by linarith)).mp h with h0
    apply hφ34; linarith
  -- sign transfer: sign C = sign B
  rcases lt_trichotomy C 0 with hCneg | hC0 | hCpos
  · -- C < 0  ⟹  B < 0  ⟹  φ₃ < φ₄ and φ₂ < φ₃  ⟹ CCW
    have hBneg : B < 0 := by
      by_contra hB
      push_neg at hB
      have : 0 ≤ B * Real.sin (φ₄ / 2) := mul_nonneg hB hD.le
      have hlt : t * (Real.sin (φ₂ / 2) * C) < 0 :=
        mul_neg_of_pos_of_neg ht (mul_neg_of_pos_of_neg hA hCneg)
      linarith [hABCD]
    have hφ34lt : φ₃ < φ₄ := by
      have := (half_sin_neg_iff (x := φ₃ - φ₄) (by linarith) (by linarith)).mp hCneg
      linarith
    have hφ23lt : φ₂ < φ₃ := by
      have := (half_sin_neg_iff (x := φ₂ - φ₃) (by linarith) (by linarith)).mp hBneg
      linarith
    left
    exact ⟨θ₁, θ₁ + φ₂, θ₁ + φ₃, θ₁ + φ₄, by linarith, by linarith, by linarith, by linarith,
      hz1, ez2, ez3, ez4⟩
  · exact absurd hC0 hCne
  · -- C > 0  ⟹  B > 0  ⟹  φ₃ > φ₄ and φ₂ > φ₃  ⟹ CW
    have hBpos : 0 < B := by
      by_contra hB
      push_neg at hB
      have hle : B * Real.sin (φ₄ / 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hB hD.le
      have hgt : 0 < t * (Real.sin (φ₂ / 2) * C) :=
        mul_pos ht (mul_pos hA hCpos)
      linarith [hABCD]
    have hφ34gt : φ₄ < φ₃ := by
      have := (half_sin_pos_iff (x := φ₃ - φ₄) (by linarith) (by linarith)).mp hCpos
      linarith
    have hφ23gt : φ₃ < φ₂ := by
      have := (half_sin_pos_iff (x := φ₂ - φ₃) (by linarith) (by linarith)).mp hBpos
      linarith
    right
    -- IsCWOrder z₁ z₂ z₃ z₄ = IsCCWOrder z₁ z₄ z₃ z₂
    exact ⟨θ₁, θ₁ + φ₄, θ₁ + φ₃, θ₁ + φ₂, by linarith, by linarith, by linarith, by linarith,
      hz1, ez4, ez3, ez2⟩

/-- **Corollary — the unit-circle converse, now axiom-free.** Combining the discharged step
with the proportionality extraction reproduces the parent's
`ptolemy_equality_implies_ccw_or_cw` without the `positive_ratio_implies_cyclic_order` axiom. -/
theorem ptolemy_equality_implies_ccw_or_cw_axiomfree (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hd : FourDistinct z₁ z₂ z₃ z₄)
    (hptolemy : ‖z₁ - z₃‖ * ‖z₂ - z₄‖ =
                ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) :
    IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCWOrder z₁ z₂ z₃ z₄ := by
  obtain ⟨t, ht_pos, ht_eq⟩ := ptolemy_eq_implies_pos_prop z₁ z₂ z₃ z₄ hd hptolemy
  exact positive_ratio_implies_cyclic_order_thm z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hd t ht_pos ht_eq

#check @positive_ratio_implies_cyclic_order_thm
#check @ptolemy_equality_implies_ccw_or_cw_axiomfree

end Ptolemy.ConverseDischarge

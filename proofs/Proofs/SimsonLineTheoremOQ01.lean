import Proofs.SimsonLineTheorem

/-
# Simson's Line Theorem — the biconditional (simson-line-theorem-oq-01)

The base development `Proofs/SimsonLineTheorem.lean` proves the **forward**
direction of Simson's theorem: if `P` lies on the circumcircle of `ABC`
(normalised to the unit circle), then the three feet of the perpendiculars from
`P` onto the side-lines are collinear (`SimsonLineTheorem.simson_key`,
`simson_collinear`).

This file closes the **open question**: the genuinely new *converse* direction,
giving the full biconditional

  feet collinear  ⟺  `P` lies on the circumcircle.

## The new ingredient

`simson_key` only computes the collinearity equation *under the hypothesis*
`Complex.normSq p = 1`. The converse needs the same algebra carried out for an
**arbitrary** point `p` (no unit-circle assumption on `p`). Doing so yields the
sharp identity (`simson_defect`)

  `(F_BC − F_AB)·conj(F_CA − F_AB) − conj(F_BC − F_AB)·(F_CA − F_AB)`
    `= (a − c)(c − b)(a − b) / (4 a b c) · (1 − p · conj p)`,

where the left-hand side is the *collinearity defect* of the pedal feet (it
vanishes exactly when the three feet are collinear). For a non-degenerate
triangle the leading coefficient is nonzero, so the defect vanishes **iff**
`p · conj p = 1`, i.e. `Complex.normSq p = 1` — the circumcircle. The forward
direction (`simson_forward`) is then the trivial `mpr` of the biconditional.

This development is **axiom-free and sorry-free**.
-/

namespace SimsonLineTheoremOQ01

open Complex ComplexConjugate SimsonLineTheorem

/-- A point on the unit circle is nonzero. -/
private lemma ne_zero_of_normSq_one {z : ℂ} (h : Complex.normSq z = 1) : z ≠ 0 := by
  rintro rfl; simp at h

/-- On the unit circle, `conj z = z⁻¹`. -/
private lemma conj_eq_inv {z : ℂ} (h : Complex.normSq z = 1) : conj z = z⁻¹ := by
  have h0 : z ≠ 0 := ne_zero_of_normSq_one h
  have hzz : z * conj z = 1 := by rw [Complex.mul_conj, h]; norm_num
  rw [inv_eq_one_div, eq_div_iff h0]
  linear_combination hzz

/-- If `conj z = z` then `z.im = 0`. -/
private lemma im_eq_zero_of_conj_eq {z : ℂ} (h : conj z = z) : z.im = 0 := by
  have h1 : (conj z).im = z.im := by rw [h]
  rw [Complex.conj_im] at h1
  linarith

/-- If `z.im = 0` then `conj z = z`. -/
private lemma conj_eq_of_im_eq_zero {z : ℂ} (h : z.im = 0) : conj z = z := by
  apply Complex.ext
  · simp [Complex.conj_re]
  · simp [Complex.conj_im, h]

/-- The complex collinearity criterion for the three pedal feet of `p`
(`F_AB = foot a b p`, `F_BC = foot b c p`, `F_CA = foot c a p`): the cross
product `(F_BC − F_AB)·conj(F_CA − F_AB)` equals its own conjugate, i.e. is real.
This is exactly the conclusion of `SimsonLineTheorem.simson_key`. -/
def FeetCollinear (a b c p : ℂ) : Prop :=
  (foot b c p - foot a b p) * conj (foot c a p - foot a b p)
    = conj (foot b c p - foot a b p) * (foot c a p - foot a b p)

/-- **The Simson collinearity-defect identity (for an arbitrary point `p`).**
With the circumcircle normalised to the unit circle (`a, b, c` on it, *but `p`
free*), the collinearity defect of the three pedal feet collapses to a single
factored form proportional to `1 − p · conj p`. This is the off-circle
generalisation of `SimsonLineTheorem.simson_key` and the crux of the converse. -/
theorem simson_defect (a b c p : ℂ)
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1) (hc : Complex.normSq c = 1) :
    (foot b c p - foot a b p) * conj (foot c a p - foot a b p)
      - conj (foot b c p - foot a b p) * (foot c a p - foot a b p)
      = (a - c) * (c - b) * (a - b) / (4 * a * b * c) * (1 - p * conj p) := by
  rw [foot_diff, foot_diff']
  simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]
  rw [conj_eq_inv ha, conj_eq_inv hb, conj_eq_inv hc]
  have ha0 := ne_zero_of_normSq_one ha
  have hb0 := ne_zero_of_normSq_one hb
  have hc0 := ne_zero_of_normSq_one hc
  field_simp
  ring

/-- **Simson's line theorem (biconditional).** With the circumcircle of triangle
`ABC` placed as the unit circle, the three pedal feet of `P` are collinear **iff**
`P` lies on that circle (`Complex.normSq p = 1`). The forward direction is
`SimsonLineTheorem.simson_key`; the converse is the new content here. -/
theorem feet_collinear_iff (a b c p : ℂ)
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1) (hc : Complex.normSq c = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    FeetCollinear a b c p ↔ Complex.normSq p = 1 := by
  have ha0 := ne_zero_of_normSq_one ha
  have hb0 := ne_zero_of_normSq_one hb
  have hc0 := ne_zero_of_normSq_one hc
  have hdef := simson_defect a b c p ha hb hc
  have hK : (a - c) * (c - b) * (a - b) / (4 * a * b * c) ≠ 0 := by
    apply div_ne_zero
    · exact mul_ne_zero
        (mul_ne_zero (sub_ne_zero.mpr hca.symm) (sub_ne_zero.mpr hbc.symm))
        (sub_ne_zero.mpr hab)
    · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha0) hb0) hc0
  unfold FeetCollinear
  rw [← sub_eq_zero, hdef, mul_eq_zero]
  constructor
  · rintro (hK0 | hp)
    · exact absurd hK0 hK
    · have hpc : (Complex.normSq p : ℂ) = 1 := by
        rw [← Complex.mul_conj]; linear_combination -hp
      exact_mod_cast hpc
  · intro h
    right
    have hpc : p * conj p = 1 := by rw [Complex.mul_conj, h]; norm_num
    linear_combination -hpc

/-- The collinearity criterion is equivalent to the vanishing of the signed area
`((F_BC − F_AB)·conj(F_CA − F_AB)).im` of the pedal triangle — the form used in
`SimsonLineTheorem.simson_collinear`. -/
theorem feet_collinear_iff_signed_area (a b c p : ℂ) :
    FeetCollinear a b c p
      ↔ ((foot b c p - foot a b p) * conj (foot c a p - foot a b p)).im = 0 := by
  unfold FeetCollinear
  have hconj : conj ((foot b c p - foot a b p) * conj (foot c a p - foot a b p))
      = conj (foot b c p - foot a b p) * (foot c a p - foot a b p) := by
    rw [map_mul, Complex.conj_conj]
  constructor
  · intro h
    exact im_eq_zero_of_conj_eq (hconj.trans h.symm)
  · intro h
    exact (conj_eq_of_im_eq_zero h).symm.trans hconj

/-- **Forward direction (recovered).** If `P` lies on the circumcircle, the three
pedal feet are collinear — the statement of `SimsonLineTheorem.simson_key`, here
obtained as the easy `mpr` half of the biconditional. -/
theorem simson_forward (a b c p : ℂ)
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1) (hc : Complex.normSq c = 1)
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) (hp : Complex.normSq p = 1) :
    FeetCollinear a b c p :=
  (feet_collinear_iff a b c p ha hb hc hab hbc hca).mpr hp

end SimsonLineTheoremOQ01

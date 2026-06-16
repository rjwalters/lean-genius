import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Simson's line theorem (simson-line-theorem-oq-01)

Let `A, B, C` be three points of a circle and `P` a fourth point on the **same** circle.
Drop the perpendicular from `P` onto each of the three side-lines `AB`, `BC`, `CA`, obtaining
the three feet `F_AB`, `F_BC`, `F_CA`. **Simson's theorem** states that these three feet are
**collinear** (the line they span is the *Simson line* of `P`).

We model the points as complex numbers and normalise the circumcircle to the **unit circle**,
encoded by `Complex.normSq A = 1` (i.e. `|A|² = 1`), and likewise for `B, C, P`. Any circle is
carried to the unit circle by an affine map of `ℂ`, which preserves both perpendicularity and
collinearity, so this is no loss of generality.

The engine of the proof is the closed form for the foot of a perpendicular onto a chord of the
unit circle:

    foot u v p = (u + v + p - u * v * conj p) / 2.                       (`foot`)

For `u, v` on the unit circle this is exactly the orthogonal projection of `p` onto the line
`u v`: the segment `P → foot` is perpendicular to the chord (`foot_perp`) and the foot lies on
the chord line (`foot_on_chord`). Its decisive feature is the **difference identity**

    foot b c p - foot a b p = (c - a) * (1 - b * conj p) / 2,            (`foot_diff`)

a pure `ring` fact, with the symmetric companion (`foot_diff'`). Writing
`w = (F_BC - F_AB) * conj (F_CA - F_AB)`, collinearity of the three feet is the classical
complex criterion `w ∈ ℝ`, i.e. `w = conj w` (`simson_key`), equivalently the vanishing of the
signed-area cross product `w.im = 0` (`simson_collinear`). Substituting `conj z = z⁻¹` (valid on
the unit circle) turns `simson_key` into a rational-function identity closed by `field_simp; ring`.

The proof is fully machine-checked: no axioms, no `sorry`. Not a named Mathlib result.
-/

namespace SimsonLineTheorem

open Complex ComplexConjugate

/-- Foot of the perpendicular dropped from `p` onto the chord through `u` and `v` of the unit
circle, in closed form. For `u, v` on the unit circle this is the orthogonal projection of `p`
onto the line `u v` (see `foot_perp` and `foot_on_chord`). -/
noncomputable def foot (u v p : ℂ) : ℂ := (u + v + p - u * v * conj p) / 2

/-- A point on the unit circle is nonzero. -/
private lemma ne_zero_of_normSq_one {z : ℂ} (h : Complex.normSq z = 1) : z ≠ 0 := by
  rintro rfl; simp at h

/-- On the unit circle, `conj z = z⁻¹`. -/
private lemma conj_eq_inv {z : ℂ} (h : Complex.normSq z = 1) : conj z = z⁻¹ := by
  have h0 : z ≠ 0 := ne_zero_of_normSq_one h
  have hzz : z * conj z = 1 := by rw [Complex.mul_conj, h]; norm_num
  rw [inv_eq_one_div, eq_div_iff h0]
  linear_combination hzz

/-- If `conj z = z` then `z` is real, so `z.im = 0`. -/
private lemma im_eq_zero_of_conj_eq {z : ℂ} (h : conj z = z) : z.im = 0 := by
  have h1 : (conj z).im = z.im := by rw [h]
  rw [Complex.conj_im] at h1
  linarith

/-- If `conj z = -z` then `z` is purely imaginary, so `z.re = 0`. -/
private lemma re_eq_zero_of_conj_eq_neg {z : ℂ} (h : conj z = -z) : z.re = 0 := by
  have h1 : (conj z).re = (-z).re := by rw [h]
  rw [Complex.conj_re, Complex.neg_re] at h1
  linarith

/-- **Difference identity** (pure `ring`). The vector between the `BC`-foot and the `AB`-foot
of `p` factors through the chord direction `c - a`. -/
theorem foot_diff (a b c p : ℂ) :
    foot b c p - foot a b p = (c - a) * (1 - b * conj p) / 2 := by
  simp only [foot]; ring

/-- Companion difference identity for the `CA`-foot and the `AB`-foot. -/
theorem foot_diff' (a b c p : ℂ) :
    foot c a p - foot a b p = (c - b) * (1 - a * conj p) / 2 := by
  simp only [foot]; ring

/-- The segment `P → foot u v p` is **perpendicular** to the chord `u v`: the real part of
`(p - foot u v p) * conj (v - u)` vanishes. Needs only `u, v` on the unit circle (any `p`).
Together with `foot_on_chord` this certifies that `foot u v p` is the orthogonal projection. -/
theorem foot_perp {u v p : ℂ} (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1) :
    ((p - foot u v p) * conj (v - u)).re = 0 := by
  apply re_eq_zero_of_conj_eq_neg
  have hu0 := ne_zero_of_normSq_one hu
  have hv0 := ne_zero_of_normSq_one hv
  simp only [foot, map_mul, map_sub, map_add, map_div₀, map_one, map_ofNat, Complex.conj_conj]
  rw [conj_eq_inv hu, conj_eq_inv hv]
  field_simp
  ring

/-- The foot **lies on** the chord line `u v`: `foot u v p - u` is a real multiple of the
direction `v - u`, encoded as the vanishing imaginary part of `(foot u v p - u) * conj (v - u)`.
Needs only `u, v` on the unit circle (any `p`). -/
theorem foot_on_chord {u v p : ℂ} (hu : Complex.normSq u = 1) (hv : Complex.normSq v = 1) :
    ((foot u v p - u) * conj (v - u)).im = 0 := by
  apply im_eq_zero_of_conj_eq
  have hu0 := ne_zero_of_normSq_one hu
  have hv0 := ne_zero_of_normSq_one hv
  simp only [foot, map_mul, map_sub, map_add, map_div₀, map_one, map_ofNat, Complex.conj_conj]
  rw [conj_eq_inv hu, conj_eq_inv hv]
  field_simp
  ring

/-- **Simson's theorem (collinearity equation).** For `A, B, C, P` on the unit circle, the three
feet of the perpendiculars from `P` to the side-lines `AB`, `BC`, `CA` satisfy the complex
collinearity criterion: `(F_BC - F_AB) * conj (F_CA - F_AB)` equals its own conjugate, i.e. it is
real. This says precisely that the three feet lie on a common line — the *Simson line* of `P`. -/
theorem simson_key {a b c p : ℂ}
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hp : Complex.normSq p = 1) :
    (foot b c p - foot a b p) * conj (foot c a p - foot a b p)
      = conj (foot b c p - foot a b p) * (foot c a p - foot a b p) := by
  rw [foot_diff, foot_diff']
  simp only [map_mul, map_sub, map_div₀, map_one, map_ofNat, Complex.conj_conj]
  rw [conj_eq_inv ha, conj_eq_inv hb, conj_eq_inv hc, conj_eq_inv hp]
  have ha0 := ne_zero_of_normSq_one ha
  have hb0 := ne_zero_of_normSq_one hb
  have hc0 := ne_zero_of_normSq_one hc
  have hp0 := ne_zero_of_normSq_one hp
  field_simp
  ring

/-- **Simson's theorem (signed-area form).** The cross product of the two edge-vectors of the
triangle of feet vanishes: `((F_BC - F_AB) * conj (F_CA - F_AB)).im = 0`. Since this imaginary
part is twice the signed area of the triangle `F_AB F_BC F_CA`, the three feet are collinear. -/
theorem simson_collinear {a b c p : ℂ}
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hp : Complex.normSq p = 1) :
    ((foot b c p - foot a b p) * conj (foot c a p - foot a b p)).im = 0 := by
  apply im_eq_zero_of_conj_eq
  rw [map_mul, Complex.conj_conj]
  exact (simson_key ha hb hc hp).symm

end SimsonLineTheorem

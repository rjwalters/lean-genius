import Mathlib.Tactic
import Proofs.SimsonLineTheorem

/-!
# Simson lines rotate at half angular speed — the angle-doubling theorem
  (simson-line-theorem-oq-01-oq-01)

The parent entry `simson-line-theorem-oq-01` proves Simson's theorem (the feet of the
perpendiculars from a circumcircle point `P` onto the side-lines of `△ABC` are collinear),
together with several classical strengthenings. One of them is the special fact that the Simson
lines of **antipodal** points `P` and `-P` are **perpendicular** (`antipodal_simson_perp`).

This entry settles the **sharp generalisation** that the antipodal fact is a single instance of:
as `P` traverses the circumcircle, its Simson line rotates at **half** `P`'s angular speed — the
angle between the Simson lines of `P` and `Q` is exactly half the central angle of the arc `PQ`.
Antipodal points (`Q = -P`) subtend a half-arc of `90°`, recovering perpendicularity.

## The coordinate model and the direction vector

Reusing the parent's model (circumcircle = unit circle, `Complex.normSq · = 1`), the Simson line of
`p` is spanned by `D p := foot b c p - foot a b p`, which `foot_diff` puts in closed form
`(c - a) * (1 - b * conj p) / 2`. On the unit circle (`conj p = p⁻¹`) this simplifies to

    D p = (c - a) * (p - b) / (2 p).                                   (`simson_direction`)

## Why squaring is the right invariant

A line's direction is only defined up to a real scalar, so its angle lives in `ℝ / πℤ`. The naive
Hermitian product `D p * conj (D q)` still depends on the triangle (through `b`). **Squaring**
removes that ambiguity: working with `D p ^ 2` lifts the angle to `ℝ / 2πℤ`, and the triangle
dependence cancels. Concretely, the master identity is the *exact* closed form

    (D p)² · p · conj((D q)² · q) = |c - a|⁴ · |p - b|² · |q - b|² / 16,   (`simson_angle_doubling`)

a manifestly **nonnegative real**. A positive-real value has argument `0 (mod 2π)`, which says

    2·arg(D p / D q) - arg(q / p) ≡ 0 (mod 2π),   i.e.   arg(D p / D q) ≡ ½·arg(q / p) (mod π):

the angle between the two Simson lines is half the arc `PQ`. Realness alone would only pin this down
mod `π/2`; the nonnegativity (not merely realness) of the right-hand side is what makes the encoding
*faithful*. Two corollaries read this off: the product is real (`simson_hermitian_real`) and
nonnegative (`simson_hermitian_nonneg`).

Specialising to `q = -p` recovers the parent's perpendicularity result
(`antipodal_perp_recovered`): the squared form forces `(D p · conj (D (-p)))²` to be a nonpositive
real, hence `D p · conj (D (-p))` is purely imaginary — exactly perpendicularity of the two lines.

The proof is fully machine-checked: no axioms, no `sorry`. The engine is the parent's
`foot_diff` plus `conj z = z⁻¹` on the unit circle, after which every identity is a rational-function
fact closed by `field_simp; ring`.
-/

namespace SimsonLineTheoremOQ01OQ01

open Complex ComplexConjugate
open SimsonLineTheorem (foot foot_diff)

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

/-- **Closed form of the Simson direction.** For `p` on the unit circle, the direction vector
`D p = foot b c p - foot a b p` of the Simson line of `p` equals `(c - a)(p - b)/(2p)`. This is the
parent's `foot_diff` with the conjugate eliminated via `conj p = p⁻¹`; it exposes how the direction
depends on `p` (through the single linear factor `p - b`, divided by `p`). -/
theorem simson_direction {a b c p : ℂ} (hp : Complex.normSq p = 1) :
    foot b c p - foot a b p = (c - a) * (p - b) / (2 * p) := by
  have hp0 := ne_zero_of_normSq_one hp
  rw [foot_diff, conj_eq_inv hp]
  field_simp

/-- **Angle-doubling master identity.** For `A, B, C, P, Q` on the unit circle, the squared Simson
directions satisfy the *exact* closed form

    (D P)² · P · conj((D Q)² · Q) = |C - A|⁴ · |P - B|² · |Q - B|² / 16,

where `D X = foot b c X - foot a b X`. The right-hand side is a manifestly **nonnegative real**, so
the left-hand side has argument `0 (mod 2π)`; equivalently the Simson line of `P` makes with that of
`Q` an angle equal to half the central angle of the arc `PQ`. (Squaring the directions is what lifts
the line-angle to `mod 2π` and cancels the triangle's dependence on `B`.) -/
theorem simson_angle_doubling {a b c p q : ℂ}
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hp : Complex.normSq p = 1) (hq : Complex.normSq q = 1) :
    (foot b c p - foot a b p) ^ 2 * p * conj ((foot b c q - foot a b q) ^ 2 * q)
      = ((Complex.normSq (c - a) ^ 2 * Complex.normSq (p - b) * Complex.normSq (q - b) / 16 : ℝ) :
          ℂ) := by
  have ha0 := ne_zero_of_normSq_one ha
  have hb0 := ne_zero_of_normSq_one hb
  have hc0 := ne_zero_of_normSq_one hc
  have hp0 := ne_zero_of_normSq_one hp
  have hq0 := ne_zero_of_normSq_one hq
  have hca : ((Complex.normSq (c - a) : ℝ) : ℂ) = (c - a) * conj (c - a) :=
    (Complex.mul_conj _).symm
  have hpb : ((Complex.normSq (p - b) : ℝ) : ℂ) = (p - b) * conj (p - b) :=
    (Complex.mul_conj _).symm
  have hqb : ((Complex.normSq (q - b) : ℝ) : ℂ) = (q - b) * conj (q - b) :=
    (Complex.mul_conj _).symm
  rw [foot_diff, foot_diff]
  push_cast
  rw [hca, hpb, hqb]
  simp only [map_mul, map_sub, map_pow, map_div₀, map_one, map_ofNat, Complex.conj_conj]
  rw [conj_eq_inv ha, conj_eq_inv hb, conj_eq_inv hc, conj_eq_inv hp, conj_eq_inv hq]
  field_simp
  ring

/-- **The angle-doubling Hermitian product is real.** Immediate from `simson_angle_doubling`: the
right-hand side is a real number, so the squared-direction Hermitian product has vanishing imaginary
part. -/
theorem simson_hermitian_real {a b c p q : ℂ}
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hp : Complex.normSq p = 1) (hq : Complex.normSq q = 1) :
    ((foot b c p - foot a b p) ^ 2 * p * conj ((foot b c q - foot a b q) ^ 2 * q)).im = 0 := by
  rw [simson_angle_doubling ha hb hc hp hq, Complex.ofReal_im]

/-- **The angle-doubling Hermitian product is nonnegative.** The real part of the squared-direction
Hermitian product equals `|c - a|⁴ |p - b|² |q - b|² / 16 ≥ 0`. Together with `simson_hermitian_real`
this pins the product to the nonnegative real axis — the faithful (mod `2π`) form of angle-doubling
that mere realness could not provide. -/
theorem simson_hermitian_nonneg {a b c p q : ℂ}
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hp : Complex.normSq p = 1) (hq : Complex.normSq q = 1) :
    0 ≤ ((foot b c p - foot a b p) ^ 2 * p * conj ((foot b c q - foot a b q) ^ 2 * q)).re := by
  rw [simson_angle_doubling ha hb hc hp hq, Complex.ofReal_re]
  apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 16)
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)) (Complex.normSq_nonneg _)

/-- **The antipodal-perpendicularity theorem is the `Q = -P` instance.** Specialising the master
identity to `Q = -P` forces `(D P · conj (D (-P)))²` to be a nonpositive real, so `D P · conj (D (-P))`
is purely imaginary: the Simson lines of `P` and its antipode `-P` are perpendicular. This recovers
the parent's `antipodal_simson_perp` as a corollary of angle-doubling (half-arc `= 90°`). -/
theorem antipodal_perp_recovered {a b c p : ℂ}
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hp : Complex.normSq p = 1) :
    ((foot b c p - foot a b p) * conj (foot b c (-p) - foot a b (-p))).re = 0 := by
  have hp0 := ne_zero_of_normSq_one hp
  have hq : Complex.normSq (-p) = 1 := by rwa [Complex.normSq_neg]
  -- abbreviations for the two direction vectors
  set Dp := foot b c p - foot a b p with hDp
  set Dm := foot b c (-p) - foot a b (-p) with hDm
  -- master identity at `q = -p`
  have H := simson_angle_doubling (a := a) (b := b) (c := c) (p := p) (q := -p) ha hb hc hp hq
  rw [← hDp, ← hDm] at H
  -- rewrite the master LHS as `-(Dp * conj Dm)² * (p * conj p)`
  have hpp : p * conj p = 1 := by rw [Complex.mul_conj, hp]; norm_num
  have e : Dp ^ 2 * p * conj (Dm ^ 2 * -p) = -(Dp * conj Dm) ^ 2 * (p * conj p) := by
    rw [map_mul, map_pow, map_neg]; ring
  rw [e, hpp, mul_one] at H
  -- so `(Dp * conj Dm)² = ↑(-R)`, a nonpositive real
  set Y := Dp * conj Dm with hY
  set R : ℝ := Complex.normSq (c - a) ^ 2 * Complex.normSq (p - b) * Complex.normSq (-p - b) / 16
    with hR
  have hYsq : Y ^ 2 = ((-R : ℝ) : ℂ) := by push_cast; linear_combination -H
  -- `Y² = conj (Y²)`, hence `(conj Y)² = Y²`
  have hreal : conj (Y ^ 2) = Y ^ 2 := by rw [hYsq, Complex.conj_ofReal]
  have hsq : (conj Y) ^ 2 = Y ^ 2 := by rw [← map_pow]; exact hreal
  -- factor the difference of squares
  have hfac : (conj Y - Y) * (conj Y + Y) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hfac with h1 | h2
  · -- `conj Y = Y`: `Y` is real with `Y² = -R ≤ 0`, forcing `Y = 0`
    have hYeq : conj Y = Y := sub_eq_zero.mp h1
    have hRnn : 0 ≤ R := by
      rw [hR]
      apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 16)
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _))
        (Complex.normSq_nonneg _)
    have him : Y.im = 0 := im_eq_zero_of_conj_eq hYeq
    -- take real parts of `Y² = ↑(-R)`
    have hre : Y.re ^ 2 - Y.im ^ 2 = -R := by
      have := congrArg Complex.re hYsq
      simpa [pow_two, Complex.mul_re, Complex.ofReal_re] using this
    nlinarith [sq_nonneg Y.re, hRnn, him, hre]
  · -- `conj Y = -Y`: `Y` is purely imaginary, i.e. perpendicularity
    exact re_eq_zero_of_conj_eq_neg (eq_neg_of_add_eq_zero_left h2)

end SimsonLineTheoremOQ01OQ01

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Varignon parallelogram of the van Aubel square-centers is a square
(van-aubel-theorem-oq-01-oq-01)

van Aubel's theorem (parent entry `van-aubel-theorem-oq-01`) takes an arbitrary planar
quadrilateral with vertices `a, b, c, d : ℂ`, erects a square externally on each directed
side, and shows that the two diagonals `PR` and `QS` of the resulting square-center
quadrilateral `P, Q, R, S` are equal in length and perpendicular — all packaged in the single
identity

    R - P = i · (S - Q).                                     (`vanAubel_key`)

This entry pushes one step further and applies **Varignon's theorem** to the square-center
quadrilateral `PQRS`. Varignon's theorem says the midpoints of the sides of *any*
quadrilateral form a parallelogram whose sides are parallel to, and half the length of, the
diagonals. Since the diagonals `PR` and `QS` of `PQRS` are equal and perpendicular, the
Varignon parallelogram of `PQRS` is in fact a **square**.

Concretely, let

* `M₁ = midpoint P Q`,  `M₂ = midpoint Q R`,  `M₃ = midpoint R S`,  `M₄ = midpoint S P`.

The four directed edges `eₖ` of `M₁M₂M₃M₄` satisfy `e_{k+1} = -i · eₖ`, i.e. each side is a
`90°` rotation of the previous one (`varignon_rot12`, `_rot23`, `_rot34`, `_rot41`). A closed
polygon whose consecutive edges are exact `90°` rotations of one another is a square, so we
obtain:

* all four sides have equal length (`varignon_equal_sides`),
* consecutive sides are perpendicular (`varignon_perp`),
* the common side length is exactly half the common van Aubel diagonal length
  (`varignon_side_eq_half_diagonal`).

Everything descends from the parent's key identity `R - P = i·(S - Q)`, which itself is a
one-line `linear_combination` using `i² = -1`. No axioms, no `sorry`.

Not a named Mathlib result.
-/

namespace VanAubelTheoremOQ01OQ01

open Complex ComplexConjugate

/-- Center of the square erected externally on the directed edge `u → v`, using the `+90°`
rotation convention `i · (v - u)` (identical to the parent entry's `squareCenter`). -/
noncomputable def squareCenter (u v : ℂ) : ℂ := (u + v) / 2 + I * (v - u) / 2

/-- The four square centers `P, Q, R, S` of the quadrilateral `a, b, c, d`. -/
noncomputable def P (a b c d : ℂ) : ℂ := squareCenter a b
noncomputable def Q (a b c d : ℂ) : ℂ := squareCenter b c
noncomputable def R (a b c d : ℂ) : ℂ := squareCenter c d
noncomputable def S (a b c d : ℂ) : ℂ := squareCenter d a

/-- **Parent key identity** (restated for self-containedness): the diagonal `R - P` of the
square-center quadrilateral equals `i` times the diagonal `S - Q`. Proved by
`linear_combination` from `i² = -1`. -/
theorem vanAubel_key (a b c d : ℂ) :
    R a b c d - P a b c d = I * (S a b c d - Q a b c d) := by
  unfold R P S Q squareCenter
  linear_combination (-(a + b - c - d) / 2) * Complex.I_sq

/-- Midpoint of two complex points. -/
noncomputable def mid (x y : ℂ) : ℂ := (x + y) / 2

/-- The four Varignon midpoints of the square-center quadrilateral `PQRS`. -/
noncomputable def M₁ (a b c d : ℂ) : ℂ := mid (P a b c d) (Q a b c d)
noncomputable def M₂ (a b c d : ℂ) : ℂ := mid (Q a b c d) (R a b c d)
noncomputable def M₃ (a b c d : ℂ) : ℂ := mid (R a b c d) (S a b c d)
noncomputable def M₄ (a b c d : ℂ) : ℂ := mid (S a b c d) (P a b c d)

/-- Edge `M₁ → M₂` of the Varignon quadrilateral equals half the diagonal `R - P`. This is the
content of Varignon's theorem for this edge: the side is parallel to a diagonal, half length. -/
theorem varignon_edge12 (a b c d : ℂ) :
    M₂ a b c d - M₁ a b c d = (R a b c d - P a b c d) / 2 := by
  unfold M₂ M₁ mid; ring

/-- Edge `M₂ → M₃` equals half the diagonal `S - Q`. -/
theorem varignon_edge23 (a b c d : ℂ) :
    M₃ a b c d - M₂ a b c d = (S a b c d - Q a b c d) / 2 := by
  unfold M₃ M₂ mid; ring

/-- Edge `M₃ → M₄` equals `-(R - P)/2` (the reverse of the first edge). -/
theorem varignon_edge34 (a b c d : ℂ) :
    M₄ a b c d - M₃ a b c d = -(R a b c d - P a b c d) / 2 := by
  unfold M₄ M₃ mid; ring

/-- Edge `M₄ → M₁` equals `-(S - Q)/2` (the reverse of the second edge). -/
theorem varignon_edge41 (a b c d : ℂ) :
    M₁ a b c d - M₄ a b c d = -(S a b c d - Q a b c d) / 2 := by
  unfold M₁ M₄ mid; ring

/-- **Rotation, edge 1 → edge 2.** The second Varignon edge is the first rotated by `-90°`
(`-i`). This is the square-ness of the corner at `M₂`. Follows from the parent key identity. -/
theorem varignon_rot12 (a b c d : ℂ) :
    M₃ a b c d - M₂ a b c d = -I * (M₂ a b c d - M₁ a b c d) := by
  rw [varignon_edge23, varignon_edge12]
  -- R - P = I·(S - Q) ⟹ S - Q = -I·(R - P), since I·(-I) = 1.
  have hSQ : S a b c d - Q a b c d = -I * (R a b c d - P a b c d) := by
    linear_combination I * vanAubel_key a b c d
      + (S a b c d - Q a b c d) * Complex.I_sq
  rw [hSQ]; ring

/-- **Rotation, edge 2 → edge 3.** Needs only the key identity (no `i² = -1`). -/
theorem varignon_rot23 (a b c d : ℂ) :
    M₄ a b c d - M₃ a b c d = -I * (M₃ a b c d - M₂ a b c d) := by
  rw [varignon_edge34, varignon_edge23]
  rw [vanAubel_key a b c d]; ring

/-- **Rotation, edge 3 → edge 4.** -/
theorem varignon_rot34 (a b c d : ℂ) :
    M₁ a b c d - M₄ a b c d = -I * (M₄ a b c d - M₃ a b c d) := by
  rw [varignon_edge41, varignon_edge34]
  have hSQ : S a b c d - Q a b c d = -I * (R a b c d - P a b c d) := by
    linear_combination I * vanAubel_key a b c d
      + (S a b c d - Q a b c d) * Complex.I_sq
  rw [hSQ]; ring

/-- **Rotation, edge 4 → edge 1.** Closes the loop. Needs only the key identity. -/
theorem varignon_rot41 (a b c d : ℂ) :
    M₂ a b c d - M₁ a b c d = -I * (M₁ a b c d - M₄ a b c d) := by
  rw [varignon_edge12, varignon_edge41]
  rw [vanAubel_key a b c d]; ring

/-- **Varignon is a parallelogram** (opposite edges are equal and opposite): the four edges
sum to zero, so the polygon closes. Automatic for any quadrilateral's midpoints. -/
theorem varignon_closes (a b c d : ℂ) :
    (M₂ a b c d - M₁ a b c d) + (M₃ a b c d - M₂ a b c d)
      + (M₄ a b c d - M₃ a b c d) + (M₁ a b c d - M₄ a b c d) = 0 := by
  ring

/-- **Equal sides.** All four sides of the Varignon quadrilateral have the same length: it is
equilateral. Immediate from the `-i` rotation identities, since `|-i| = 1`. -/
theorem varignon_equal_sides (a b c d : ℂ) :
    ‖M₂ a b c d - M₁ a b c d‖ = ‖M₃ a b c d - M₂ a b c d‖
      ∧ ‖M₃ a b c d - M₂ a b c d‖ = ‖M₄ a b c d - M₃ a b c d‖
      ∧ ‖M₄ a b c d - M₃ a b c d‖ = ‖M₁ a b c d - M₄ a b c d‖ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [varignon_rot12, norm_mul, norm_neg, Complex.norm_I, one_mul]
  · rw [varignon_rot23, norm_mul, norm_neg, Complex.norm_I, one_mul]
  · rw [varignon_rot34, norm_mul, norm_neg, Complex.norm_I, one_mul]

/-- **Perpendicular consecutive sides.** Each corner of the Varignon quadrilateral is a right
angle: the real part of `edgeₖ · conj(edge_{k+1})` vanishes. Together with equal sides this
makes it a square. Shown here at the corner `M₂` (edge 1 vs edge 2); the other corners are
identical by the analogous rotation identities. -/
theorem varignon_perp (a b c d : ℂ) :
    ((M₂ a b c d - M₁ a b c d) *
        conj (M₃ a b c d - M₂ a b c d)).re = 0 := by
  rw [varignon_rot12, map_mul]
  rw [show conj (-I) = I by simp, ← mul_assoc, mul_comm _ I, mul_assoc,
    Complex.mul_conj]
  simp [Complex.ofReal_im]

/-- **Side length is half the diagonal.** The common Varignon side length equals half the
common van Aubel diagonal length `‖R - P‖ = ‖S - Q‖`. This pins down the size of the square. -/
theorem varignon_side_eq_half_diagonal (a b c d : ℂ) :
    ‖M₂ a b c d - M₁ a b c d‖ = ‖R a b c d - P a b c d‖ / 2 := by
  rw [varignon_edge12, norm_div]
  simp

end VanAubelTheoremOQ01OQ01

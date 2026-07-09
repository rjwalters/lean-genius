/-
# Pythagorean Theorem OQ-06: de Gua's Theorem (the 3-D Pythagorean theorem)

## What This Proves

**de Gua's theorem** is the three-dimensional analogue of the Pythagorean theorem.
For a tetrahedron that has a *right-angle corner* -- an apex `O` at which the three
edges are mutually perpendicular -- the square of the area of the face *opposite*
`O` (the "hypotenuse face") equals the sum of the squares of the areas of the three
faces meeting at `O`:

  `Area(hypotenuse face)² = Area(face₁)² + Area(face₂)² + Area(face₃)².`

This is a genuine generalisation of Pythagoras: unlike the planar identity
`‖v + w‖² = ‖v‖² + ‖w‖²` (which, in a fixed inner-product model, is just the
polarization identity), de Gua's theorem is a statement about *areas of triangles
in ℝ³* and does not collapse to the norm identity.

## Proof Strategy

We model a triangle by its three vertices in `ℝ³ = Fin 3 → ℝ` and use the classical
cross-product area formula: the (unsigned) area of the triangle `P Q R` is
`½‖(Q − P) × (R − P)‖`, hence its squared area is
`sqArea P Q R = ¼‖(Q − P) × (R − P)‖²`, where `‖x‖² = x ⬝ᵥ x`.

Place the right-angle apex at `O` with three mutually perpendicular edge vectors
`u, v, w`. Two facts drive the proof:

1. **Edge expansion.** The hypotenuse face has edge vectors `v − u` and `w − u`, and
   `(v − u) × (w − u) = u × v + v × w + w × u` (bilinearity + anticommutativity, with
   `u × u = 0`).

2. **Orthogonal cross terms vanish.** Expanding `‖u×v + v×w + w×u‖²` produces three
   mixed terms of the form `(u×v) ⬝ᵥ (v×w)`. The Binet–Cauchy identity
   (`cross_dot_cross`) evaluates each to a combination of dot products
   `(u⬝ᵥv), (v⬝ᵥw), (w⬝ᵥu)`, every one of which is zero by mutual perpendicularity.

What survives is exactly `‖u×v‖² + ‖v×w‖² + ‖w×u‖²`, i.e. the three leg-face areas.

## Key Results

- `deGua`            — general form for perpendicular edge vectors `u, v, w` at apex `O`.
- `deGua_zero`       — apex-at-origin form: `sqArea u v w = sqArea 0 u v + sqArea 0 v w + sqArea 0 w u`.
- `deGua_scalar`     — the recognisable closed form with axis-aligned edges of lengths
                       `a, b, c`: hypotenuse area² `= (½ab)² + (½bc)² + (½ca)²`.

All results are proved with no `sorry` and no additional axioms.
-/
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

open Matrix

namespace PythagoreanDeGua

/-- The **squared area** of the triangle with vertices `P`, `Q`, `R` in `ℝ³`.

Using the cross-product area formula `area = ½‖(Q − P) × (R − P)‖`, the squared area
is `¼‖(Q − P) × (R − P)‖²`, where the squared Euclidean norm of a vector `x` is the
self dot product `x ⬝ᵥ x`. -/
noncomputable def sqArea (P Q R : Fin 3 → ℝ) : ℝ :=
  (1 / 4) * (((Q - P) ⨯₃ (R - P)) ⬝ᵥ ((Q - P) ⨯₃ (R - P)))

/-- **Edge expansion.** For any `u v w : ℝ³`, the cross product of the two edge
vectors `v − u`, `w − u` of the "hypotenuse" triangle telescopes into a cyclic sum of
cross products of the original edges:
`(v − u) × (w − u) = u × v + v × w + w × u`.

This uses only bilinearity of the cross product and `u × u = 0`; no orthogonality is
required here. -/
theorem hyp_edge_cross (u v w : Fin 3 → ℝ) :
    (v - u) ⨯₃ (w - u) = u ⨯₃ v + v ⨯₃ w + w ⨯₃ u := by
  rw [map_sub crossProduct v u, LinearMap.sub_apply,
      map_sub (crossProduct v) w u, map_sub (crossProduct u) w u]
  simp only [cross_self, sub_zero]
  rw [← cross_anticomm u v, ← cross_anticomm w u]
  abel

/-- **de Gua's theorem** (general form).

Let `u`, `v`, `w` be three mutually perpendicular edge vectors emanating from the apex
`O` of a tetrahedron `O, O+u, O+v, O+w`. Then the squared area of the face opposite
`O` equals the sum of the squared areas of the three faces meeting at `O`. -/
theorem deGua (O u v w : Fin 3 → ℝ)
    (huv : u ⬝ᵥ v = 0) (hvw : v ⬝ᵥ w = 0) (hwu : w ⬝ᵥ u = 0) :
    sqArea (O + u) (O + v) (O + w)
      = sqArea O (O + u) (O + v)
      + sqArea O (O + v) (O + w)
      + sqArea O (O + w) (O + u) := by
  -- Symmetric companions of the orthogonality hypotheses.
  have huw : u ⬝ᵥ w = 0 := by rw [dotProduct_comm]; exact hwu
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm]; exact huv
  have hwv : w ⬝ᵥ v = 0 := by rw [dotProduct_comm]; exact hvw
  -- The three mixed cross terms vanish, via the Binet–Cauchy identity.
  have h1 : (u ⨯₃ v) ⬝ᵥ (v ⨯₃ w) = 0 := by rw [cross_dot_cross, huv, huw]; ring
  have h2 : (v ⨯₃ w) ⬝ᵥ (w ⨯₃ u) = 0 := by rw [cross_dot_cross, hvw, hvu]; ring
  have h3 : (w ⨯₃ u) ⬝ᵥ (u ⨯₃ v) = 0 := by rw [cross_dot_cross, hwu, hwv]; ring
  have h1' : (v ⨯₃ w) ⬝ᵥ (u ⨯₃ v) = 0 := by rw [dotProduct_comm]; exact h1
  have h2' : (w ⨯₃ u) ⬝ᵥ (v ⨯₃ w) = 0 := by rw [dotProduct_comm]; exact h2
  have h3' : (u ⨯₃ v) ⬝ᵥ (w ⨯₃ u) = 0 := by rw [dotProduct_comm]; exact h3
  -- Reduce all four face edge-vectors, then expand the hypotenuse norm.
  simp only [sqArea, add_sub_cancel_left, add_sub_add_left_eq_sub]
  rw [hyp_edge_cross]
  simp only [dotProduct_add, add_dotProduct, h1, h2, h3, h1', h2', h3']
  ring

/-- **de Gua's theorem**, apex at the origin. With the right-angle corner at `0` and
mutually perpendicular edges `u, v, w`, the hypotenuse face is the triangle `u v w`. -/
theorem deGua_zero (u v w : Fin 3 → ℝ)
    (huv : u ⬝ᵥ v = 0) (hvw : v ⬝ᵥ w = 0) (hwu : w ⬝ᵥ u = 0) :
    sqArea u v w = sqArea 0 u v + sqArea 0 v w + sqArea 0 w u := by
  have h := deGua 0 u v w huv hvw hwu
  simpa using h

/-- **de Gua's theorem**, classical scalar form. With mutually perpendicular edges of
lengths `a, b, c` along the coordinate axes, the three faces meeting at the origin have
areas `½ab, ½bc, ½ca`, and the hypotenuse face `A B C` satisfies
`Area(ABC)² = (½ab)² + (½bc)² + (½ca)²`. -/
theorem deGua_scalar (a b c : ℝ) :
    sqArea ![a, 0, 0] ![0, b, 0] ![0, 0, c]
      = (1 / 2 * a * b) ^ 2 + (1 / 2 * b * c) ^ 2 + (1 / 2 * c * a) ^ 2 := by
  simp only [sqArea, cross_apply, vec3_dotProduct, Pi.sub_apply]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

end PythagoreanDeGua

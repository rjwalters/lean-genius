import Mathlib

/-
# Law of Cosines — OQ-07-OQ-02-OQ-01: the Leibniz / Lagrange identity

## Research Problem: law-of-cosines-oq-07-oq-02-oq-01

The parent entry `law-of-cosines-oq-07-oq-02` computes the *sum of the squared
medians* of a triangle. Its open question asks for the underlying **Leibniz /
Lagrange identity**: for any point `p` and the centroid `g` of a triangle with
vertices `a b c`,

    dist p a ² + dist p b ² + dist p c ²
        = 3 · dist p g ²  +  (dist g a ² + dist g b ² + dist g c ²),

i.e. the total squared distance from a moving point `p` to the three vertices
splits into a part that depends on `p` only through `dist p g` and a constant
part `∑ dist g vertex ²`. Specialising further gives the **centroid identity**

    dist g a ² + dist g b ² + dist g c ²  =  ⅓ · (a² + b² + c²),

answering the parent's question of whether the median/centroid relation can be
recovered (here directly, without passing through the 2:1 median ratio).

The single mathematical input is the polarisation of the norm: writing
`p -ᵥ vᵢ = (p -ᵥ g) + (g -ᵥ vᵢ)` and expanding `‖·‖²`, the cross term is
`2 ⟪p -ᵥ g, (g -ᵥ a) + (g -ᵥ b) + (g -ᵥ c)⟫`, which vanishes precisely because
`g` is the centroid: `(a -ᵥ g) + (b -ᵥ g) + (c -ᵥ g) = 0`.

Like the parent, everything is **coordinate-free**: `a b c p` are genuine points
of a real inner-product affine space (`NormedAddTorsor`), `g` is an honest point,
and distances are `dist`s. The result holds in every Euclidean affine space of
any dimension. The centroid is built explicitly so no extra hypotheses are
needed.

DISTINCT from the parent (sum of squared *medians*): the content here is the
Leibniz/Lagrange splitting for an *arbitrary* point `p`, of which the median sum
is one instance (`p` ranging over the vertices).

Tags: geometry, centroid, leibniz-identity, lagrange-identity, inner-product-space
-/

namespace LawOfCosinesOQ07OQ02OQ01

open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- The **centroid** of three points `a b c`, given explicitly as the point
`g` with `g -ᵥ a = ⅓·((b -ᵥ a) + (c -ᵥ a))`.  This is the barycentre that
divides each median in ratio `2 : 1`. -/
noncomputable def centroid₃ (a b c : P) : P :=
  (3⁻¹ : ℝ) • ((b -ᵥ a) + (c -ᵥ a)) +ᵥ a

/-- The defining **balance** property of the centroid: the displacement vectors
from the three vertices to the centroid sum to zero. -/
theorem centroid₃_balance (a b c : P) :
    (a -ᵥ centroid₃ a b c) + (b -ᵥ centroid₃ a b c) + (c -ᵥ centroid₃ a b c)
      = (0 : V) := by
  simp only [centroid₃, vsub_vadd_eq_vsub_sub, vsub_self]
  module

/-- **Leibniz / Lagrange identity** (abstract centroid form).

For any points `a b c p` and any point `g` whose vertex-displacements balance
(`(a -ᵥ g) + (b -ᵥ g) + (c -ᵥ g) = 0`), the total squared distance from `p`
to the three vertices splits as

    dist p a ² + dist p b ² + dist p c ²
      = 3 · dist p g ² + (dist g a ² + dist g b ² + dist g c ²).

Proof: polarise each `‖p -ᵥ vᵢ‖²` along `p -ᵥ vᵢ = (p -ᵥ g) + (g -ᵥ vᵢ)`; the
three cross terms add to `2 ⟪p -ᵥ g, (g -ᵥ a)+(g -ᵥ b)+(g -ᵥ c)⟫`, and the
balance hypothesis makes the inner factor zero. -/
theorem leibniz_identity (a b c p g : P)
    (hg : (a -ᵥ g) + (b -ᵥ g) + (c -ᵥ g) = (0 : V)) :
    dist p a ^ 2 + dist p b ^ 2 + dist p c ^ 2
      = 3 * dist p g ^ 2 + (dist g a ^ 2 + dist g b ^ 2 + dist g c ^ 2) := by
  -- the centroid balance, written with the vertices as the *second* argument
  have hsum : (g -ᵥ a) + (g -ᵥ b) + (g -ᵥ c) = (0 : V) := by
    have h : (g -ᵥ a) + (g -ᵥ b) + (g -ᵥ c)
        = -((a -ᵥ g) + (b -ᵥ g) + (c -ᵥ g)) := by
      simp only [neg_add, neg_vsub_eq_vsub_rev]
    rw [h, hg, neg_zero]
  -- polarisation of each squared distance about the centroid `g`
  have key : ∀ x : P, dist p x ^ 2
      = dist p g ^ 2 + 2 * ⟪p -ᵥ g, g -ᵥ x⟫ + dist g x ^ 2 := by
    intro x
    rw [dist_eq_norm_vsub V p x, dist_eq_norm_vsub V p g, dist_eq_norm_vsub V g x,
      ← vsub_add_vsub_cancel p g x, norm_add_sq_real]
  rw [key a, key b, key c]
  -- the three cross terms collapse to an inner product against `0`
  have hcross : ⟪p -ᵥ g, g -ᵥ a⟫ + ⟪p -ᵥ g, g -ᵥ b⟫ + ⟪p -ᵥ g, g -ᵥ c⟫ = (0 : ℝ) := by
    rw [← inner_add_right, ← inner_add_right, hsum, inner_zero_right]
  linear_combination 2 * hcross

/-- **Leibniz / Lagrange identity** for the actual triangle centroid `centroid₃`.
The balance hypothesis is discharged by `centroid₃_balance`. -/
theorem leibniz_centroid (a b c p : P) :
    dist p a ^ 2 + dist p b ^ 2 + dist p c ^ 2
      = 3 * dist p (centroid₃ a b c) ^ 2
        + (dist (centroid₃ a b c) a ^ 2 + dist (centroid₃ a b c) b ^ 2
            + dist (centroid₃ a b c) c ^ 2) :=
  leibniz_identity a b c p (centroid₃ a b c) (centroid₃_balance a b c)

/-- **Centroid identity**: the sum of the squared distances from the centroid to
the three vertices equals one third of the sum of the squared side lengths,

    dist g a ² + dist g b ² + dist g c ²  =  ⅓ · (dist a b ² + dist b c ² + dist c a ²).

Derived purely from three instances of `leibniz_centroid` (with `p` ranging over
the vertices) together with the symmetry `dist x y = dist y x`. -/
theorem centroid_sum_sq (a b c : P) :
    dist (centroid₃ a b c) a ^ 2 + dist (centroid₃ a b c) b ^ 2
        + dist (centroid₃ a b c) c ^ 2
      = (3⁻¹ : ℝ) * (dist a b ^ 2 + dist b c ^ 2 + dist c a ^ 2) := by
  set g := centroid₃ a b c with hgdef
  have ea := leibniz_centroid a b c a
  have eb := leibniz_centroid a b c b
  have ec := leibniz_centroid a b c c
  rw [← hgdef] at ea eb ec
  -- kill the self-distances `dist a a = 0`, etc.
  simp only [dist_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add, add_zero] at ea eb ec
  -- squared-distance symmetries needed to align the atoms
  have s1 : dist a g ^ 2 = dist g a ^ 2 := by rw [dist_comm]
  have s2 : dist b g ^ 2 = dist g b ^ 2 := by rw [dist_comm]
  have s3 : dist c g ^ 2 = dist g c ^ 2 := by rw [dist_comm]
  have s4 : dist a c ^ 2 = dist c a ^ 2 := by rw [dist_comm]
  have s5 : dist b a ^ 2 = dist a b ^ 2 := by rw [dist_comm]
  have s6 : dist c b ^ 2 = dist b c ^ 2 := by rw [dist_comm]
  linarith [ea, eb, ec, s1, s2, s3, s4, s5, s6]

end LawOfCosinesOQ07OQ02OQ01

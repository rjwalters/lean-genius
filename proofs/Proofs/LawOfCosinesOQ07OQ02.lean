import Mathlib
import Proofs.LawOfCosinesOQ07

/-
# Law of Cosines — OQ-07-OQ-02: Sum of the squared medians of a triangle

## Research Problem: law-of-cosines-oq-07-oq-02

OQ: In any triangle with sides `a, b, c` and medians `mₐ, m_b, m_c`, the sum of
the squares of the medians is exactly three quarters of the sum of the squares
of the sides:

    mₐ² + m_b² + m_c² = ¾ · (a² + b² + c²),

equivalently `4·(mₐ² + m_b² + m_c²) = 3·(a² + b² + c²)`.

This is the natural three-fold consequence of the parent's `median_length`
formula (`law-of-cosines-oq-07`):

    4·mₐ² = 2·b² + 2·c² − a²      (median from the `a`-vertex),

applied cyclically to all three medians and summed. Each side-square appears in
the running total with net coefficient `2 + 2 − 1 = 3`, while the median sum
carries the factor `4`, yielding `4·∑m² = 3·∑s²`.

Like the parent, the statement is **coordinate-free**: the vertices `a b c` are
genuine points of a real inner-product affine space (`NormedAddTorsor`), the
medians are `dist`s to honest `midpoint`s, and no scalar side-length
parameterisation is introduced. The result therefore holds in every Euclidean
affine space, of any dimension.

DISTINCT from the parent `law-of-cosines-oq-07` (single median, Apollonius) and
from `law-of-cosines-oq-04` (scalar Stewart/median-length algebra): here the
content is the *global* relation across all three medians at once.

Tags: geometry, median, apollonius, law-of-cosines
-/

open LawOfCosinesOQ07

namespace LawOfCosinesOQ07OQ02

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- **Sum of squared medians** (metric / coordinate-free form).

For a triangle with vertices `a b c` in a real inner-product affine space, write
`mₐ = dist a (midpoint ℝ b c)`, `m_b = dist b (midpoint ℝ a c)`,
`m_c = dist c (midpoint ℝ a b)` for the three medians. Then

    4·(mₐ² + m_b² + m_c²) = 3·(ab² + bc² + ca²).

Proof: sum the parent's `median_length` identity over the three vertices. After
folding the `dist`-symmetries `dist b a = dist a b`, `dist a c = dist c a`,
`dist c b = dist b c`, each side-square gathers coefficient `3` and the medians
the factor `4`; `linear_combination` of the three instances closes the goal. -/
theorem sum_sq_medians (a b c : P) :
    4 * (dist a (midpoint ℝ b c) ^ 2
        + dist b (midpoint ℝ a c) ^ 2
        + dist c (midpoint ℝ a b) ^ 2)
      = 3 * (dist a b ^ 2 + dist b c ^ 2 + dist c a ^ 2) := by
  have ha := median_length a b c
  have hb := median_length b a c
  have hc := median_length c a b
  simp only [dist_comm a c, dist_comm b a, dist_comm c b] at ha hb hc
  linear_combination ha + hb + hc

/-- **Sum of squared medians** in the `¾` ratio form: the median squares sum to
three quarters of the side squares. A direct rescaling of `sum_sq_medians`. -/
theorem sum_sq_medians_three_quarters (a b c : P) :
    dist a (midpoint ℝ b c) ^ 2
        + dist b (midpoint ℝ a c) ^ 2
        + dist c (midpoint ℝ a b) ^ 2
      = 3 / 4 * (dist a b ^ 2 + dist b c ^ 2 + dist c a ^ 2) := by
  have h := sum_sq_medians a b c
  linear_combination h / 4

/-- Concrete instantiation in the Euclidean plane `EuclideanSpace ℝ (Fin 2)`:
the abstract median identity holds in the standard model of plane geometry. -/
example (a b c : EuclideanSpace ℝ (Fin 2)) :
    4 * (dist a (midpoint ℝ b c) ^ 2
        + dist b (midpoint ℝ a c) ^ 2
        + dist c (midpoint ℝ a b) ^ 2)
      = 3 * (dist a b ^ 2 + dist b c ^ 2 + dist c a ^ 2) :=
  sum_sq_medians a b c

end LawOfCosinesOQ07OQ02

/-
  The Leibniz Parallel-Axis Identity — total sum of squared distances to a point set
  Open Question: british-flag-theorem-oq-01-oq-03

  The British-Flag branch of this gallery studies the *alternating* signed combination
    ∑_t (-1)^|t| ‖P - V_t‖²
  of squared distances and shows it is observer-independent (zero for a rectangle, or a
  fixed inner-product defect for a parallelogram). This leaf is the *complementary*
  identity those entries never touch: instead of the alternating sum, take the plain
  *total* sum ∑_i ‖P - V_i‖², which is **not** observer-independent — it carries an exact,
  clean P-dependence around the centroid G.

  ## Main Results

  `leibniz_parallel_axis_sum` (PROVED): for any finite family of points `v : ι → V` in a
  real inner product space with centroid `G` (i.e. `∑ i, (v i - G) = 0`), and any observer
  `P`,
    ∑ i, ‖P - v i‖²  =  (∑ i, ‖G - v i‖²)  +  (card ι) · ‖P - G‖².

  `leibniz_parallel_axis` (PROVED): the headline three-vertex case with explicit centroid
  `G = ⅓(A + B + C)`,
    ‖P-A‖² + ‖P-B‖² + ‖P-C‖²  =  (‖G-A‖² + ‖G-B‖² + ‖G-C‖²)  +  3‖P-G‖².

  `centroid_minimizes_sum_sq_dist` (PROVED): consequently the centroid minimizes the sum
  of squared distances — ∑ ‖G - v i‖² ≤ ∑ ‖P - v i‖² for every P, with equality iff P = G.

  ## Proof Strategy

  Translate so the base point is the centroid `G`: write `P - v i = (P - G) + (G - v i)`
  and expand each squared norm with `norm_add_sq_real`,
    ‖P - v i‖² = ‖P - G‖² + 2⟪P - G, G - v i⟫ + ‖G - v i‖².
  Summing over `i`, the constant term gives `(card ι)‖P - G‖²`, the squared term gives
  `∑ ‖G - v i‖²`, and the cross term is `2⟪P - G, ∑ (G - v i)⟫`, which vanishes because the
  centroid condition forces `∑ (G - v i) = 0`. No symmetry juggling is needed: every inner
  product appears with the same orientation.
-/

import Mathlib

open scoped InnerProductSpace BigOperators

namespace BritishFlagTheoremOQ0103

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Leibniz parallel-axis identity (general finite family).** For a finite family of
points `v : ι → V` whose centroid is `G` (encoded as `∑ i, (v i - G) = 0`), the total sum of
squared distances from any observer `P` to the points decomposes as the sum about the
centroid plus `(card ι)‖P - G‖²`. -/
theorem leibniz_parallel_axis_sum {ι : Type*} [Fintype ι]
    (P G : V) (v : ι → V) (hG : ∑ i, (v i - G) = 0) :
    ∑ i, ‖P - v i‖ ^ 2
      = (∑ i, ‖G - v i‖ ^ 2) + (Fintype.card ι : ℝ) * ‖P - G‖ ^ 2 := by
  -- Per-point expansion about the centroid.
  have key : ∀ i, ‖P - v i‖ ^ 2
      = ‖P - G‖ ^ 2 + 2 * (⟪P - G, G - v i⟫_ℝ) + ‖G - v i‖ ^ 2 := by
    intro i
    have h : P - v i = (P - G) + (G - v i) := by abel
    rw [h, norm_add_sq_real]
  -- The centroid condition, rewritten in the `(G - v i)` orientation.
  have hzero : ∑ i, (G - v i) = 0 := by
    have h2 : (∑ i, (G - v i)) + ∑ i, (v i - G) = 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_eq_zero
      intro i _
      abel
    rw [hG, add_zero] at h2
    exact h2
  -- The cross term vanishes.
  have hY : ∑ i, 2 * (⟪P - G, G - v i⟫_ℝ) = 0 := by
    rw [← Finset.mul_sum, ← inner_sum, hzero, inner_zero_right, mul_zero]
  -- The constant term sums to `(card ι)‖P - G‖²`.
  have hX : (∑ _i : ι, ‖P - G‖ ^ 2) = (Fintype.card ι : ℝ) * ‖P - G‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- Assemble.
  simp_rw [key]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hX, hY]
  ring

/-- **Leibniz parallel-axis identity (three vertices).** With centroid `G = ⅓(A + B + C)`,
    ‖P-A‖² + ‖P-B‖² + ‖P-C‖² = (‖G-A‖² + ‖G-B‖² + ‖G-C‖²) + 3‖P-G‖². -/
theorem leibniz_parallel_axis (P A B C G : V)
    (hG : G = (3 : ℝ)⁻¹ • (A + B + C)) :
    ‖P - A‖ ^ 2 + ‖P - B‖ ^ 2 + ‖P - C‖ ^ 2
      = (‖G - A‖ ^ 2 + ‖G - B‖ ^ 2 + ‖G - C‖ ^ 2) + 3 * ‖P - G‖ ^ 2 := by
  have key : ∀ X : V, ‖P - X‖ ^ 2
      = ‖P - G‖ ^ 2 + 2 * (⟪P - G, G - X⟫_ℝ) + ‖G - X‖ ^ 2 := by
    intro X
    have h : P - X = (P - G) + (G - X) := by abel
    rw [h, norm_add_sq_real]
  have hcross :
      (⟪P - G, G - A⟫_ℝ) + ⟪P - G, G - B⟫_ℝ + ⟪P - G, G - C⟫_ℝ = 0 := by
    rw [← inner_add_right, ← inner_add_right]
    have hz : (G - A) + (G - B) + (G - C) = 0 := by rw [hG]; module
    rw [hz, inner_zero_right]
  rw [key A, key B, key C]
  linarith [hcross]

/-- **The centroid minimizes the total sum of squared distances.** For any observer `P`,
the sum of squared distances to the points is at least the sum about the centroid. -/
theorem centroid_minimizes_sum_sq_dist {ι : Type*} [Fintype ι]
    (P G : V) (v : ι → V) (hG : ∑ i, (v i - G) = 0) :
    (∑ i, ‖G - v i‖ ^ 2) ≤ ∑ i, ‖P - v i‖ ^ 2 := by
  rw [leibniz_parallel_axis_sum P G v hG]
  have h : (0 : ℝ) ≤ (Fintype.card ι : ℝ) * ‖P - G‖ ^ 2 := by positivity
  linarith

/-- **Equality in the centroid bound holds exactly at the centroid** (when the family is
nonempty). If the total squared-distance sum from `P` equals the sum about the centroid,
then `P = G`. -/
theorem eq_centroid_of_sum_sq_dist_eq {ι : Type*} [Fintype ι] [Nonempty ι]
    (P G : V) (v : ι → V) (hG : ∑ i, (v i - G) = 0)
    (heq : (∑ i, ‖G - v i‖ ^ 2) = ∑ i, ‖P - v i‖ ^ 2) :
    P = G := by
  rw [leibniz_parallel_axis_sum P G v hG] at heq
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hnorm : ‖P - G‖ ^ 2 = 0 := by
    have : (Fintype.card ι : ℝ) * ‖P - G‖ ^ 2 = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (ne_of_gt hcard)
    · exact h
  have : ‖P - G‖ = 0 := by
    have := sq_eq_zero_iff.mp hnorm
    exact this
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this

/-- Specialization to the Euclidean plane `EuclideanSpace ℝ (Fin 2)`, the setting of the
classical British-Flag / Viviani gallery entries: the centroid form for a triangle. -/
theorem leibniz_parallel_axis_plane
    (P A B C G : EuclideanSpace ℝ (Fin 2))
    (hG : G = (3 : ℝ)⁻¹ • (A + B + C)) :
    ‖P - A‖ ^ 2 + ‖P - B‖ ^ 2 + ‖P - C‖ ^ 2
      = (‖G - A‖ ^ 2 + ‖G - B‖ ^ 2 + ‖G - C‖ ^ 2) + 3 * ‖P - G‖ ^ 2 :=
  leibniz_parallel_axis P A B C G hG

end BritishFlagTheoremOQ0103

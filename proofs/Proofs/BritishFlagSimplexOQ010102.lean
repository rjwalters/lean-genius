/-
  The Weighted Leibniz Identity
  (affine-simplex generalization of the British Flag squared-distance identity)
  Open Question: british-flag-theorem-oq-01-oq-01-oq-02

  The British Flag Theorem, and its parallelogram-defect sharpening
  (`BritishFlagTheoremOQ01OQ01`), are the four-point instances of a single
  weighted squared-distance identity attached to an arbitrary finite family of
  points — the classical **Leibniz relation** (a.k.a. the generalized parallel
  axis / Stewart relation).

  Given a finite family of points `v i` in a real inner product space, real
  weights `w i`, an observer `p`, and ANY reference point `g`, the weighted sum
  of squared distances decomposes as

    ∑ᵢ wᵢ ‖p − vᵢ‖²
      = W ‖p − g‖²  −  2 ⟪p − g, (∑ᵢ wᵢ • vᵢ) − W • g⟫  +  ∑ᵢ wᵢ ‖vᵢ − g‖²,

  where `W = ∑ᵢ wᵢ`.  This is `weighted_dist_sq_master`.

  ## Corollaries

  * `weighted_leibniz` — when `g` is the weighted barycenter
    (`∑ᵢ wᵢ • vᵢ = W • g`), the cross term vanishes and we obtain the Leibniz
    relation
      ∑ᵢ wᵢ ‖p − vᵢ‖² = W ‖p − g‖² + ∑ᵢ wᵢ ‖vᵢ − g‖².
    The `p`-dependence is isolated in the single term `W ‖p − g‖²`.

  * `british_flag_independence` — when the weights are *balanced*
    (`W = 0` and `∑ᵢ wᵢ • vᵢ = 0`), the weighted sum of squared distances is
    **independent of the observer** `p`.  This is the abstract content of the
    British Flag Theorem: the signed combination of squared distances is a
    constant of the point configuration alone.

  * `british_flag_rectangle` — recovers the classical four-point statement
    ‖P−A‖² + ‖P−C‖² = ‖P−B‖² + ‖P−D‖² for a *rectangle* `A, B, C, D`
    (parallelogram closure `C = B + D − A` together with the orthogonality
    `⟪B − A, D − A⟫ = 0`).  This is the balanced-weight `(1, −1, 1, −1)` instance
    of `british_flag_independence`: the signed sum of squared distances is
    observer-independent, and orthogonality makes its constant value vanish.
    Matches `BritishFlagTheoremOQ01OQ01.british_flag`.  (Note the orthogonality
    hypothesis is genuinely needed: for a non-rectangular parallelogram the
    observer-independent constant equals `2⟪B − A, D − A⟫ ≠ 0`.)

  ## Proof Strategy

  Translate each term through the reference point `g`:
  `p − vᵢ = (p − g) − (vᵢ − g)`.  Expanding `‖p − vᵢ‖²` with `norm_sub_sq_real`
  and summing over the (weighted) family, the cross terms collect into a single
  inner product `⟪p − g, ∑ᵢ wᵢ • (vᵢ − g)⟫` via bilinearity (`inner_weighted_sum`).
  Everything else is `Finset` sum bookkeeping.  No division is used, so the master
  identity holds for arbitrary weights (including the balanced `W = 0` case).
-/

import Mathlib

open scoped InnerProductSpace BigOperators

namespace BritishFlagSimplexOQ010102

variable {ι : Type*} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Bilinearity lemma: the weighted sum of the cross inner products
    `⟪p − g, vᵢ − g⟫` collapses into a single inner product against the weighted
    displacement `(∑ᵢ wᵢ • vᵢ) − (∑ᵢ wᵢ) • g`. -/
theorem inner_weighted_sum (s : Finset ι) (w : ι → ℝ) (v : ι → V) (p g : V) :
    ∑ i ∈ s, w i * ⟪p - g, v i - g⟫_ℝ
      = ⟪p - g, (∑ i ∈ s, w i • v i) - (∑ i ∈ s, w i) • g⟫_ℝ := by
  rw [inner_sub_right, inner_sum]
  simp only [real_inner_smul_right, inner_sub_right, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_mul]

/-- **Weighted Leibniz master identity.** For a finite family of points `v i`
    with real weights `w i`, an observer `p`, and any reference point `g`,

      ∑ᵢ wᵢ ‖p − vᵢ‖²
        = W ‖p − g‖² − 2⟪p − g, (∑ᵢ wᵢ • vᵢ) − W • g⟫ + ∑ᵢ wᵢ ‖vᵢ − g‖²

    where `W = ∑ᵢ wᵢ`.  No hypothesis on the weights is required. -/
theorem weighted_dist_sq_master (s : Finset ι) (w : ι → ℝ) (v : ι → V) (p g : V) :
    ∑ i ∈ s, w i * ‖p - v i‖ ^ 2
      = (∑ i ∈ s, w i) * ‖p - g‖ ^ 2
        - 2 * ⟪p - g, (∑ i ∈ s, w i • v i) - (∑ i ∈ s, w i) • g⟫_ℝ
        + ∑ i ∈ s, w i * ‖v i - g‖ ^ 2 := by
  have key : ∀ i ∈ s, w i * ‖p - v i‖ ^ 2
      = w i * ‖p - g‖ ^ 2 - 2 * (w i * ⟪p - g, v i - g⟫_ℝ) + w i * ‖v i - g‖ ^ 2 := by
    intro i _
    have h : p - v i = (p - g) - (v i - g) := by abel
    rw [h, norm_sub_sq_real]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, inner_weighted_sum]

/-- **Leibniz relation.** If `g` is the weighted barycenter of the family
    (`∑ᵢ wᵢ • vᵢ = (∑ᵢ wᵢ) • g`), the cross term vanishes:

      ∑ᵢ wᵢ ‖p − vᵢ‖² = W ‖p − g‖² + ∑ᵢ wᵢ ‖vᵢ − g‖².

    All dependence on the observer `p` is concentrated in `W ‖p − g‖²`. -/
theorem weighted_leibniz (s : Finset ι) (w : ι → ℝ) (v : ι → V) (p g : V)
    (hbary : ∑ i ∈ s, w i • v i = (∑ i ∈ s, w i) • g) :
    ∑ i ∈ s, w i * ‖p - v i‖ ^ 2
      = (∑ i ∈ s, w i) * ‖p - g‖ ^ 2 + ∑ i ∈ s, w i * ‖v i - g‖ ^ 2 := by
  have h := weighted_dist_sq_master s w v p g
  rw [hbary, sub_self, inner_zero_right, mul_zero, sub_zero] at h
  exact h

/-- **British Flag independence.** If the weights are *balanced* — the total
    weight vanishes (`∑ᵢ wᵢ = 0`) and the weighted centroid vanishes
    (`∑ᵢ wᵢ • vᵢ = 0`) — then the weighted sum of squared distances does not
    depend on the observer: for any two points `p` and `q`,

      ∑ᵢ wᵢ ‖p − vᵢ‖² = ∑ᵢ wᵢ ‖q − vᵢ‖².

    This is the abstract British Flag Theorem: a balanced signed combination of
    squared distances is a constant of the configuration. -/
theorem british_flag_independence (s : Finset ι) (w : ι → ℝ) (v : ι → V) (p q : V)
    (hW : ∑ i ∈ s, w i = 0) (hcent : ∑ i ∈ s, w i • v i = 0) :
    ∑ i ∈ s, w i * ‖p - v i‖ ^ 2 = ∑ i ∈ s, w i * ‖q - v i‖ ^ 2 := by
  have hval : ∀ r : V, ∑ i ∈ s, w i * ‖r - v i‖ ^ 2 = ∑ i ∈ s, w i * ‖v i‖ ^ 2 := by
    intro r
    have h := weighted_dist_sq_master s w v r 0
    simp only [hW, zero_mul, smul_zero, sub_zero, hcent, inner_zero_right, mul_zero,
      zero_add, sub_zero] at h
    exact h
  rw [hval p, hval q]

/-- **British Flag Theorem (classical four-point / rectangle form).** For a
    rectangle `A, B, C, D` — parallelogram closure `C = B + D − A` with the
    orthogonality `⟪B − A, D − A⟫ = 0` — and any observer `P`, the sums of squared
    distances to opposite vertices agree:

      ‖P − A‖² + ‖P − C‖² = ‖P − B‖² + ‖P − D‖².

    This is the balanced-weight `(1, −1, 1, −1)` instance of the general
    `british_flag_independence`: the signed sum `‖P−A‖² − ‖P−B‖² + ‖P−C‖² − ‖P−D‖²`
    is independent of `P`, and by the master identity its constant value is the
    parallelogram defect `2⟪B − A, D − A⟫`, which vanishes exactly when the sides
    are orthogonal.  Proved here directly through the same `norm_sub_sq_real`
    expansion that underlies `weighted_dist_sq_master`. -/
theorem british_flag_rectangle (P A B C D : V) (hpar : C = B + D - A)
    (hperp : ⟪B - A, D - A⟫_ℝ = 0) :
    ‖P - A‖ ^ 2 + ‖P - C‖ ^ 2 = ‖P - B‖ ^ 2 + ‖P - D‖ ^ 2 := by
  -- Parallelogram defect: the signed sum equals `2⟪B−A, D−A⟫`, independent of `P`.
  have pd : ‖P - A‖ ^ 2 + ‖P - (A + (B - A) + (D - A))‖ ^ 2
        - ‖P - (A + (B - A))‖ ^ 2 - ‖P - (A + (D - A))‖ ^ 2
      = 2 * ⟪B - A, D - A⟫_ℝ := by
    have e1 : P - (A + (B - A) + (D - A)) = (P - A) - ((B - A) + (D - A)) := by abel
    have e2 : P - (A + (B - A)) = (P - A) - (B - A) := by abel
    have e3 : P - (A + (D - A)) = (P - A) - (D - A) := by abel
    rw [e1, e2, e3, norm_sub_sq_real (P - A) ((B - A) + (D - A)),
      norm_sub_sq_real (P - A) (B - A), norm_sub_sq_real (P - A) (D - A),
      norm_add_sq_real (B - A) (D - A), inner_add_right]
    ring
  rw [hperp, mul_zero] at pd
  have hB : A + (B - A) = B := by abel
  have hD : A + (D - A) = D := by abel
  rw [hB, hD] at pd
  have hC : B + (D - A) = C := by rw [hpar]; abel
  rw [hC] at pd
  linarith

end BritishFlagSimplexOQ010102

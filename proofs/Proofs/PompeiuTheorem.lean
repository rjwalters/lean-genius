import Mathlib

/-
# Pompeiu's Theorem

## What This Proves
Let `ABC` be an equilateral triangle and `P` any point in its plane. Then the
three distances `PA`, `PB`, `PC` satisfy the triangle inequality — i.e. they can
be assembled into a (possibly degenerate) triangle. The degenerate case occurs
exactly when `P` lies on the circumcircle of `ABC`.

## Historical Context
Discovered by the Romanian mathematician Dimitrie Pompeiu (1873–1954) in 1936.
It is one of the cleanest illustrations of how a metric statement about an
equilateral triangle becomes a one-line complex-number computation.

## Approach
We work with the vertices `a, b, c` and the point `p` as complex numbers. The
purely algebraic identity
  (p - a)(b - c) + (p - b)(c - a) + (p - c)(a - b) = 0
holds for ANY four points. Taking absolute values and using that the three side
lengths `|b - c| = |c - a| = |a - b|` are equal for an equilateral triangle, the
common side length cancels and we obtain
  |p - a| ≤ |p - b| + |p - c|
together with its two cyclic permutations. That is exactly Pompeiu's inequality.
-/

namespace PompeiuTheorem

/-- The Pompeiu identity: for any four complex numbers,
`(p - a)(b - c) + (p - b)(c - a) + (p - c)(a - b) = 0`.
This holds with no hypotheses — it is a polynomial identity. -/
theorem pompeiu_identity (a b c p : ℂ) :
    (p - a) * (b - c) + (p - b) * (c - a) + (p - c) * (a - b) = 0 := by
  ring

/-- Core Pompeiu inequality (one of the three). For an equilateral triangle with
vertices `a, b, c` (all side lengths equal) and any point `p`,
`dist p a ≤ dist p b + dist p c`. -/
theorem pompeiu_dist (a b c p : ℂ)
    (h1 : ‖a - b‖ = ‖b - c‖) (h2 : ‖b - c‖ = ‖c - a‖) :
    dist p a ≤ dist p b + dist p c := by
  -- Isolate the term attached to vertex `a` in the Pompeiu identity.
  have key : (p - a) * (b - c) = -((p - b) * (c - a) + (p - c) * (a - b)) := by
    linear_combination pompeiu_identity a b c p
  -- Triangle inequality on the three complex products.
  have hnorm : ‖(p - a) * (b - c)‖ ≤ ‖(p - b) * (c - a)‖ + ‖(p - c) * (a - b)‖ := by
    rw [key, norm_neg]
    exact norm_add_le _ _
  -- Split each product norm and rewrite every side length to the common `‖b - c‖`.
  rw [norm_mul, norm_mul, norm_mul, ← h2, h1] at hnorm
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
  rcases eq_or_lt_of_le (norm_nonneg (b - c)) with hs0 | hspos
  · -- Degenerate equilateral triangle: side length is 0, so `a = b = c`.
    have hbc : b = c := by
      rw [← sub_eq_zero]; exact norm_eq_zero.mp hs0.symm
    have hab : a = b := by
      rw [← sub_eq_zero]; apply norm_eq_zero.mp; rw [h1]; exact hs0.symm
    rw [hab, hbc]
    have := norm_nonneg (p - c)
    linarith
  · -- Nondegenerate: cancel the positive common side length.
    have h : ‖p - a‖ * ‖b - c‖ ≤ (‖p - b‖ + ‖p - c‖) * ‖b - c‖ := by
      rw [add_mul]; exact hnorm
    exact le_of_mul_le_mul_right h hspos

/-- **Pompeiu's Theorem.** For an equilateral triangle `abc` and any point `p`,
the three distances `pa, pb, pc` satisfy all three triangle inequalities, hence
form a (possibly degenerate) triangle. -/
theorem pompeiu (a b c p : ℂ)
    (h1 : ‖a - b‖ = ‖b - c‖) (h2 : ‖b - c‖ = ‖c - a‖) :
    dist p a ≤ dist p b + dist p c ∧
    dist p b ≤ dist p c + dist p a ∧
    dist p c ≤ dist p a + dist p b := by
  refine ⟨pompeiu_dist a b c p h1 h2, ?_, ?_⟩
  · -- isolate vertex `b`: needs ‖b-c‖=‖c-a‖ and ‖c-a‖=‖a-b‖
    exact pompeiu_dist b c a p h2 (h1.trans h2).symm
  · -- isolate vertex `c`: needs ‖c-a‖=‖a-b‖ and ‖a-b‖=‖b-c‖
    exact pompeiu_dist c a b p (h1.trans h2).symm h1

end PompeiuTheorem

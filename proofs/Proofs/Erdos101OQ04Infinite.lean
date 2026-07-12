import Proofs.Erdos101OQ04

/-!
# Erdős #101 OQ-04 — infinitely many distinct four-point lines (companion module)

The mother file `Proofs.Erdos101OQ04` reduces the four-point-line question on the quartic
`y = x⁴ − 5x²` to the fixed ternary conic `Q(p,q,r) = p²+q²+r²+pq+qr+rp = 5`, proves that
surface is a bounded ellipsoidal shell (`ternary_conic_sq_sum_mem_Icc`), and exhibits two
explicit witnesses (the symmetric circle and one oblique rational point).  What it never
proves is that there are **infinitely many distinct** four-point lines — the qualitative
`k → ∞` backbone that the OPEN super-linear-count question refines.  Its docstrings assert
the surface "carries a continuum of solutions" only as prose.

This companion supplies the missing structural fact, rigorously and axiom-free.  It runs
along the **symmetric circular slice** `q = −p` of the surface, where `Q` collapses to the
circle `p² + r² = 5` (`conic_slice_neg_eq_circle`): for each `p ∈ (0, 1)` the abscissa set

  `symmetricAbs p = {p, −p, √(5−p²), −√(5−p²)}`

is the abscissa set of a genuine four-point line on the quartic
(`symmetricAbs_onQuartic_collinear`, via the mother file's family lemma), and the map
`p ↦ symmetricAbs p` is **injective** on `(0,1)` (`symmetricAbs_injOn`: on that interval the
abscissa `p` is recoverable as the unique element of `(0,1)`, since the other three abscissas
`−p, ±√(5−p²)` lie outside `(0,1)`).  An injective image of the infinite interval `(0,1)` is
infinite, so infinitely many *distinct* four-point-line abscissa sets occur
(`quartic_four_point_lines_infinite`).

This does **not** claim super-linear growth — only the (necessary, previously unformalized)
qualitative infinitude.  Placed in a companion module because the mother file is large
(3400+ lines); the split keeps it green.  Verified axiom-free.
-/

open scoped Real

namespace Erdos101OQ04

open Set

/-- The abscissa set of the symmetric four-point line at circle abscissa `p`: the quadruple
`(p, −p, √(5−p²), −√(5−p²))` on the circle slice `p² + r² = 5` of the surface `Q = 5`. -/
noncomputable def symmetricAbs (p : ℝ) : Finset ℝ :=
  {p, -p, Real.sqrt (5 - p ^ 2), -Real.sqrt (5 - p ^ 2)}

/-- On `p ∈ (0,1)` the companion abscissa `√(5−p²)` exceeds `2`: from `p² < 1` we get
`5 − p² > 4`, and `√` is monotone with `√4 = 2`.  This one bound separates `√(5−p²)` (and its
negative) from the interval `(0,1)`, which is what makes `symmetricAbs` injective there. -/
theorem two_lt_sqrt {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (2 : ℝ) < Real.sqrt (5 - p ^ 2) := by
  have h4 : (4 : ℝ) < 5 - p ^ 2 := by nlinarith [hp.1, hp.2]
  have hlt : Real.sqrt 4 < Real.sqrt (5 - p ^ 2) := Real.sqrt_lt_sqrt (by norm_num) h4
  rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at hlt

/-- **The symmetric abscissa map is injective on `(0,1)`.**  If `symmetricAbs a = symmetricAbs b`
with `a, b ∈ (0,1)`, then `a`, being an element of its own set, lies in `symmetricAbs b`; but on
`(0,1)` the only element of `{b, −b, √(5−b²), −√(5−b²)}` that can equal `a ∈ (0,1)` is `b`
itself (`−b < 0`, `√(5−b²) > 2 > 1`, `−√(5−b²) < 0`), so `a = b`.  Distinct circle abscissas
give distinct four-point-line abscissa sets. -/
theorem symmetricAbs_injOn : Set.InjOn symmetricAbs (Set.Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  have haa : a ∈ symmetricAbs b := by
    rw [← hab]; unfold symmetricAbs; exact Finset.mem_insert_self _ _
  unfold symmetricAbs at haa
  simp only [Finset.mem_insert, Finset.mem_singleton] at haa
  rcases haa with h | h | h | h
  · exact h
  · exfalso; nlinarith [ha.1, hb.1, h]
  · exfalso; nlinarith [ha.2, h, two_lt_sqrt hb]
  · exfalso; nlinarith [ha.1, h, Real.sqrt_nonneg (5 - b ^ 2)]

/-- **Each symmetric quadruple is a genuine four-point line on the quartic.**  For `p ∈ (0,1)`,
the four points above `p, −p, √(5−p²), −√(5−p²)` on `y = x⁴ − 5x²` are collinear (a four-point
line anchored through the first two points), by the mother file's
`quartic_quadruple_family_onQuartic_collinear` applied to the circle-slice point
`(p, −p, √(5−p²))` of the surface `Q = 5`.  The four abscissas are pairwise distinct because
`√(5−p²) > 2` while `p ∈ (0,1)`. -/
theorem symmetricAbs_onQuartic_collinear {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    collinear (p, p ^ 4 - 5 * p ^ 2) (-p, (-p) ^ 4 - 5 * (-p) ^ 2)
        (Real.sqrt (5 - p ^ 2), Real.sqrt (5 - p ^ 2) ^ 4 - 5 * Real.sqrt (5 - p ^ 2) ^ 2) ∧
      collinear (p, p ^ 4 - 5 * p ^ 2) (-p, (-p) ^ 4 - 5 * (-p) ^ 2)
        (-(p + -p + Real.sqrt (5 - p ^ 2)),
          (-(p + -p + Real.sqrt (5 - p ^ 2))) ^ 4 - 5 * (-(p + -p + Real.sqrt (5 - p ^ 2))) ^ 2) := by
  have hs0 : (0 : ℝ) ≤ 5 - p ^ 2 := by nlinarith [hp.1, hp.2]
  have hssq : Real.sqrt (5 - p ^ 2) ^ 2 = 5 - p ^ 2 := Real.sq_sqrt hs0
  have hs2 : (2 : ℝ) < Real.sqrt (5 - p ^ 2) := two_lt_sqrt hp
  have hconic : p ^ 2 + (-p) ^ 2 + Real.sqrt (5 - p ^ 2) ^ 2 + p * (-p)
      + (-p) * Real.sqrt (5 - p ^ 2) + Real.sqrt (5 - p ^ 2) * p = 5 := by
    rw [conic_slice_neg_eq_circle p (Real.sqrt (5 - p ^ 2))]; nlinarith [hssq]
  exact quartic_quadruple_family_onQuartic_collinear p (-p) (Real.sqrt (5 - p ^ 2)) hconic
    (show p ≠ -p by intro h; nlinarith [hp.1])
    (show -p ≠ Real.sqrt (5 - p ^ 2) by intro h; nlinarith [hp.1, hs2])
    (show Real.sqrt (5 - p ^ 2) ≠ p by intro h; nlinarith [hp.2, hs2])
    (show (-p) ≠ -(p + -p + Real.sqrt (5 - p ^ 2)) by intro h; nlinarith [hp.2, hs2])
    (show -(p + -p + Real.sqrt (5 - p ^ 2)) ≠ p by intro h; nlinarith [hp.1, hs2])
    (show Real.sqrt (5 - p ^ 2) ≠ -(p + -p + Real.sqrt (5 - p ^ 2)) by intro h; nlinarith [hs2])

/-- **Infinitely many distinct four-point-line abscissa sets on the quartic.**  The set of
abscissa sets `symmetricAbs p` for `p ∈ (0,1)` is infinite: it is the injective image
(`symmetricAbs_injOn`) of the infinite interval `(0,1)`.  Each member is a genuine four-point
line (`symmetricAbs_onQuartic_collinear`), so the quartic `y = x⁴ − 5x²` carries infinitely
many *distinct* four-point lines.  This is the qualitative infinitude underlying — and
necessary for — the OPEN super-linear count `fourPointLineCount`; it makes no growth-rate
claim.  Axiom-free. -/
theorem quartic_four_point_lines_infinite :
    {S : Finset ℝ | ∃ p ∈ Set.Ioo (0 : ℝ) 1, S = symmetricAbs p}.Infinite := by
  have hset : {S : Finset ℝ | ∃ p ∈ Set.Ioo (0 : ℝ) 1, S = symmetricAbs p}
      = symmetricAbs '' Set.Ioo (0 : ℝ) 1 := by
    ext S; simp only [Set.mem_image, Set.mem_setOf_eq, eq_comm]
  rw [hset]
  exact (Set.infinite_image_iff symmetricAbs_injOn).mpr (Set.Ioo_infinite (by norm_num))

end Erdos101OQ04

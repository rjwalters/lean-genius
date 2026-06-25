import Mathlib

/-!
# Ptolemy's inequality: the equality case in a general Euclidean space

## What this proves

For arbitrary points `a, b, c, d` in *any* real inner-product (Euclidean) space — no
unit-circle, no complex coordinates, no cyclic-order hypothesis — Mathlib already gives the
**Ptolemy inequality**

  `dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d`
  (`EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`).

This file pins down **exactly when equality holds**, the genuinely missing half of
"Ptolemy's theorem ⇔ cyclic quadrilateral". The answer is a clean, coordinate-free,
**axiom-free** certificate phrased through the inversion centred at `a`:

  `dist a c * dist b d = dist a b * dist c d + dist b c * dist a d`
    ↔ `Wbtw ℝ (inversion a 1 b) (inversion a 1 c) (inversion a 1 d)`,

i.e. equality holds **iff** the three inversion images `b', c', d'` are collinear with `c'`
between `b'` and `d'`.

## Why this is "equality ⇔ cyclic"

Inversion centred at `a` maps the circle through `a, b, c, d` to the *line* through
`b', c', d'`, sending "cocyclic in the order `b, c, d` (separated from `a`)" to "collinear in
the order `b', c', d'`". So `Wbtw ℝ b' c' d'` is precisely the analytic incarnation of
"`a, b, c, d` are concyclic (or collinear) with `c` opposite to `a`". We record the weaker,
purely-Mathlib certificate `Collinear ℝ {b', c', d'}` as a corollary.

## How the proof works

Mathlib's proof of the inequality applies the triangle inequality to the inversion images and
uses `dist_inversion_inversion : dist (inversion a 1 x) (inversion a 1 y)
= 1² / (dist x a * dist y a) * dist x y`. Equality in Ptolemy is therefore equality in that one
triangle inequality, which the strict-convexity lemma `dist_add_dist_eq_iff` characterises as
`Wbtw`. Real inner-product spaces are strictly convex (`InnerProductSpace.toUniformConvexSpace`
→ `UniformConvexSpace.toStrictConvexSpace`), so no extra hypotheses are needed. The remaining
work is the elementary algebra of clearing the three positive denominators.

## Relation to the parent entries

The parent leaf `ptolemys-theorem-oq-01-oq-01` proves the converse for four points **on the
unit circle**, but its angular sign-analysis step is sealed behind an `axiom`
(`positive_ratio_implies_cyclic_order`). The result here is **fully general** (any Euclidean
space, any four points) and **0-axiom / 0-sorry**, trading the brittle trigonometric ordering
for the inversion/betweenness certificate.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open EuclideanGeometry

namespace Ptolemy.EqualityCase

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ## The scalar algebra behind clearing the inversion denominators -/

/-- The arithmetic heart of the equivalence: with three positive "radii" `p, q, r`, the
sum-of-inverted-distances equality is equivalent to the Ptolemy product equality. Here
`p = dist a b`, `q = dist a c`, `r = dist a d` and `u = dist b c`, `v = dist c d`,
`w = dist b d`, and the `1 ^ 2` factors are the inversion radius squared. -/
private theorem key_equiv {p q r u v w : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    (1 ^ 2 / (p * q) * u + 1 ^ 2 / (q * r) * v = 1 ^ 2 / (p * r) * w)
      ↔ (q * w = p * v + u * r) := by
  have hp' : p ≠ 0 := hp.ne'
  have hq' : q ≠ 0 := hq.ne'
  have hr' : r ≠ 0 := hr.ne'
  have hpq : p * q ≠ 0 := mul_ne_zero hp' hq'
  have hqr : q * r ≠ 0 := mul_ne_zero hq' hr'
  have hpr : p * r ≠ 0 := mul_ne_zero hp' hr'
  have hpqr : p * q * r ≠ 0 := mul_ne_zero hpq hr'
  -- normalise `1 ^ 2 / x * y` into `y / x`
  simp only [one_pow, one_div_mul_eq_div]
  rw [div_add_div _ _ hpq hqr, div_eq_div_iff (mul_ne_zero hpq hqr) hpr]
  constructor
  · -- the cleared product equality forces the Ptolemy relation
    intro h
    have hz : p * q * r * (q * w - (p * v + u * r)) = 0 := by linear_combination -h
    have := (mul_eq_zero.mp hz).resolve_left hpqr
    linarith
  · -- conversely the Ptolemy relation gives the cleared product equality
    intro h
    linear_combination (-(p * q * r)) * h

/-! ## The equality characterisation -/

/-- **Ptolemy's equality case.** For points `a, b, c, d` in a real inner-product (Euclidean)
space with `b, c, d ≠ a`, Ptolemy's inequality
`dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d` becomes an **equality** if and
only if the inversion images of `b, c, d` about `a` are collinear with the image of `c` between
those of `b` and `d`:

`dist a c * dist b d = dist a b * dist c d + dist b c * dist a d`
  ↔ `Wbtw ℝ (inversion a 1 b) (inversion a 1 c) (inversion a 1 d)`.

This is the precise, coordinate-free, axiom-free form of "Ptolemy's equality ⇔ cyclic
quadrilateral": inversion at `a` carries the circumcircle through `a, b, c, d` to the line
through the three images, so the betweenness on the right says exactly that `a, b, c, d` are
concyclic (or collinear) with `c` separated from `a`. -/
theorem ptolemy_eq_iff_wbtw_inversion (a b c d : P)
    (hb : b ≠ a) (hc : c ≠ a) (hd : d ≠ a) :
    dist a c * dist b d = dist a b * dist c d + dist b c * dist a d
      ↔ Wbtw ℝ (inversion a 1 b) (inversion a 1 c) (inversion a 1 d) := by
  have hp : (0 : ℝ) < dist a b := dist_pos.mpr hb.symm
  have hq : (0 : ℝ) < dist a c := dist_pos.mpr hc.symm
  have hr : (0 : ℝ) < dist a d := dist_pos.mpr hd.symm
  rw [← dist_add_dist_eq_iff, dist_inversion_inversion hb hc 1,
    dist_inversion_inversion hc hd 1, dist_inversion_inversion hb hd 1,
    dist_comm b a, dist_comm c a, dist_comm d a]
  exact (key_equiv hp hq hr).symm

/-- **Strict Ptolemy inequality off the equality locus.** The inequality is *strict* exactly
when the inversion images fail to be in betweenness order. -/
theorem ptolemy_strict_iff_not_wbtw (a b c d : P)
    (hb : b ≠ a) (hc : c ≠ a) (hd : d ≠ a) :
    dist a c * dist b d < dist a b * dist c d + dist b c * dist a d
      ↔ ¬ Wbtw ℝ (inversion a 1 b) (inversion a 1 c) (inversion a 1 d) := by
  have hle := mul_dist_le_mul_dist_add_mul_dist a b c d
  rw [← ptolemy_eq_iff_wbtw_inversion a b c d hb hc hd]
  constructor
  · intro hlt heq; exact (ne_of_lt hlt) heq
  · intro hne; exact lt_of_le_of_ne hle hne

/-- **Concyclicity certificate.** Ptolemy's equality forces the three inversion images about
`a` to be collinear — the line that the circle through `a, b, c, d` becomes under inversion.
This is the purely-Mathlib (order-free) shadow of "the quadrilateral is cyclic". -/
theorem ptolemy_eq_imp_collinear_inversion (a b c d : P)
    (hb : b ≠ a) (hc : c ≠ a) (hd : d ≠ a)
    (h : dist a c * dist b d = dist a b * dist c d + dist b c * dist a d) :
    Collinear ℝ ({inversion a 1 b, inversion a 1 c, inversion a 1 d} : Set P) :=
  ((ptolemy_eq_iff_wbtw_inversion a b c d hb hc hd).mp h).collinear

/-! ## Sanity checks -/

/-- The degenerate case `c = b` (still `≠ a`) is on the equality locus: both sides of Ptolemy
read `dist a b * dist b d`, and indeed the inversion images satisfy `Wbtw` with a repeated
point. -/
example (a b d : P) (hb : b ≠ a) (hd : d ≠ a) :
    Wbtw ℝ (inversion a 1 b) (inversion a 1 b) (inversion a 1 d) := by
  refine (ptolemy_eq_iff_wbtw_inversion a b b d hb hb hd).mp ?_
  simp [dist_self]

end Ptolemy.EqualityCase

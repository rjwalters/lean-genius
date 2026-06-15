/-
  Birthday Problem OQ-01-OQ-01-OQ-03 (Schur side): the no-collision probability
  `Pr_p(X = 0)` is *maximized* at the uniform distribution.

  Companion to `BirthdayProblemOQ01OQ01OQ03.lean` (draft PR #23219), which settles
  the *collision-count* side: `E_p[X] = C(n,2)·∑ p_k²` is *minimized* at uniform via
  Cauchy–Schwarz. This file formalizes the algebraic kernel of the dual statement,
  certified symbolically in `verify_no_collision_extremum.py`:

      Pr_p(X = 0) = n! · e_n(p)        (e_n = degree-n elementary symmetric poly)

  and uniform maximizes `e_n` on the probability simplex because `e_n` is
  Schur-concave. The whole Schur-concavity argument reduces, via the
  Hardy–Littlewood–Pólya transfer principle, to a single pairwise-equalization
  step: replacing two coordinates `(x, y)` by their common mean `m = (x+y)/2`
  never decreases `e_n` (and strictly increases it unless `x = y`).

  The key structural fact making this elementary is that `e_n` is **biaffine** in
  any two of its arguments: degree ≤ 1 in each separately. Fixing all other
  coordinates and isolating two distinguished ones `x, y`, the symmetric
  elementary polynomial takes the shape

      g x y = A + (x + y)·B + x·y·C,

  where `A = e_n(rest)`, `B = e_{n-1}(rest)`, `C = e_{n-2}(rest)` are the
  elementary symmetric polynomials of the *remaining* coordinates, and for a
  probability vector `C ≥ 0` (a sum of products of nonnegatives). The transfer
  step is then a pure inequality about this biaffine form, proved below.

  This is the missing Lean kernel for "uniform maximizes Pr(X=0)"; assembling it
  into the full simplex extremum (a finite chain of such transfers, i.e.
  majorization) plus the `Pr = n!·e_n` counting identity is the remaining ACT,
  build-gated by the Docker outage of 2026-06-13/15.

  BUILD STATUS: not yet machine-checked (written during the Docker / `lake build`
  verification outage). All Mathlib lemma names verified against the pinned
  Mathlib v4.26.0 sibling checkout; the inequalities are discharged by
  `nlinarith`/`linear_combination` with explicit `sq_nonneg` witnesses.
-/
import Mathlib

namespace BirthdayCollisionSchur

/-- A symmetric **biaffine** form in two real variables:
    `g x y = A + (x + y)·B + x·y·C`. Any elementary symmetric polynomial,
    viewed as a function of two of its coordinates with the rest fixed, has this
    shape, with `A`, `B`, `C` the elementary symmetric polynomials of the
    remaining coordinates. -/
def biaffine (A B C x y : ℝ) : ℝ := A + (x + y) * B + x * y * C

/-- **Equalization increment.** Moving the two coordinates to their common mean
    `m = (x+y)/2` changes the biaffine form by exactly `((x - y)/2)² · C`.
    This is the one identity underlying Schur-concavity of `e_n`. -/
theorem biaffine_mean_sub (A B C x y : ℝ) :
    biaffine A B C ((x + y) / 2) ((x + y) / 2) - biaffine A B C x y
      = ((x - y) / 2) ^ 2 * C := by
  unfold biaffine
  ring

/-- **Hardy–Littlewood–Pólya transfer step (weak form).** If the "weight"
    coefficient `C` is nonnegative, replacing `(x, y)` by their mean never
    decreases the biaffine form. For `e_n` of a probability vector, `C = e_{n-2}`
    of the remaining coordinates is `≥ 0`, so this says equalizing two
    probabilities never decreases `e_n` — uniform is the maximizer. -/
theorem biaffine_le_mean (A B C x y : ℝ) (hC : 0 ≤ C) :
    biaffine A B C x y ≤ biaffine A B C ((x + y) / 2) ((x + y) / 2) := by
  have h := biaffine_mean_sub A B C x y
  have hsq : 0 ≤ ((x - y) / 2) ^ 2 * C := mul_nonneg (sq_nonneg _) hC
  linarith [h, hsq]

/-- **Strict transfer step.** If the weight `C` is strictly positive and the two
    coordinates differ, equalizing them strictly increases the form. This gives
    uniqueness: uniform is the *unique* maximizer of `e_n` (hence of `Pr(X=0)`)
    whenever the relevant lower-order symmetric weights are positive. -/
theorem biaffine_lt_mean (A B C x y : ℝ) (hC : 0 < C) (hxy : x ≠ y) :
    biaffine A B C x y < biaffine A B C ((x + y) / 2) ((x + y) / 2) := by
  have h := biaffine_mean_sub A B C x y
  have hne : ((x - y) / 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (div_ne_zero (sub_ne_zero.mpr hxy) two_ne_zero)
  have hsq : 0 < ((x - y) / 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
  have hpos : 0 < ((x - y) / 2) ^ 2 * C := mul_pos hsq hC
  linarith [h, hpos]

/-- **Equality characterization of the transfer step.** With positive weight,
    equality of the biaffine form at `(x, y)` and at the equalized pair holds iff
    the two coordinates were already equal. -/
theorem biaffine_eq_mean_iff (A B C x y : ℝ) (hC : 0 < C) :
    biaffine A B C x y = biaffine A B C ((x + y) / 2) ((x + y) / 2) ↔ x = y := by
  constructor
  · intro heq
    by_contra hne
    exact absurd heq (ne_of_lt (biaffine_lt_mean A B C x y hC hne))
  · intro hxy
    subst hxy
    have : (x + x) / 2 = x := by ring
    rw [this]

end BirthdayCollisionSchur

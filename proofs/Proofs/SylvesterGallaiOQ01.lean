/-
# Sylvester–Gallai theorem (ordinary line existence) — research scaffold

**Problem (`sylvester-gallai-theorem-oq-01`):** every finite set of points in the
real plane that is *not* collinear determines an *ordinary line* — a line passing
through exactly two of the points.

This file sets up Kelly's metric proof, which is the right route for Lean: it needs
only the signed-area (2D cross-product) functional, distance, and the affine
`Collinear` predicate, all available in Mathlib, and avoids the projective-duality
and Euler-characteristic machinery of Melchior's proof.

## Status (research, in progress)

The reusable *lever* is the signed-area functional `area2 a b c` — twice the signed
area of triangle `abc`, equal to the determinant `det[b-a, c-a]`. The perpendicular
distance from `c` to the line through `a b` is `|area2 a b c| / dist a b`.

Proved here (self-contained, no `sorry`):
* `area2` and its full permutation/degeneracy algebra (`ring`-closed);
* `distToLine` and its non-negativity.

Open kernel (left as `sorry`, decomposed for Aristotle / future sessions):
* `collinear_iff_area2_eq_zero` — the bridge from the affine `Collinear` predicate to
  the vanishing of the signed area (HARD, known; clean Aristotle target);
* `area2_strict_decrease` — Kelly's geometric inequality (the heart of the proof);
* `sylvester_gallai` — the assembled minimization argument.

This is a genuine formalization contribution: Sylvester–Gallai is **not** in Mathlib
(no `SylvesterGallai` / `ordinaryLine` / de Bruijn–Erdős declarations exist).
-/
import Mathlib

namespace SylvesterGallaiOQ01

/-- Points of the real Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-- Twice the signed area of triangle `a b c`: the 2D cross product of `b - a` and
`c - a`, i.e. the determinant `det[b-a, c-a]`. This is the lever for Kelly's proof —
its absolute value over the base length is the perpendicular distance to the line. -/
noncomputable def area2 (a b c : Pt) : ℝ :=
  (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0)

/-! ### Algebra of the signed area (degeneracies and permutations) -/

@[simp] lemma area2_self_left (a c : Pt) : area2 a a c = 0 := by
  unfold area2; ring

@[simp] lemma area2_self_mid (a b : Pt) : area2 a b a = 0 := by
  unfold area2; ring

@[simp] lemma area2_self_right (a b : Pt) : area2 a b b = 0 := by
  unfold area2; ring

/-- Swapping the last two vertices negates the signed area. -/
lemma area2_swap_right (a b c : Pt) : area2 a c b = - area2 a b c := by
  unfold area2; ring

/-- Swapping the first two vertices negates the signed area. -/
lemma area2_swap_left (a b c : Pt) : area2 b a c = - area2 a b c := by
  unfold area2; ring

/-- The signed area is invariant under a cyclic rotation of the vertices. -/
lemma area2_cyclic (a b c : Pt) : area2 b c a = area2 a b c := by
  unfold area2; ring

/-- Translation invariance: shifting all three vertices by a common vector `t`
leaves the signed area unchanged. -/
lemma area2_vadd (t a b c : Pt) :
    area2 (t + a) (t + b) (t + c) = area2 a b c := by
  unfold area2
  simp only [PiLp.add_apply]
  ring

/-! ### Perpendicular distance to a line -/

/-- The perpendicular distance from `c` to the line through `a` and `b`,
expressed via the signed area: `|area2 a b c| / dist a b`. When `a = b` this is `0`
(degenerate base), so it is only meaningful for `a ≠ b`. -/
noncomputable def distToLine (a b c : Pt) : ℝ := |area2 a b c| / dist a b

lemma distToLine_nonneg (a b c : Pt) : 0 ≤ distToLine a b c :=
  div_nonneg (abs_nonneg _) dist_nonneg

@[simp] lemma distToLine_self_left (a c : Pt) : distToLine a a c = 0 := by
  simp [distToLine]

/-! ### The collinearity bridge (open) -/

/-- **Bridge (open).** Three points are collinear exactly when the signed area
vanishes. This connects the affine `Collinear` predicate used in the statement to
the concrete `area2` functional used in the proof.

Forward direction: `collinear_iff_of_mem` gives a common direction `v` with
`b = r_b • v +ᵥ a`, `c = r_c • v +ᵥ a`, whence each coordinate difference is a scalar
multiple of `v` and the determinant collapses to `0`. Reverse: a vanishing
determinant exhibits `b - a` and `c - a` as linearly dependent, giving the direction.
Clean `HARD` Aristotle target once the coordinate-evaluation bookkeeping is fixed. -/
theorem collinear_iff_area2_eq_zero (a b c : Pt) :
    Collinear ℝ ({a, b, c} : Set Pt) ↔ area2 a b c = 0 := by
  sorry

/-- `distToLine a b c = 0` iff `c` lies on the line through `a b` (for `a ≠ b`). -/
theorem distToLine_eq_zero_iff {a b c : Pt} (hab : a ≠ b) :
    distToLine a b c = 0 ↔ Collinear ℝ ({a, b, c} : Set Pt) := by
  rw [distToLine, div_eq_zero_iff, abs_eq_zero, collinear_iff_area2_eq_zero]
  have : dist a b ≠ 0 := by
    simpa [dist_eq_zero] using hab
  simp [this]

/-! ### Kelly's geometric inequality (open kernel) -/

/-- **Kelly's strict-decrease step (open).** Suppose `P₀` is off the line `ℓ₀`
through `a₀ b₀`, and `ℓ₀` carries a third collinear point. Taking the foot `F` of the
perpendicular from `P₀` and the two collinear points `B` (nearer `F`), `C` (farther,
same side), one gets a strictly smaller perpendicular distance
`distToLine P₀ C B < distToLine a₀ b₀ P₀`.

This is the geometric heart of Kelly's proof; the ratio of nested similar triangles
`CB / CP₀ < 1` drives the strict inequality. Left as a `sorry`: this is the genuinely
hard, creative part and is **not** a known Mathlib result. -/
theorem area2_strict_decrease
    {a₀ b₀ P₀ B C : Pt} (hab : a₀ ≠ b₀)
    (hP : ¬ Collinear ℝ ({a₀, b₀, P₀} : Set Pt))
    (hB : Collinear ℝ ({a₀, b₀, B} : Set Pt))
    (hC : Collinear ℝ ({a₀, b₀, C} : Set Pt))
    (hBC : B ≠ C) (hPC : P₀ ≠ C)
    (hside : True /- B, C strictly on the same side of the foot F, B nearer -/) :
    distToLine P₀ C B < distToLine a₀ b₀ P₀ := by
  sorry

/-! ### Main theorem (open assembly) -/

/-- **Sylvester–Gallai (open).** Any finite, non-collinear set of points in the plane
admits an *ordinary line*: two distinct points `a, b ∈ S` such that every point of `S`
collinear with `a` and `b` is equal to `a` or `b`.

Proof strategy (Kelly): minimize `distToLine a b P` over the finite, nonempty set of
triples `(a, b, P)` with `a, b, P ∈ S`, `a ≠ b`, and `P` off the line `ab`
(nonempty since `S` is non-collinear). If the minimizing line carried a third point,
`area2_strict_decrease` would produce a strictly smaller member — contradiction. -/
theorem sylvester_gallai {S : Finset Pt}
    (hS : ¬ Collinear ℝ (↑S : Set Pt)) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      ∀ c ∈ S, Collinear ℝ ({a, b, c} : Set Pt) → c = a ∨ c = b := by
  sorry

end SylvesterGallaiOQ01

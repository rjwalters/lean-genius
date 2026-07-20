/-
# Erdős Problem #507 (Heilbronn's Triangle Problem) — Foundational Lemmas

Axiom-free foundational scaffolding for the objects defined in
`Proofs/Erdos507Problem.lean`:

    triangleArea p q r = |p₁(q₂−r₂) + q₁(r₂−p₂) + r₁(p₂−q₂)| / 2,
    IsInUnitDisk P     = ∀ p ∈ P, p₁² + p₂² ≤ 1,

the shoelace area of a triangle in `ℝ²` and the unit-disk configuration
predicate underlying Heilbronn's function `heilbronn n`.

Heilbronn's triangle problem — estimating `α(n)`, the largest value such that
some `n`-point set in the unit disk keeps every triangle area `≥ α(n)` — is
**open** (the exponent `β` with `α(n) = n^{−β+o(1)}` satisfies only
`7/6 ≤ β ≤ 2`).  The deep bounds (Komlós–Pintz–Szemerédi, Cohen–Pohoata–
Zakharov) are untouched here; this file establishes the elementary geometry
of the atomic building block `triangleArea`:

* nonnegativity;
* full permutation behaviour (transpositions negate the signed area, cyclic
  rotations preserve it — so `triangleArea` is symmetric under all six
  orderings);
* the three degenerate (repeated-vertex) cases vanish;
* `triangleArea = 0 ↔ the three points are collinear` (signed area zero);
* an explicit value `triangleArea (0,0) (1,0) (0,1) = 1/2`;
* unit-disk facts: coordinate bounds `|p₁|, |p₂| ≤ 1`, and the uniform area
  bound `triangleArea p q r ≤ 3` for points in the unit disk (so
  `heilbronn n` is bounded — its `sSup` is over a bounded set).

All results are `0`-axiom / `0`-sorry.

Reference: <https://erdosproblems.com/507>
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Proofs.Erdos507Problem

namespace Erdos507WIP01

/-! ## `triangleArea`: nonnegativity -/

/-- The triangle area is nonnegative (it is an absolute value over `2`). -/
theorem triangleArea_nonneg (p q r : ℝ × ℝ) : 0 ≤ triangleArea p q r := by
  unfold triangleArea; positivity

/-! ## Permutation behaviour

The *signed* area (the bracket before the absolute value) is an alternating
function of the three vertices: transpositions negate it, cyclic rotations
fix it.  After the absolute value, `triangleArea` is therefore invariant under
every permutation of its arguments. -/

/-- Swapping the first two vertices leaves the area unchanged. -/
theorem triangleArea_swap_left (p q r : ℝ × ℝ) :
    triangleArea q p r = triangleArea p q r := by
  unfold triangleArea
  rw [show q.1 * (p.2 - r.2) + p.1 * (r.2 - q.2) + r.1 * (q.2 - p.2)
        = -(p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)) from by ring,
    abs_neg]

/-- Swapping the last two vertices leaves the area unchanged. -/
theorem triangleArea_swap_right (p q r : ℝ × ℝ) :
    triangleArea p r q = triangleArea p q r := by
  unfold triangleArea
  rw [show p.1 * (r.2 - q.2) + r.1 * (q.2 - p.2) + q.1 * (p.2 - r.2)
        = -(p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)) from by ring,
    abs_neg]

/-- Cyclic rotation of the vertices leaves the area unchanged. -/
theorem triangleArea_cyclic (p q r : ℝ × ℝ) :
    triangleArea q r p = triangleArea p q r := by
  unfold triangleArea
  rw [show q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2) + p.1 * (q.2 - r.2)
        = p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2) from by ring]

/-! ## Degenerate (repeated-vertex) triangles vanish -/

/-- A repeated first/second vertex gives zero area. -/
theorem triangleArea_self_left (p r : ℝ × ℝ) : triangleArea p p r = 0 := by
  unfold triangleArea
  rw [show p.1 * (p.2 - r.2) + p.1 * (r.2 - p.2) + r.1 * (p.2 - p.2) = 0 from by ring,
    abs_zero, zero_div]

/-- A repeated second/third vertex gives zero area. -/
theorem triangleArea_self_mid (p q : ℝ × ℝ) : triangleArea p q q = 0 := by
  unfold triangleArea
  rw [show p.1 * (q.2 - q.2) + q.1 * (q.2 - p.2) + q.1 * (p.2 - q.2) = 0 from by ring,
    abs_zero, zero_div]

/-- A repeated first/third vertex gives zero area. -/
theorem triangleArea_self_outer (p q : ℝ × ℝ) : triangleArea p q p = 0 := by
  unfold triangleArea
  rw [show p.1 * (q.2 - p.2) + q.1 * (p.2 - p.2) + p.1 * (p.2 - q.2) = 0 from by ring,
    abs_zero, zero_div]

/-! ## Collinearity ⟺ zero area -/

/-- `triangleArea p q r = 0` exactly when the signed area vanishes, i.e. the
    three points are collinear. -/
theorem triangleArea_eq_zero_iff (p q r : ℝ × ℝ) :
    triangleArea p q r = 0 ↔
      p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2) = 0 := by
  unfold triangleArea
  rw [div_eq_zero_iff]
  simp [abs_eq_zero]

/-! ## An explicit value -/

/-- The unit right triangle `(0,0), (1,0), (0,1)` has area `1/2`. -/
theorem triangleArea_unit :
    triangleArea ((0 : ℝ), (0 : ℝ)) (1, 0) (0, 1) = 1 / 2 := by
  unfold triangleArea; norm_num

/-! ## The unit-disk predicate -/

/-- The empty configuration lies in the unit disk. -/
theorem isInUnitDisk_empty : IsInUnitDisk (∅ : Finset (ℝ × ℝ)) := by
  intro p hp; exact absurd hp (Finset.notMem_empty p)

/-- A subset of a unit-disk configuration is a unit-disk configuration. -/
theorem IsInUnitDisk.subset {P Q : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    (hQ : Q ⊆ P) : IsInUnitDisk Q := fun p hp => h p (hQ hp)

/-- In the unit disk, the first coordinate is bounded: `|p₁| ≤ 1`. -/
theorem unitDisk_abs_fst_le {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {p : ℝ × ℝ} (hp : p ∈ P) : |p.1| ≤ 1 := by
  have hdisk : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := h p hp
  have hsq : p.1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.2]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (p.1 - 1), sq_nonneg (p.1 + 1)]

/-- In the unit disk, the second coordinate is bounded: `|p₂| ≤ 1`. -/
theorem unitDisk_abs_snd_le {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {p : ℝ × ℝ} (hp : p ∈ P) : |p.2| ≤ 1 := by
  have hdisk : p.1 ^ 2 + p.2 ^ 2 ≤ 1 := h p hp
  have hsq : p.2 ^ 2 ≤ 1 := by nlinarith [sq_nonneg p.1]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (p.2 - 1), sq_nonneg (p.2 + 1)]

/-- **Uniform area bound.** Any triangle with all three vertices in the unit
    disk has area at most `3`.  In particular the `sSup` defining `heilbronn n`
    is taken over a bounded set of reals, so `heilbronn n` is finite. -/
theorem triangleArea_le_three {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {p q r : ℝ × ℝ} (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P) :
    triangleArea p q r ≤ 3 := by
  have bp1 := unitDisk_abs_fst_le h hp
  have bp2 := unitDisk_abs_snd_le h hp
  have bq1 := unitDisk_abs_fst_le h hq
  have bq2 := unitDisk_abs_snd_le h hq
  have br1 := unitDisk_abs_fst_le h hr
  have br2 := unitDisk_abs_snd_le h hr
  -- each of the three summands has absolute value at most `2`
  have term : ∀ a b c : ℝ, |a| ≤ 1 → |b| ≤ 1 → |c| ≤ 1 → |a * (b - c)| ≤ 2 := by
    intro a b c ha hb hc
    rw [abs_mul]
    have hbc : |b - c| ≤ 2 := by
      rw [abs_le] at hb hc ⊢
      constructor <;> linarith [hb.1, hb.2, hc.1, hc.2]
    calc |a| * |b - c| ≤ 1 * 2 :=
          mul_le_mul ha hbc (abs_nonneg _) (by norm_num)
      _ = 2 := by norm_num
  have t1 := term p.1 q.2 r.2 bp1 bq2 br2
  have t2 := term q.1 r.2 p.2 bq1 br2 bp2
  have t3 := term r.1 p.2 q.2 br1 bp2 bq2
  unfold triangleArea
  have hE : |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)| ≤ 6 := by
    calc |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)|
        ≤ |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2)| + |r.1 * (p.2 - q.2)| :=
          abs_add_le _ _
      _ ≤ |p.1 * (q.2 - r.2)| + |q.1 * (r.2 - p.2)| + |r.1 * (p.2 - q.2)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ 6 := by linarith [t1, t2, t3]
  linarith [hE]

end Erdos507WIP01

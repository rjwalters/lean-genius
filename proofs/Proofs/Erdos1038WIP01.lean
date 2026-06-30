/-
  Erdős Problem #1038 — WIP-01: the extremal quadratic x² − 1 realizes the supremum 2√2

  The gallery stub `Erdos1038Problem` sets up the sublevel-set problem — for monic
  real-rooted polynomials with roots in `[-1,1]`, study `|{x : |f(x)| < 1}|` — but
  proves no theorems (the extremal facts are only sketched in prose).  This file
  formalizes the concrete extremal computation noted there:

      the quadratic `x² − 1 = (x−1)(x+1)` is admissible, and its sublevel set
      `{x : |x² − 1| < 1} = (−√2, √2) ∖ {0}` has Lebesgue measure `2√2`,

  the supremum value (Erdős–Herzog–Piranian 1958, confirmed by Tao 2025).  The
  full supremum *bound* over all admissible `f` needs logarithmic potential theory
  beyond Mathlib and is not attempted; this is the matching lower witness.

  * `quadratic_admissible`        — `x² − 1` is monic with both roots in `[-1,1]`.
  * `mem_sublevelSet_quadratic`   — `x ∈ sublevelSet (x²−1) ↔ 0 < x² ∧ x² < 2`.
  * `sublevelSet_quadratic`       — `= Set.Ioo (−√2) √2 ∖ {0}`.
  * `sublevelMeasure_quadratic`   — `= ENNReal.ofReal (2√2)`.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Erdős–Herzog–Piranian (1958); Tao, *Sublevel Sets of Logarithmic
  Potentials* (2025); https://erdosproblems.com/1038.
-/

import Mathlib

open scoped Real ENNReal
open MeasureTheory Polynomial Set

namespace Erdos1038WIP01

/-- A monic polynomial with all roots real and in `[-1,1]` (re-declared to be
    self-contained against the stub). -/
def MonicRealRootedIn01 (f : Polynomial ℝ) : Prop :=
  f.Monic ∧ (∀ r ∈ f.roots, r ∈ Set.Icc (-1 : ℝ) 1)

/-- The sublevel set `{x : |f(x)| < 1}`. -/
def sublevelSet (f : Polynomial ℝ) : Set ℝ := {x | |f.eval x| < 1}

/-- Lebesgue measure of the sublevel set. -/
noncomputable def sublevelMeasure (f : Polynomial ℝ) : ℝ≥0∞ := volume (sublevelSet f)

/-- The extremal quadratic `x² − 1`. -/
noncomputable def q : Polynomial ℝ := X ^ 2 - C 1

@[simp] theorem eval_q (x : ℝ) : q.eval x = x ^ 2 - 1 := by
  simp [q]

/-- **The quadratic `x² − 1` is admissible**: monic with both roots in `[-1,1]`. -/
theorem quadratic_admissible : MonicRealRootedIn01 q := by
  constructor
  · -- monic
    simpa [q] using monic_X_pow_sub_C (1 : ℝ) (n := 2) (by norm_num)
  · -- roots in [-1, 1]
    intro r hr
    rw [Polynomial.mem_roots'] at hr
    have hroot : r ^ 2 - 1 = 0 := by simpa using hr.2
    rw [Set.mem_Icc]
    constructor <;> nlinarith [hroot]

/-- **Membership in the sublevel set of `x² − 1`** in elementary form. -/
theorem mem_sublevelSet_quadratic (x : ℝ) :
    x ∈ sublevelSet q ↔ 0 < x ^ 2 ∧ x ^ 2 < 2 := by
  simp only [sublevelSet, Set.mem_setOf_eq, eval_q, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **The sublevel set of `x² − 1` is `(−√2, √2) ∖ {0}`.** -/
theorem sublevelSet_quadratic :
    sublevelSet q = Set.Ioo (-Real.sqrt 2) (Real.sqrt 2) \ {0} := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  ext x
  rw [mem_sublevelSet_quadratic, Set.mem_diff, Set.mem_Ioo, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h2⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · nlinarith [hs, hspos, sq_nonneg (x + Real.sqrt 2)]
    · nlinarith [hs, hspos, sq_nonneg (x - Real.sqrt 2)]
    · intro hx; rw [hx] at h0; simpa using h0
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, ?_⟩
    · have : x ≠ 0 := h3
      positivity
    · nlinarith [hs, hspos, h1, h2]

/-- **The extremal quadratic realizes the supremum `2√2`.**  The sublevel set
    `(−√2, √2) ∖ {0}` has Lebesgue measure `2√2` (removing the single point `0`
    does not change the measure). -/
theorem sublevelMeasure_quadratic :
    sublevelMeasure q = ENNReal.ofReal (2 * Real.sqrt 2) := by
  unfold sublevelMeasure
  rw [sublevelSet_quadratic, measure_diff_null (by simp), Real.volume_Ioo]
  congr 1
  ring

end Erdos1038WIP01

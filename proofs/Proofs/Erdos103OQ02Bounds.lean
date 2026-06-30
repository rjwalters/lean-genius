/-
Erdős Problem #103 — Open Question 02, supplementary: bounds on `minDiameter`

## Context

The parent file `Erdos103Problem.lean` defines

    minDiameter (n) := ⨅ P : {P : PointConfig n // IsValidConfig n P}, diameter n P.val

and `IsOptimal n P := IsValidConfig n P ∧ diameter n P = minDiameter n`. The whole
formalization (and the OQ-02 audit in `Erdos103OQ02.lean`) revolves around this real
number `minDiameter n`, yet nothing pins it down: a priori it could be the junk value
of an infimum over an empty or unbounded-below set.

This file establishes that `minDiameter n` is a genuine, non-vacuous quantity:

1. `validConfig_exists` — for every `n` there is a valid configuration (the points
   on a line at unit spacing), so the infimum is taken over a **nonempty** index.
2. `diameter_nonneg` — `diameter n P ≥ 0` for every configuration, so the value set
   is **bounded below** and `minDiameter` is a true infimum (not a junk `sInf`).
3. `minDiameter_le` — the explicit line configuration gives `minDiameter n ≤ n - 1`
   (for `n ≥ 1`).
4. `one_le_minDiameter` — every valid configuration on `n ≥ 2` points has two points
   at distance `≥ 1`, so `diameter ≥ 1`, hence `minDiameter n ≥ 1`.

Together (`minDiameter_mem_Icc`): for `n ≥ 2`,

    1 ≤ minDiameter n ≤ n - 1.

This is the natural sandwich on the object whose *attainment* (existence of an optimal
configuration) is the standing hypothesis of the OQ-02 audit's Part 7 and of the
parent's `related_to_problem_99`. The bounds are the prerequisites for any future
compactness proof of that attainment.

## Axioms / Sorries
None. All results are machine-checked from Mathlib + the parent file only.
-/

import Mathlib
import Proofs.Erdos103Problem

open Erdos103

namespace Erdos103OQ02Bounds

-- ============================================================
-- PART 1: pointDist basics on the x-axis
-- ============================================================

/-- Distance between two points on the x-axis is the absolute difference of the
    abscissae. -/
theorem pointDist_xaxis (a b : ℝ) :
    pointDist (a, 0) (b, 0) = |a - b| := by
  unfold pointDist
  have e1 : ((a, 0) : ℝ × ℝ).1 - ((b, 0) : ℝ × ℝ).1 = a - b := rfl
  have e2 : ((a, 0) : ℝ × ℝ).2 - ((b, 0) : ℝ × ℝ).2 = 0 := by norm_num
  rw [e1, e2]
  rw [show (a - b) ^ 2 + (0 : ℝ) ^ 2 = (a - b) ^ 2 by ring, Real.sqrt_sq_eq_abs]

/-- `pointDist` is always nonnegative (it is a square root). -/
theorem pointDist_nonneg (p q : ℝ × ℝ) : 0 ≤ pointDist p q := by
  unfold pointDist; exact Real.sqrt_nonneg _

-- ============================================================
-- PART 2: diameter is nonnegative (so minDiameter is bounded below)
-- ============================================================

/-- The inner supremum defining the diameter ranges over a finite (hence bounded)
    family, so it is `BddAbove`. -/
theorem diameter_inner_bddAbove {n : ℕ} (P : PointConfig n) (i : Fin n) :
    BddAbove (Set.range (fun j : Fin n => pointDist (P i) (P j))) :=
  Set.Finite.bddAbove (Set.finite_range _)

/-- The outer supremum defining the diameter ranges over a finite family. -/
theorem diameter_outer_bddAbove {n : ℕ} (P : PointConfig n) :
    BddAbove (Set.range (fun i : Fin n => ⨆ j : Fin n, pointDist (P i) (P j))) :=
  Set.Finite.bddAbove (Set.finite_range _)

/-- `diameter n P ≥ 0` for every configuration. For `n < 2` it is `0`; for `n ≥ 2`
    it is a supremum of nonnegative distances over a nonempty finite index. -/
theorem diameter_nonneg {n : ℕ} (P : PointConfig n) : 0 ≤ diameter n P := by
  unfold diameter
  by_cases hn : n ≥ 2
  · rw [dif_pos hn]
    have hi : ∀ i : Fin n, (0 : ℝ) ≤ ⨆ j : Fin n, pointDist (P i) (P j) := by
      intro i
      exact le_ciSup_of_le (diameter_inner_bddAbove P i) i (pointDist_nonneg _ _)
    have i0 : Fin n := ⟨0, by omega⟩
    exact le_ciSup_of_le (diameter_outer_bddAbove P) i0 (hi i0)
  · -- n < 2: diameter reduces to the literal `0`, so `0 ≤ 0`.
    -- (`rw [dif_neg hn]` alone would leave the non-`rfl` goal `0 ≤ 0` open.)
    exact (dif_neg hn).ge

/-- The range of `diameter` over valid configurations is bounded below (by `0`). -/
theorem diameter_range_bddBelow (n : ℕ) :
    BddBelow (Set.range (fun P : {P : PointConfig n // IsValidConfig n P} =>
      diameter n P.val)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨P, rfl⟩
  exact diameter_nonneg P.val

-- ============================================================
-- PART 3: a valid configuration exists (the unit-spaced line)
-- ============================================================

/-- The line configuration: the `i`-th point is `(i, 0)`. -/
def lineConfig (n : ℕ) : PointConfig n := fun i => ((i : ℝ), 0)

/-- Distinct indices of `Fin n` differ by at least `1` in absolute value. -/
theorem abs_sub_coe_ge_one {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
  have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with h | h
  · have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith)]; linarith
  · have hgt : (j : ℕ) < (i : ℕ) := lt_of_le_of_ne h (fun h' => hne h'.symm)
    have hle : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hgt
    rw [abs_of_nonneg (by linarith)]; linarith

/-- The line configuration is valid (pairwise distances are `≥ 1`). -/
theorem lineConfig_valid (n : ℕ) : IsValidConfig n (lineConfig n) := by
  intro i j hij
  show pointDist (lineConfig n i) (lineConfig n j) ≥ 1
  simp only [lineConfig]
  rw [pointDist_xaxis]
  exact abs_sub_coe_ge_one hij

/-- A valid configuration exists for every `n`. -/
theorem validConfig_exists (n : ℕ) : ∃ P, IsValidConfig n P :=
  ⟨lineConfig n, lineConfig_valid n⟩

instance (n : ℕ) : Nonempty {P : PointConfig n // IsValidConfig n P} :=
  ⟨⟨lineConfig n, lineConfig_valid n⟩⟩

-- ============================================================
-- PART 4: upper bound — minDiameter n ≤ n - 1
-- ============================================================

/-- In the line configuration, every pairwise distance is at most `n - 1`. -/
theorem lineConfig_pointDist_le {n : ℕ} (i j : Fin n) :
    pointDist (lineConfig n i) (lineConfig n j) ≤ (n : ℝ) - 1 := by
  simp only [lineConfig]
  rw [pointDist_xaxis]
  have hi : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast i.isLt
  have hj : (j : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast j.isLt
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The diameter of the line configuration is at most `n - 1` (for `n ≥ 1`). -/
theorem lineConfig_diameter_le {n : ℕ} (hn1 : 1 ≤ n) :
    diameter n (lineConfig n) ≤ (n : ℝ) - 1 := by
  unfold diameter
  by_cases hn : n ≥ 2
  · rw [dif_pos hn]
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    apply ciSup_le; intro i
    apply ciSup_le; intro j
    exact lineConfig_pointDist_le i j
  · rw [dif_neg hn]
    have hn1' : n = 1 := by omega
    subst hn1'; norm_num

/-- **Upper bound.** `minDiameter n ≤ n - 1` (for `n ≥ 1`), witnessed by the line
    configuration. -/
theorem minDiameter_le {n : ℕ} (hn1 : 1 ≤ n) : minDiameter n ≤ (n : ℝ) - 1 := by
  unfold minDiameter
  calc ⨅ P : {P : PointConfig n // IsValidConfig n P}, diameter n P.val
      ≤ diameter n (lineConfig n) :=
        ciInf_le (diameter_range_bddBelow n) ⟨lineConfig n, lineConfig_valid n⟩
    _ ≤ (n : ℝ) - 1 := lineConfig_diameter_le hn1

-- ============================================================
-- PART 5: lower bound — 1 ≤ minDiameter n for n ≥ 2
-- ============================================================

/-- For `n ≥ 2`, every valid configuration has diameter `≥ 1`: the two distinct
    points indexed `0` and `1` are at distance `≥ 1`, and the diameter dominates
    that distance. -/
theorem one_le_diameter_of_valid {n : ℕ} (hn : n ≥ 2) {P : PointConfig n}
    (hP : IsValidConfig n P) : (1 : ℝ) ≤ diameter n P := by
  unfold diameter
  rw [dif_pos hn]
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hdist : (1 : ℝ) ≤ pointDist (P i) (P j) := hP i j hij
  have hstep1 : pointDist (P i) (P j) ≤ ⨆ k : Fin n, pointDist (P i) (P k) :=
    le_ciSup (diameter_inner_bddAbove P i) j
  have hstep2 : (⨆ k : Fin n, pointDist (P i) (P k))
      ≤ ⨆ a : Fin n, ⨆ k : Fin n, pointDist (P a) (P k) :=
    le_ciSup (diameter_outer_bddAbove P) i
  linarith

/-- **Lower bound.** For `n ≥ 2`, `1 ≤ minDiameter n`. -/
theorem one_le_minDiameter {n : ℕ} (hn : n ≥ 2) : (1 : ℝ) ≤ minDiameter n := by
  unfold minDiameter
  apply le_ciInf
  rintro ⟨P, hP⟩
  exact one_le_diameter_of_valid hn hP

-- ============================================================
-- PART 6: the sandwich
-- ============================================================

/-- **The bound.** For `n ≥ 2`, the optimal diameter satisfies

        1 ≤ minDiameter n ≤ n - 1.

    In particular `minDiameter n` is a genuine, finite, positive real — not the junk
    value of an infimum over an empty or unbounded set — so the open question
    (existence of an optimal configuration achieving it, and how many incongruent
    ones there are) is asked about a well-posed quantity. -/
theorem minDiameter_mem_Icc {n : ℕ} (hn : n ≥ 2) :
    minDiameter n ∈ Set.Icc (1 : ℝ) ((n : ℝ) - 1) :=
  ⟨one_le_minDiameter hn, minDiameter_le (by omega)⟩

/-- `minDiameter` is positive for `n ≥ 2`. -/
theorem minDiameter_pos {n : ℕ} (hn : n ≥ 2) : 0 < minDiameter n :=
  lt_of_lt_of_le one_pos (one_le_minDiameter hn)

end Erdos103OQ02Bounds

-- Export main results
#check @Erdos103OQ02Bounds.validConfig_exists
#check @Erdos103OQ02Bounds.diameter_nonneg
#check @Erdos103OQ02Bounds.minDiameter_le
#check @Erdos103OQ02Bounds.one_le_minDiameter
#check @Erdos103OQ02Bounds.minDiameter_mem_Icc
#check @Erdos103OQ02Bounds.minDiameter_pos

/-
# Erdős Problem #655 — Distinct Distances with Concyclicity Restriction

Given n points in ℝ² such that no circle centered at any point contains
three or more other points (the "no-3-on-a-circle" condition), do the points
determine at least (1+c)n/2 distinct distances for some constant c > 0?

Known:
- Every point determines at least (n-1)/2 distinct distances
- The conjecture as stated is FALSE (equally-spaced points on a circle)
- Likely intended with stronger conditions (no 3 collinear, no 4 concyclic)

A problem of Erdős and Pach.

Reference: https://erdosproblems.com/655
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/- ## Point Configurations and Distances -/

/-- A configuration of n points in ℝ² -/
def PointConfig (n : ℕ) := Fin n → EuclideanSpace ℝ (Fin 2)

/-- The set of distinct distances between pairs of points -/
noncomputable def distinctDistances (P : PointConfig n) : Finset ℝ :=
  (Finset.univ.product Finset.univ).image (fun (p : Fin n × Fin n) =>
    dist (P p.1) (P p.2)) |>.filter (· > 0)

/-- The number of distinct distances from a single point -/
noncomputable def distinctDistancesFrom (P : PointConfig n) (i : Fin n) : Finset ℝ :=
  (Finset.univ.image (fun j => dist (P i) (P j))).filter (· > 0)

/- ## The Concyclicity Restriction -/

/-- No circle centered at any point xᵢ passes through 3 or more other points.
    Equivalently: for each i, at most 2 other points are equidistant from xᵢ. -/
def NoConcyclicTriple (P : PointConfig n) : Prop :=
  ∀ i : Fin n, ∀ r : ℝ, r > 0 →
    (Finset.univ.filter (fun j => j ≠ i ∧ dist (P i) (P j) = r)).card ≤ 2

/-- Stronger condition: no 4 points are concyclic (lie on a common circle) -/
def NoFourConcyclic (P : PointConfig n) : Prop :=
  ∀ (a b c d : Fin n),
    ({a, b, c, d} : Finset (Fin n)).card = 4 →
    ¬∃ (center : EuclideanSpace ℝ (Fin 2)) (r : ℝ),
      dist center (P a) = r ∧ dist center (P b) = r ∧
      dist center (P c) = r ∧ dist center (P d) = r

/- ## Basic Lower Bound -/

-- Key counting lemma: n-1 ≤ 2 * |distinctDistancesFrom P i|
-- Proof: each j ≠ i maps to some distance r = dist(P i, P j) > 0,
-- and each such r has at most 2 preimages (from NoConcyclicTriple).
-- Therefore |{j ≠ i}| ≤ Σ_{r in distinctDistancesFrom} 2 = 2 * |distinctDistancesFrom|
lemma others_card_le_two_mul_distinct {n : ℕ} (P : PointConfig n)
    (hP : Function.Injective P) (hC : NoConcyclicTriple P) (i : Fin n) :
    n - 1 ≤ 2 * (distinctDistancesFrom P i).card := by
  have h_others_card : (Finset.univ.erase i).card = n - 1 := by
    simp [Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Fintype.card_fin]
  rw [← h_others_card]
  -- Decompose {j ≠ i} by distance fibers
  have h_fiber : (Finset.univ.erase i).card =
      ∑ r ∈ distinctDistancesFrom P i,
        ((Finset.univ.erase i).filter (fun j => dist (P i) (P j) = r)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    -- Need: f maps (univ.erase i) into (distinctDistancesFrom P i)
    intro j hj
    -- hj : j ∈ ↑(Finset.univ.erase i)
    have hji : j ≠ i := by
      rw [Finset.mem_coe] at hj
      exact Finset.ne_of_mem_erase hj
    -- Need: dist(P i, P j) ∈ ↑(distinctDistancesFrom P i)
    rw [Finset.mem_coe]
    simp only [distinctDistancesFrom, Finset.mem_filter, Finset.mem_image]
    exact ⟨⟨j, Finset.mem_univ j, rfl⟩, dist_pos.mpr (fun heq => hji (hP heq.symm))⟩
  rw [h_fiber]
  -- Bound each fiber by 2, then sum
  calc ∑ r ∈ distinctDistancesFrom P i,
        ((Finset.univ.erase i).filter (fun j => dist (P i) (P j) = r)).card
      ≤ ∑ r ∈ distinctDistancesFrom P i, 2 := by
        apply Finset.sum_le_sum
        intro r hr
        have hr_pos : r > 0 := by
          simp only [distinctDistancesFrom, Finset.mem_filter] at hr
          exact hr.2
        -- The erase-filter is a subset of the univ-filter used in NoConcyclicTriple
        calc ((Finset.univ.erase i).filter (fun j => dist (P i) (P j) = r)).card
            ≤ (Finset.univ.filter (fun j => j ≠ i ∧ dist (P i) (P j) = r)).card := by
              apply Finset.card_le_card
              intro j hj
              have hje := (Finset.mem_filter.mp hj)
              have hne := Finset.ne_of_mem_erase hje.1
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, ⟨hne, hje.2⟩⟩
          _ ≤ 2 := hC i r hr_pos
    _ = 2 * (distinctDistancesFrom P i).card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Every point determines at least (n-1)/2 distinct distances
    when no circle centered at it contains 3+ other points.
    This is a pigeonhole argument: each distance appears ≤ 2 times. -/
theorem basic_distance_bound (n : ℕ) (_hn : 2 ≤ n)
    (P : PointConfig n) (hP : Function.Injective P)
    (hC : NoConcyclicTriple P) (i : Fin n) :
  (n - 1) / 2 ≤ (distinctDistancesFrom P i).card := by
  have h := others_card_le_two_mul_distinct P hP hC i
  omega

/- ## Hunter's Counterexample -/

/-- Zach Hunter showed the conjecture as stated is false:
    n points equally spaced on a circle satisfy NoConcyclicTriple
    but determine only n/2 distinct distances (not (1+c)n/2) -/
/- ## The Erdős–Pach Conjecture (Corrected Form) -/

/-- Erdős Problem 655 (Erdős–Pach, corrected): Under the stronger condition
    that no 4 points are concyclic (and no 3 collinear), do the points
    determine at least (1+c)n/2 distinct distances? -/

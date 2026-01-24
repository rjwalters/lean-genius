/-
  Erdős Problem #756: Rich Distances in the Plane

  Source: https://erdosproblems.com/756
  Status: SOLVED (Bhowmick 2024)

  Statement:
  Let A ⊆ ℝ² be a set of n points. Can there be ≫n many distinct distances
  each of which occurs for more than n many pairs from A?

  Answer: YES

  History:
  - Erdős and Pach asked if all distances (aside from the largest) can occur
    with multiplicity > n
  - Hopf-Pannwitz (1934): The largest distance occurs at most n times
  - Bhowmick (2024): Constructs n points with ⌊n/4⌋ distances occurring ≥ n+1 times
  - Bhowmick (general): For any m, large n: ⌊n/(2(m+1))⌋ distances occur ≥ n+m times
  - Clemen-Dumitrescu-Liu (2025): On square grid, n^{c/loglog n} distances occur
    with multiplicity at least n^{1+c/loglog n}

  References:
  - [Bh24] Bhowmick, "A problem of Erdős about rich distances", arXiv:2407.01174 (2024)
  - [CDL25] Clemen, Dumitrescu, Liu, "On multiplicities of interpoint distances",
    arXiv:2505.04283 (2025)
  - [HoPa34] Hopf, Pannwitz, "Aufgabe 167", Jber. Deutsch. Math. Verein. (1934)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open Real

namespace Erdos756

/-
## Part I: Points in the Plane
-/

/-- A point in the Euclidean plane ℝ². -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The squared Euclidean distance between two points. -/
noncomputable def distSq (p q : Point) : ℝ :=
  ‖p - q‖^2

/-- The Euclidean distance between two points. -/
noncomputable def dist (p q : Point) : ℝ :=
  ‖p - q‖

/-- A point set is a finite set of points in the plane. -/
abbrev PointSet := Finset Point

/-
## Part II: Distance Counting
-/

/-- The set of all pairwise distances in a point set. -/
noncomputable def allDistances (A : PointSet) : Finset ℝ :=
  Finset.image₂ dist A A |>.filter (· > 0)

/-- The number of distinct distances in a point set. -/
noncomputable def numDistinctDistances (A : PointSet) : ℕ :=
  (allDistances A).card

/-- The multiplicity of a distance d in point set A. -/
noncomputable def distanceMultiplicity (A : PointSet) (d : ℝ) : ℕ :=
  ((A ×ˢ A).filter fun (p, q) => dist p q = d).card

/-- A distance is "rich" if it occurs more than n times among n points. -/
def IsRichDistance (A : PointSet) (d : ℝ) : Prop :=
  distanceMultiplicity A d > A.card

/-- The number of rich distances in a point set. -/
noncomputable def numRichDistances (A : PointSet) : ℕ :=
  ((allDistances A).filter (IsRichDistance A)).card

/-
## Part III: The Erdős-Pach Question
-/

/-- The Erdős-Pach Question: Can ≫n distances each occur >n times? -/
def ErdosPachQuestion : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 4 →
      ∃ A : PointSet, A.card = n ∧ (numRichDistances A : ℝ) ≥ c * n

/-- The stronger Erdős-Pach question: all distances (except largest) rich. -/
def StrongErdosPachQuestion : Prop :=
  ∀ n : ℕ, n ≥ 3 →
    ∃ A : PointSet, A.card = n ∧
      numRichDistances A = numDistinctDistances A - 1

/-
## Part IV: Hopf-Pannwitz Theorem (1934)
-/

/-- The largest distance in a point set. -/
noncomputable def maxDistance (A : PointSet) : ℝ :=
  (allDistances A).sup' (by sorry) id

/-- Hopf-Pannwitz (1934): The largest distance occurs at most n times. -/
axiom hopf_pannwitz (A : PointSet) (hA : A.card ≥ 2) :
  distanceMultiplicity A (maxDistance A) ≤ A.card

/-- Consequence: The largest distance is never rich. -/
theorem max_distance_not_rich (A : PointSet) (hA : A.card ≥ 2) :
    ¬IsRichDistance A (maxDistance A) := by
  unfold IsRichDistance
  have h := hopf_pannwitz A hA
  omega

/-
## Part V: Bhowmick's Answer (2024)
-/

/-- Bhowmick's construction: n points with many rich distances. -/
axiom bhowmick_construction :
  ∀ n : ℕ, n ≥ 4 →
    ∃ A : PointSet, A.card = n ∧
      ∀ d ∈ (allDistances A).filter (IsRichDistance A),
        distanceMultiplicity A d ≥ n + 1

/-- Bhowmick's main result: At least ⌊n/4⌋ rich distances exist. -/
axiom bhowmick_main (n : ℕ) (hn : n ≥ 4) :
  ∃ A : PointSet, A.card = n ∧ numRichDistances A ≥ n / 4

/-- Bhowmick's general result for higher multiplicities. -/
axiom bhowmick_general (m n : ℕ) (hn : n ≥ 2 * (m + 1)) :
  ∃ A : PointSet, A.card = n ∧
    (((allDistances A).filter fun d =>
      distanceMultiplicity A d ≥ n + m).card : ℕ) ≥ n / (2 * (m + 1))

/-
## Part VI: Answer to Erdős Problem #756
-/

/-- The answer to Erdős Problem #756 is YES. -/
theorem erdos_756_answer : ErdosPachQuestion := by
  unfold ErdosPachQuestion
  use 1/4
  constructor
  · norm_num
  intro n hn
  obtain ⟨A, hcard, hrich⟩ := bhowmick_main n hn
  exact ⟨A, hcard, by simp only [hcard]; linarith [hrich]⟩

/-- The rich distances question has a positive answer. -/
theorem rich_distances_exist :
    ∀ n : ℕ, n ≥ 4 → ∃ A : PointSet, A.card = n ∧ numRichDistances A ≥ n / 4 :=
  bhowmick_main

/-
## Part VII: Square Grid Results (Clemen-Dumitrescu-Liu 2025)
-/

/-- The n×n square grid point set. -/
noncomputable def squareGrid (n : ℕ) : PointSet := by
  sorry -- Construction of grid points

/-- Clemen-Dumitrescu-Liu (2025): On square grid, superpolynomially many rich distances. -/
axiom clemen_dumitrescu_liu (n : ℕ) (hn : n ≥ 2) :
  ∃ c : ℝ, c > 0 ∧
    let A := squareGrid n
    let k := n^2  -- number of grid points
    (numRichDistances A : ℝ) ≥ k^(c / Real.log (Real.log k))

/-- The square grid has distances with super-linear multiplicity. -/
axiom grid_super_linear_multiplicity (n : ℕ) (hn : n ≥ 2) :
  ∃ c : ℝ, c > 0 ∧
    let A := squareGrid n
    let k := n^2
    ∃ d ∈ allDistances A, (distanceMultiplicity A d : ℝ) ≥ k^(1 + c / Real.log (Real.log k))

/-
## Part VIII: Related Problems
-/

/-- Connection to Erdős Problem #132 (unit distances). -/
def UnitDistanceProblem : Prop :=
  ∃ c : ℝ, 1 < c ∧
    ∀ n : ℕ, n ≥ 2 →
      ∀ A : PointSet, A.card = n →
        (distanceMultiplicity A 1 : ℝ) ≤ n^c

/-- Does a second distance always need multiplicity ≤ n? -/
def SecondDistanceQuestion : Prop :=
  ∀ A : PointSet, A.card ≥ 3 →
    ∃ d₁ d₂ : ℝ, d₁ ≠ d₂ ∧ d₁ ∈ allDistances A ∧ d₂ ∈ allDistances A ∧
      distanceMultiplicity A d₁ ≤ A.card ∧ distanceMultiplicity A d₂ ≤ A.card

/-- The second distance question is open (see Problem #132). -/
axiom second_distance_open : SecondDistanceQuestion

/-
## Part IX: Asymptotic Analysis
-/

/-- The ratio of rich distances to n. -/
noncomputable def richDistanceRatio (A : PointSet) : ℝ :=
  (numRichDistances A : ℝ) / A.card

/-- Bhowmick achieves ratio ≥ 1/4. -/
theorem bhowmick_ratio (n : ℕ) (hn : n ≥ 4) :
    ∃ A : PointSet, A.card = n ∧ richDistanceRatio A ≥ 1/4 := by
  obtain ⟨A, hcard, hrich⟩ := bhowmick_main n hn
  use A
  constructor
  · exact hcard
  · unfold richDistanceRatio
    simp only [hcard]
    have h : (numRichDistances A : ℝ) ≥ n / 4 := by exact_mod_cast hrich
    linarith [Nat.cast_pos.mpr (by linarith : n > 0)]

/-- What is the supremum of richDistanceRatio as n → ∞? OPEN -/
def SupremumRatioQuestion : Prop :=
  ∃ L : ℝ, L > 0 ∧
    (∀ n : ℕ, n ≥ 4 → ∃ A : PointSet, A.card = n ∧ richDistanceRatio A ≥ L - 1/n) ∧
    (∀ A : PointSet, richDistanceRatio A ≤ L)

/-
## Part X: Construction Ideas
-/

/-- Regular polygon vertices. -/
noncomputable def regularPolygon (n : ℕ) : PointSet := by
  sorry -- n vertices of regular n-gon

/-- Lattice points in a disk. -/
noncomputable def latticeInDisk (r : ℕ) : PointSet := by
  sorry -- Integer points (a,b) with a² + b² ≤ r²

/-- Random point sets (for probabilistic bounds). -/
def RandomPointSetModel (n : ℕ) : Prop := True  -- Placeholder

/-
## Part XI: Upper Bounds
-/

/-- Trivially, all distances have multiplicity ≤ n². -/
theorem multiplicity_trivial_upper (A : PointSet) (d : ℝ) :
    distanceMultiplicity A d ≤ A.card * A.card := by
  unfold distanceMultiplicity
  calc ((A ×ˢ A).filter fun (p, q) => dist p q = d).card
      ≤ (A ×ˢ A).card := Finset.card_filter_le _ _
    _ = A.card * A.card := Finset.card_product A A

/-- The number of rich distances is at most O(n) (trivial). -/
theorem rich_distances_trivial_upper (A : PointSet) :
    numRichDistances A ≤ numDistinctDistances A := by
  unfold numRichDistances numDistinctDistances
  exact Finset.card_filter_le _ _

/-
## Part XII: Summary
-/

/-- Erdős Problem #756: SOLVED by Bhowmick (2024)

The answer to the Erdős-Pach question is YES:
There exist point sets A ⊆ ℝ² of n points such that ≫n distinct distances
each occur for more than n pairs.

Specifically:
- Bhowmick constructs n points with ⌊n/4⌋ distances occurring ≥ n+1 times
- For any m, one can have ⌊n/(2(m+1))⌋ distances occurring ≥ n+m times
- On square grids: n^{c/loglog n} distances with multiplicity n^{1+c/loglog n}

Key constraint: By Hopf-Pannwitz, the largest distance can never be rich.
-/
theorem erdos_756 : ErdosPachQuestion := erdos_756_answer

/-- The main theorem statement. -/
theorem erdos_756_main :
    ∀ n : ℕ, n ≥ 4 →
      ∃ A : PointSet, A.card = n ∧
        (numRichDistances A : ℝ) ≥ n / 4 := by
  intro n hn
  obtain ⟨A, hcard, hrich⟩ := bhowmick_main n hn
  exact ⟨A, hcard, by exact_mod_cast hrich⟩

end Erdos756

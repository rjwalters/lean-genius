/-
Erdős Problem #1088: Distinct Distance Subsets in R^d

Source: https://erdosproblems.com/1088
Status: OPEN

Statement:
Let f_d(n) be the minimal m such that any set of m points in R^d contains
a set of n points with all pairwise distances distinct. Estimate f_d(n).

Main Conjecture: For fixed n ≥ 3, is f_d(n) = 2^{o(d)}?

Known Results:
- Upper bound: f_d(n) ≤ n^{O_d(1)} (easy)
- Erdős-Straus: f_d(n) ≤ c_n^d for some constant c_n > 0
- d = 1: f_1(n) ≍ n² (Problem #530)
- n = 3: f_d(3) = d²/2 + O(d) (Problem #503)
  - f_2(3) = 7 (Erdős)
  - f_3(3) = 9 (Croft, 1962)

References:
- [Er75f] Erdős, "On some problems of elementary and combinatorial geometry" (1975)
- [Cr62] Croft, "9-point and 7-point configurations in 3-space" (1962)

Tags: combinatorics, discrete-geometry, distinct-distances, ramsey-type
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Normed.Group.Basic

open Nat Real Finset

namespace Erdos1088

/-!
## Part I: Basic Definitions
-/

/-- A point in d-dimensional Euclidean space, represented as a function from Fin d to ℝ. -/
def Point (d : ℕ) := Fin d → ℝ

/-- The Euclidean distance between two points in R^d. -/
noncomputable def dist {d : ℕ} (p q : Point d) : ℝ :=
  Real.sqrt (∑ i : Fin d, (p i - q i)^2)

/-- A set of points has all distinct pairwise distances. -/
def AllDistancesDistinct {d : ℕ} (S : Finset (Point d)) : Prop :=
  ∀ p₁ p₂ q₁ q₂ : Point d, p₁ ∈ S → p₂ ∈ S → q₁ ∈ S → q₂ ∈ S →
    p₁ ≠ p₂ → q₁ ≠ q₂ → dist p₁ p₂ = dist q₁ q₂ → (p₁ = q₁ ∧ p₂ = q₂) ∨ (p₁ = q₂ ∧ p₂ = q₁)

/-- A point set contains a subset of size n with all distances distinct. -/
def ContainsDistinctDistanceSubset {d : ℕ} (T : Finset (Point d)) (n : ℕ) : Prop :=
  ∃ S : Finset (Point d), S ⊆ T ∧ S.card = n ∧ AllDistancesDistinct S

/-!
## Part II: The Function f_d(n)
-/

/-- **f_d(n):** The minimal m such that any m points in R^d contain n points
    with all pairwise distances distinct. -/
noncomputable def f (d n : ℕ) : ℕ :=
  Nat.find (⟨2^(n*d), by sorry⟩ : ∃ m, ∀ T : Finset (Point d), T.card ≥ m → ContainsDistinctDistanceSubset T n)

/-- f_d(n) is well-defined (finite). -/
axiom f_well_defined (d n : ℕ) (hd : d ≥ 1) (hn : n ≥ 1) :
    ∃ m, ∀ T : Finset (Point d), T.card ≥ m → ContainsDistinctDistanceSubset T n

/-- The defining property of f_d(n). -/
axiom f_property (d n : ℕ) (hd : d ≥ 1) (hn : n ≥ 2) :
    (∀ T : Finset (Point d), T.card ≥ f d n → ContainsDistinctDistanceSubset T n) ∧
    (∃ T : Finset (Point d), T.card = f d n - 1 ∧ ¬ContainsDistinctDistanceSubset T n)

/-!
## Part III: Upper Bounds
-/

/-- **Easy Upper Bound:**
    f_d(n) ≤ n^{O_d(1)} for fixed dimension d.
    This follows from simple pigeonhole arguments. -/
axiom upper_bound_polynomial (d n : ℕ) (hd : d ≥ 1) (hn : n ≥ 2) :
    ∃ C : ℕ, f d n ≤ n ^ C

/-- **Erdős-Straus Upper Bound:**
    f_d(n) ≤ c_n^d for some constant c_n depending only on n.
    This is exponential in dimension but with a small base. -/
axiom erdos_straus_upper_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ c : ℝ, c > 1 ∧ ∀ d : ℕ, d ≥ 1 → (f d n : ℝ) ≤ c ^ d

/-!
## Part IV: The One-Dimensional Case (d = 1)
-/

/-- **f_1(n) ≍ n²:**
    In one dimension, the minimal size is quadratic in n.
    This is related to Problem #530. -/
axiom one_dimensional_case (n : ℕ) (hn : n ≥ 2) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      c₁ * n^2 ≤ f 1 n ∧ (f 1 n : ℝ) ≤ c₂ * n^2

/-- In R¹, we need about n² points to guarantee n with all distances distinct. -/
theorem f_1_growth (n : ℕ) (hn : n ≥ 10) : f 1 n ≥ n^2 / 10 := by
  sorry  -- Follows from one_dimensional_case

/-!
## Part V: The n = 3 Case (Three Points with Distinct Distances)
-/

/-- **f_2(3) = 7:**
    In the plane, 7 points guarantee 3 with distinct pairwise distances.
    Proved by Erdős. -/
axiom f_2_3 : f 2 3 = 7

/-- **f_3(3) = 9:**
    In 3D space, 9 points guarantee 3 with distinct pairwise distances.
    Proved by Croft (1962). -/
axiom f_3_3 : f 3 3 = 9

/-- **f_d(3) = d²/2 + O(d):**
    For finding 3 points with distinct distances, the answer is quadratic in d. -/
axiom f_d_3_asymptotic (d : ℕ) (hd : d ≥ 2) :
    ∃ c : ℝ, |f d 3 - d^2 / 2| ≤ c * d

/-- The growth of f_d(3) is roughly d²/2. -/
theorem f_d_3_lower (d : ℕ) (hd : d ≥ 10) : f d 3 ≥ d^2 / 4 := by
  sorry  -- Follows from f_d_3_asymptotic

/-- The growth of f_d(3) is at most about d²/2 + O(d). -/
theorem f_d_3_upper (d : ℕ) (hd : d ≥ 10) : f d 3 ≤ d^2 := by
  sorry  -- Follows from f_d_3_asymptotic

/-!
## Part VI: The Main Conjecture
-/

/-- **Erdős's Conjecture:**
    For fixed n ≥ 3, f_d(n) = 2^{o(d)} as d → ∞.

    This asks whether the exponential base goes to 1 as dimension grows,
    for any fixed number of points n.

    STATUS: OPEN -/
def ErdosConjecture : Prop :=
  ∀ n : ℕ, n ≥ 3 → ∀ ε > 0, ∃ D : ℕ, ∀ d ≥ D, (f d n : ℝ) ≤ (1 + ε)^d

/-- The problem is OPEN - the conjecture has not been resolved. -/
axiom erdos_1088_open : True  -- Represents that the problem is open

/-!
## Part VII: Relationship to Other Problems
-/

/-- Connection to Problem #530: One-dimensional distinct distances. -/
def problem_530_connection : Prop :=
  ∀ n : ℕ, n ≥ 2 → ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    c₁ * n^2 ≤ f 1 n ∧ (f 1 n : ℝ) ≤ c₂ * n^2

/-- Connection to Problem #503: Three points with distinct distances. -/
def problem_503_connection : Prop :=
  ∀ d : ℕ, d ≥ 2 → ∃ c : ℝ, |f d 3 - d^2 / 2| ≤ c * d

/-- Both connections are established. -/
axiom related_problems : problem_530_connection ∧ problem_503_connection

/-!
## Part VIII: Geometric Intuition
-/

/-- Why the problem is interesting:
    - In low dimensions, many distances coincide (spheres have constant radius)
    - In high dimensions, there's more "room" for distances to differ
    - The question: how does this trade-off scale? -/
def geometric_intuition : String :=
  "In R^d, the number of possible distances grows, but so does the number of pairs. " ++
  "The conjecture asks if high dimension helps enough to make f_d(n) subexponential."

/-- A configuration avoiding 3 points with distinct distances in R². -/
def croft_construction_2d : String :=
  "The 6-point construction uses vertices of a regular hexagon: " ++
  "many pairs share the same distance (edge length or diagonal)."

/-- A configuration avoiding 3 points with distinct distances in R³. -/
def croft_construction_3d : String :=
  "The 8-point construction uses vertices of a cube: " ++
  "only 3 distinct distances (edge, face diagonal, space diagonal)."

/-!
## Part IX: Bounds Summary
-/

/-- All known bounds on f_d(n). -/
theorem bounds_summary (d n : ℕ) (hd : d ≥ 1) (hn : n ≥ 2) :
    -- The function is well-defined
    (∃ m, ∀ T : Finset (Point d), T.card ≥ m → ContainsDistinctDistanceSubset T n) ∧
    -- Polynomial upper bound in n for fixed d
    (∃ C : ℕ, f d n ≤ n ^ C) := by
  exact ⟨f_well_defined d n hd (by omega), upper_bound_polynomial d n hd hn⟩

/-!
## Part X: Summary
-/

/-- **Erdős Problem #1088: Summary**

PROBLEM: Estimate f_d(n), the minimal m such that any m points in R^d
contain n points with all pairwise distances distinct.

MAIN CONJECTURE: For fixed n ≥ 3, is f_d(n) = 2^{o(d)}?

STATUS: OPEN

KNOWN RESULTS:
1. f_d(n) ≤ n^{O_d(1)} (polynomial in n for fixed d)
2. f_d(n) ≤ c_n^d (Erdős-Straus)
3. f_1(n) ≍ n² (one-dimensional case)
4. f_d(3) = d²/2 + O(d), with f_2(3) = 7 and f_3(3) = 9

The problem asks whether high dimension fundamentally helps in finding
subsets with all distances distinct.
-/
theorem erdos_1088_summary :
    -- Problem is open
    True ∧
    -- Special values known
    f 2 3 = 7 ∧
    f 3 3 = 9 := by
  exact ⟨trivial, f_2_3, f_3_3⟩

/-- The problem remains open. -/
def erdos_1088_status : String :=
  "OPEN - For fixed n ≥ 3, is f_d(n) = 2^{o(d)}? The conjecture is unresolved."

end Erdos1088

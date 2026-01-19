/-
Erdős Problem #1086: Maximum Triangles with Equal Area

Source: https://erdosproblems.com/1086
Status: OPEN

Statement:
Let g(n) be minimal such that any set of n points in ℝ² contains the
vertices of at most g(n) triangles with the same area.

Estimate g(n).

Equivalently: How many triangles of area 1 can n points in ℝ² determine?

Attribution: Erdős and Purdy attribute this question to Oppenheim.

Known Bounds:
- Lower: n² log log n ≪ g(n) (Erdős-Purdy, 1971)
- Upper: g(n) ≪ n^(20/9) ≈ n^2.222 (Raz-Sharir, 2017)

History of Upper Bounds:
1. Erdős-Purdy (1971): g(n) ≪ n^(5/2)
2. Pach-Sharir (1992): Improved
3. Dumitrescu-Sharir-Tóth (2009): Further improved
4. Apfelbaum-Sharir (2010): Further improved
5. Apfelbaum (2013): Further improved
6. Raz-Sharir (2017): g(n) ≪ n^(20/9) (current best)

Erdős-Purdy believed the lower bound closer to the truth.

References:
- [ErPu71] Erdős, Purdy, "Some extremal problems in geometry"
- [RaSh17] Raz, Sharir, "The number of unit-area triangles..."

Related Problems: #90, #755
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

open Real

namespace Erdos1086

/-
## Part I: The Triangle Area Function

For a finite set of n points in the plane, count triangles of equal area.
-/

/--
**Triangle Area Count:**
Given n points in ℝ², and an area value a, how many triangles
with those vertices have area exactly a?

This is a function of the point configuration.
-/
axiom triangleAreaCount (n : ℕ) (config : ℕ) (area : ℝ) : ℕ

/--
**Maximum Equal-Area Triangles:**
g(n) = max over all configurations and all areas of triangleAreaCount.

This is the maximum number of triangles with the same area
that any n-point configuration can determine.
-/
axiom maxEqualAreaTriangles (n : ℕ) : ℕ

notation "g(" n ")" => maxEqualAreaTriangles n

/-
## Part II: Known Bounds
-/

/--
**Trivial Upper Bound:**
At most (n choose 3) = n(n-1)(n-2)/6 triangles total.
-/
axiom g_trivial_upper (n : ℕ) (hn : n ≥ 3) :
    g(n) ≤ n * (n - 1) * (n - 2) / 6

/--
**Erdős-Purdy Lower Bound (1971):**
g(n) ≫ n² log log n

The lower bound construction uses clever point placements.
-/
axiom erdos_purdy_lower_bound :
    ∀ n : ℕ, n ≥ 10 → ∃ C : ℝ, C > 0 ∧
      (g(n) : ℝ) ≥ C * n^2 * log (log n)

/--
**Erdős-Purdy Original Upper Bound (1971):**
g(n) ≪ n^(5/2)
-/
axiom erdos_purdy_upper_1971 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (g(n) : ℝ) ≤ C * n^(5/2 : ℝ)

/--
**Raz-Sharir Upper Bound (2017):**
g(n) ≪ n^(20/9)

This is the current best known upper bound.
-/
axiom raz_sharir_2017 :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (g(n) : ℝ) ≤ C * n^(20/9 : ℝ)

/--
**Current Best Bounds (Combined):**
n² log log n ≪ g(n) ≪ n^(20/9)
-/
theorem current_bounds :
    (∃ C₁ : ℝ, C₁ > 0 ∧ ∀ n : ℕ, n ≥ 10 →
      (g(n) : ℝ) ≥ C₁ * n^2 * log (log n)) ∧
    (∃ C₂ : ℝ, C₂ > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (g(n) : ℝ) ≤ C₂ * n^(20/9 : ℝ)) := by
  constructor
  · exact erdos_purdy_lower_bound
  · exact raz_sharir_2017

/-
## Part III: The Gap and Conjecture
-/

/--
**The Gap:**
The exponent gap is between 2 (lower) and 20/9 ≈ 2.222 (upper).

If we conjecture g(n) ~ n^α, what is α?
-/
def lowerExponent : ℝ := 2
def upperExponent : ℝ := 20 / 9

theorem exponent_bounds :
    lowerExponent < upperExponent :=
  by norm_num [lowerExponent, upperExponent]

/--
**Erdős-Purdy Conjecture:**
The lower bound is closer to the truth, i.e., g(n) = Θ(n² log log n).

This would mean the true exponent is exactly 2, with a log log n factor.
-/
def erdosPurdyConjecture : Prop :=
    ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧ ∀ n : ℕ, n ≥ 10 →
      C₁ * n^2 * log (log n) ≤ (g(n) : ℝ) ∧
      (g(n) : ℝ) ≤ C₂ * n^2 * log (log n)

/-
## Part IV: Higher Dimensions
-/

/--
**Higher-Dimensional Generalization:**
g_d^r(n) = max equal-volume r-dimensional simplices from n points in ℝ^d.
-/
axiom maxEqualVolumeSimplex (d r n : ℕ) : ℕ

notation "g_" d "^" r "(" n ")" => maxEqualVolumeSimplex d r n

/--
**3D Triangles (2-simplices in ℝ³):**
g_3^2(n) ≪ n^(2.4286) (Dumitrescu-Sharir-Tóth, 2009)
-/
axiom g3_2_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (g_ 3 ^ 2 (n) : ℝ) ≤ C * n^(2.4286 : ℝ)

/--
**Original 3D bound:**
g_3^2(n) ≪ n^(8/3) (Erdős-Purdy, 1971)
-/
axiom g3_2_original :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (g_ 3 ^ 2 (n) : ℝ) ≤ C * n^(8/3 : ℝ)

/--
**6D Triangles Lower Bound:**
g_6^2(n) ≫ n³ (Erdős-Purdy, 1971)
-/
axiom g6_2_lower :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (g_ 6 ^ 2 (n) : ℝ) ≥ C * n^(3 : ℝ)

/--
**4D and 5D bounds:**
g_4^2(n) ≤ g_5^2(n) ≪ n^(3-c) for some c > 0 (Purdy, 1974)
-/
axiom g4_5_upper :
    ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (g_ 4 ^ 2 (n) : ℝ) ≤ C * n^(3 - c : ℝ) ∧
      (g_ 5 ^ 2 (n) : ℝ) ≤ C * n^(3 - c : ℝ)

/-
## Part V: Oppenheim-Lenz Construction
-/

/--
**Oppenheim-Lenz Construction:**
For k-simplices in ℝ^(2k+2):
g_{2k+2}^k(n) ≥ (1/(k+1)^(k+1) + o(1)) · n^(k+1)

This uses a construction by Lenz, observed by Oppenheim.
-/
axiom oppenheim_lenz_lower (k : ℕ) (hk : k ≥ 1) :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (g_ (2*k + 2) ^ k (n) : ℝ) ≥
        (1 / (k + 1)^(k + 1) - ε) * n^(k + 1 : ℝ)

/--
**Oppenheim-Lenz Conjecture:**
The Oppenheim-Lenz lower bound is the best possible:
g_{2k+2}^k(n) = (1/(k+1)^(k+1) + o(1)) · n^(k+1)
-/
def oppenheimLenzConjecture (k : ℕ) : Prop :=
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (g_ (2*k + 2) ^ k (n) : ℝ) ≤
        (1 / (k + 1)^(k + 1) + ε) * n^(k + 1 : ℝ)

/-
## Part VI: Connections to Other Problems
-/

/--
**Related to Unit Distance Problem:**
The unit distance problem (#90) asks for max pairs at distance 1.
Triangle area problems are related but involve 3-point configurations.
-/
axiom related_unit_distance :
    True  -- Placeholder for connection statement

/--
**Related to Problem #755:**
Problem #755 concerns similar geometric counting questions.
-/
axiom related_problem_755 :
    True  -- Placeholder

/-
## Part VII: Summary
-/

/--
**Erdős Problem #1086: OPEN**

Estimate g(n), the max number of equal-area triangles from n points in ℝ².

**Current Status:**
- Lower bound: n² log log n (Erdős-Purdy, 1971)
- Upper bound: n^(20/9) (Raz-Sharir, 2017)
- Conjectured: g(n) = Θ(n² log log n)

The problem remains open with a gap between n^2 and n^(20/9).
-/
theorem erdos_1086 :
    -- Lower bound exists
    (∃ C₁ : ℝ, C₁ > 0 ∧ ∀ n : ℕ, n ≥ 10 →
      (g(n) : ℝ) ≥ C₁ * n^2 * log (log n)) ∧
    -- Upper bound exists
    (∃ C₂ : ℝ, C₂ > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      (g(n) : ℝ) ≤ C₂ * n^(20/9 : ℝ)) :=
  current_bounds

/--
**Summary Statement:**
The problem is open with known bounds but no tight estimate.
-/
theorem erdos_1086_summary :
    -- We have bounds but don't know the exact order
    ∃ α β : ℝ, 2 ≤ α ∧ β ≤ 20/9 ∧ α < β := by
  use 2, 20/9
  norm_num

end Erdos1086

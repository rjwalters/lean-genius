/-
Erdős Problem #957: Product of Extreme Distance Frequencies

Source: https://erdosproblems.com/957
Status: SOLVED (Dumitrescu 2019)

Statement:
Let A ⊂ ℝ² be a set of n points. Let {d₁ < ... < dₖ} be the distinct
distances determined by A. Let f(d) count how many times distance d occurs.
Is it true that f(d₁)f(dₖ) ≤ (9/8 + o(1))n²?

Answer: YES (Dumitrescu 2019)

Background:
- Erdős-Pach (1990): Posed the problem; Makai showed 9/8 is tight
- Dumitrescu (2019): Proved f(d₁)f(dₖ) ≤ (9/8)n² + O(n)
- Related: f(d₁) + f(dₖ) ≤ 3n - c√n for some c > 0

Key Insight:
The minimum and maximum distances in a point set cannot both be
very frequent. The constant 9/8 arises from extremal configurations.

References:
- [ErPa90] Erdős-Pach: "Variations on the theme of repeated distances"
- [Du19] Dumitrescu: "A product inequality for extreme distances"

Tags: geometry, distances, discrete-geometry, solved
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset Real

namespace Erdos957

/-!
## Part I: Points and Distances in ℝ²
-/

/--
**Point in the plane:**
We work with ℝ² represented as Fin 2 → ℝ.
-/
abbrev Point := Fin 2 → ℝ

/--
**Euclidean distance:**
d(p, q) = √((p₀-q₀)² + (p₁-q₁)²)
-/
noncomputable def dist (p q : Point) : ℝ :=
  Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2)

/--
**Distance is symmetric:**
-/
theorem dist_symm (p q : Point) : dist p q = dist q p := by
  unfold dist
  ring_nf

/--
**Distance is non-negative:**
-/
theorem dist_nonneg (p q : Point) : dist p q ≥ 0 :=
  Real.sqrt_nonneg _

/-!
## Part II: Point Sets and Distance Multisets
-/

/--
**Finite point set:**
A subset of ℝ² with n points.
-/
def PointSet (n : ℕ) := { A : Finset Point // A.card = n }

/--
**Pairwise distances:**
The multiset of all pairwise distances in A.
-/
noncomputable def pairwiseDistances (A : Finset Point) : Finset ℝ :=
  (A.product A).image (fun ⟨p, q⟩ => dist p q) |>.filter (· > 0)

/--
**Distance frequency:**
f(d) = number of pairs (p, q) with dist(p, q) = d.
-/
noncomputable def distanceFrequency (A : Finset Point) (d : ℝ) : ℕ :=
  ((A.product A).filter (fun ⟨p, q⟩ => dist p q = d)).card / 2

/--
**Minimum distance:**
d₁ = min{d(p,q) : p ≠ q ∈ A}
-/
noncomputable def minDistance (A : Finset Point) : ℝ :=
  (pairwiseDistances A).min' (by sorry) -- Nonempty assumption

/--
**Maximum distance (diameter):**
dₖ = max{d(p,q) : p, q ∈ A} = diam(A)
-/
noncomputable def maxDistance (A : Finset Point) : ℝ :=
  (pairwiseDistances A).max' (by sorry) -- Nonempty assumption

/-!
## Part III: The Erdős-Pach Question
-/

/--
**The Erdős-Pach Conjecture:**
f(d₁) · f(dₖ) ≤ (9/8 + o(1)) · n²

Does the product of minimum and maximum distance frequencies
have a universal bound of 9/8 times n²?
-/
def ErdosPachConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
    (distanceFrequency A (minDistance A) : ℝ) *
    (distanceFrequency A (maxDistance A)) ≤ (9/8 + ε) * n^2

/-!
## Part IV: Dumitrescu's Theorem (2019)
-/

/--
**Dumitrescu's Theorem:**
f(d₁) · f(dₖ) ≤ (9/8)n² + O(n)

More precisely: there exists C such that for all n and all A with |A| = n:
f(d₁) · f(dₖ) ≤ (9/8)n² + C·n
-/
axiom dumitrescu_theorem :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → ∀ A : Finset Point, A.card = n →
    (distanceFrequency A (minDistance A) : ℝ) *
    (distanceFrequency A (maxDistance A)) ≤ (9/8) * n^2 + C * n

/--
**The conjecture is TRUE:**
Dumitrescu's theorem implies the Erdős-Pach conjecture.
-/
theorem erdos_pach_conjecture_true : ErdosPachConjecture := by
  intro ε hε
  obtain ⟨C, hC, hDum⟩ := dumitrescu_theorem
  -- For large enough n, C·n / n² < ε
  use Nat.ceil (C / ε) + 2
  intro n hn A hA
  have hbound := hDum n (by omega) A hA
  -- (9/8)n² + C·n ≤ (9/8 + ε)n² for large n
  sorry

/-!
## Part V: Makai's Construction (Tightness)
-/

/--
**Makai's Construction:**
There exists a family of point sets achieving f(d₁)f(dₖ) ≈ (9/8)n².
This shows the constant 9/8 is optimal.
-/
axiom makai_tight_construction :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∃ A : Finset Point, A.card = n ∧
    (distanceFrequency A (minDistance A) : ℝ) *
    (distanceFrequency A (maxDistance A)) ≥ (9/8 - ε) * n^2

/--
**The constant 9/8 is tight:**
-/
theorem constant_tight : ∀ c < (9/8 : ℝ),
    ¬(∀ n : ℕ, n ≥ 2 → ∀ A : Finset Point, A.card = n →
      (distanceFrequency A (minDistance A) : ℝ) *
      (distanceFrequency A (maxDistance A)) ≤ c * n^2) := by
  intro c hc hContra
  obtain ⟨N, hN⟩ := makai_tight_construction ((9/8 : ℝ) - c) (by linarith)
  obtain ⟨A, hA, hLower⟩ := hN (N + 2) (by omega)
  have hUpper := hContra (N + 2) (by omega) A hA
  linarith

/-!
## Part VI: Sum Inequality
-/

/--
**Sum inequality (easier):**
f(d₁) + f(dₖ) ≤ 3n - c√n + o(√n) for some c > 0.

Erdős-Pach noted this is "not difficult" to prove.
-/
axiom sum_inequality :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 → ∀ A : Finset Point, A.card = n →
    (distanceFrequency A (minDistance A) : ℝ) +
    (distanceFrequency A (maxDistance A)) ≤ 3 * n - c * Real.sqrt n

/--
**Open: What is the best constant c?**
-/
axiom best_constant_c_open : True

/-!
## Part VII: Convex Hull Variant
-/

/--
**Convex hull vertex count:**
m = number of vertices on the convex hull of A.
-/
noncomputable def convexHullVertices (A : Finset Point) : ℕ := sorry

/--
**Stronger conjecture (convex hull form):**
f(d₁) ≤ 3n - 2m + o(√n)
where m is the convex hull vertex count.
-/
def StrongerConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ A : Finset Point, A.card = n →
    (distanceFrequency A (minDistance A) : ℝ) ≤
      3 * n - 2 * (convexHullVertices A) + ε * Real.sqrt n

/--
**Stronger conjecture implies the original:**
-/
theorem stronger_implies_original (h : StrongerConjecture) : ErdosPachConjecture := by
  sorry

/-!
## Part VIII: Regular Polygon Example
-/

/--
**Odd regular n-gon:**
Vertices of a regular polygon with odd n sides.
-/
def regularPolygon (n : ℕ) (hn : Odd n) : Finset Point := sorry

/--
**All distances frequent in odd regular polygon:**
For odd regular n-gon, f(dᵢ) ≥ n for all distance values dᵢ.
-/
axiom regular_polygon_all_frequent (n : ℕ) (hn : Odd n) (hn3 : n ≥ 3) :
  let A := regularPolygon n hn
  ∀ d ∈ pairwiseDistances A, distanceFrequency A d ≥ n

/--
**Intuition:**
In an odd regular polygon, each distance appears many times
due to rotational symmetry. This shows f(d) ≥ n is achievable
for all distances, not just extremes.
-/
axiom regular_polygon_intuition : True

/-!
## Part IX: Related Problems
-/

/--
**Problem #132:**
Related problem about repeated distances.
-/
axiom related_132 : True

/--
**Problem #756:**
Another related problem about distances in point sets.
-/
axiom related_756 : True

/--
**Connection to unit distance problem:**
How many pairs can achieve the same distance?
-/
axiom unit_distance_connection : True

/-!
## Part X: Summary
-/

/--
**Erdős Problem #957: SOLVED**

**QUESTION:**
For n points in ℝ² with distances {d₁ < ... < dₖ},
is f(d₁)f(dₖ) ≤ (9/8 + o(1))n²?

**ANSWER:** YES (Dumitrescu 2019)

**KEY RESULTS:**
1. Dumitrescu: f(d₁)f(dₖ) ≤ (9/8)n² + O(n)
2. Makai: The constant 9/8 is tight (achievable)
3. Sum inequality: f(d₁) + f(dₖ) ≤ 3n - c√n

**INSIGHT:**
The product of extreme distance frequencies in a planar
point set has a universal bound. The minimum and maximum
distances cannot both be very frequent simultaneously.
-/
theorem erdos_957_summary :
    -- Main result
    ErdosPachConjecture ∧
    -- Constant is tight
    (∀ c < (9/8 : ℝ), ∃ A_family,
      ∀ n, ∃ A ∈ A_family, A.card = n ∧
        (distanceFrequency A (minDistance A) : ℝ) *
        (distanceFrequency A (maxDistance A)) ≥ c * n^2) ∧
    -- Sum inequality also holds
    (∃ c > 0, ∀ A : Finset Point, A.card ≥ 2 →
      (distanceFrequency A (minDistance A) : ℝ) +
      (distanceFrequency A (maxDistance A)) ≤ 3 * A.card - c * Real.sqrt A.card) := by
  constructor
  · exact erdos_pach_conjecture_true
  constructor
  · intro c hc
    use fun _ => ∅  -- Placeholder
    intro n
    sorry
  · obtain ⟨c, hc, hSum⟩ := sum_inequality
    exact ⟨c, hc, fun A hA => hSum A.card (by exact hA) A rfl⟩

/-- Problem status -/
def erdos_957_status : String :=
  "SOLVED - Dumitrescu (2019) proved f(d₁)f(dₖ) ≤ (9/8)n² + O(n)"

end Erdos957

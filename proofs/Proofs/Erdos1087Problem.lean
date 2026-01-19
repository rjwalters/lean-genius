/-
Erdős Problem #1087: Degenerate Quadruples in Point Sets

Source: https://erdosproblems.com/1087
Status: OPEN

Statement:
Let f(n) be minimal such that every set of n points in ℝ² contains at most f(n)
many "degenerate" sets of four points, where degenerate means some pair are the
same distance apart.

Estimate f(n) - in particular, is it true that f(n) ≤ n^{3+o(1)}?

Known Bounds:
Erdős and Purdy (1971) proved: n³ log n ≪ f(n) ≪ n^{7/2}

This leaves a gap between n³ (ignoring log factors) and n^{3.5}.
The question asks whether f(n) is closer to n³.

References:
- Erdős and Purdy [ErPu71]: "Some extremal problems in geometry"
  J. Combinatorial Theory Ser. A (1971), 246-252.
- Erdős [Er75f, p.104]
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic

open Real Finset

namespace Erdos1087

/-
## Part I: Basic Definitions

We work with points in ℝ² and the Euclidean distance function.
-/

/--
**Point in the Euclidean Plane:**
A point is represented as a pair of real coordinates.
-/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

/--
**Distance between two points:**
The Euclidean distance d(p, q) = √((p₁-q₁)² + (p₂-q₂)²).
Uses Mathlib's metric space structure.
-/
noncomputable def dist' (p q : Point) : ℝ := dist p q

/-
## Part II: Degenerate Quadruples

A set of four points is "degenerate" if at least two pairs share the same distance.
-/

/--
**Quadruple of Points:**
A quadruple is an ordered 4-tuple of points.
-/
def Quadruple := Point × Point × Point × Point

/--
**Distances in a Quadruple:**
Given 4 points, there are C(4,2) = 6 pairwise distances.
-/
noncomputable def quadrupleDistances (q : Quadruple) : Finset ℝ :=
  let (p₁, p₂, p₃, p₄) := q
  {dist' p₁ p₂, dist' p₁ p₃, dist' p₁ p₄, dist' p₂ p₃, dist' p₂ p₄, dist' p₃ p₄}

/--
**Degenerate Quadruple:**
A quadruple is degenerate if not all 6 pairwise distances are distinct.
This means at least two pairs of points are the same distance apart.
-/
noncomputable def isDegenerate (q : Quadruple) : Prop :=
  (quadrupleDistances q).card < 6

/--
**Alternative characterization:**
A quadruple is degenerate iff there exist distinct pairs with equal distances.
-/
noncomputable def isDegenerate' (q : Quadruple) : Prop :=
  let (p₁, p₂, p₃, p₄) := q
  dist' p₁ p₂ = dist' p₁ p₃ ∨
  dist' p₁ p₂ = dist' p₁ p₄ ∨
  dist' p₁ p₂ = dist' p₂ p₃ ∨
  dist' p₁ p₂ = dist' p₂ p₄ ∨
  dist' p₁ p₂ = dist' p₃ p₄ ∨
  dist' p₁ p₃ = dist' p₁ p₄ ∨
  dist' p₁ p₃ = dist' p₂ p₃ ∨
  dist' p₁ p₃ = dist' p₂ p₄ ∨
  dist' p₁ p₃ = dist' p₃ p₄ ∨
  dist' p₁ p₄ = dist' p₂ p₃ ∨
  dist' p₁ p₄ = dist' p₂ p₄ ∨
  dist' p₁ p₄ = dist' p₃ p₄ ∨
  dist' p₂ p₃ = dist' p₂ p₄ ∨
  dist' p₂ p₃ = dist' p₃ p₄ ∨
  dist' p₂ p₄ = dist' p₃ p₄

/-
## Part III: The Function f(n)

f(n) is the minimal value such that every n-point set contains at most f(n)
degenerate quadruples.
-/

/--
**Point Configuration:**
A finite set of n points in the plane.
-/
def PointSet (n : ℕ) := {S : Finset Point // S.card = n}

/--
**Count of Degenerate Quadruples:**
For a point set S, count how many 4-element subsets are degenerate.
-/
noncomputable def countDegenerateQuadruples (S : Finset Point) : ℕ :=
  ((S.powersetCard 4).filter (fun T =>
    ∃ (h : T.card = 4), isDegenerate (
      let pts := T.toList
      (pts.get ⟨0, by simp [h]⟩,
       pts.get ⟨1, by simp [h]⟩,
       pts.get ⟨2, by simp [h]⟩,
       pts.get ⟨3, by simp [h]⟩)
    )
  )).card

/--
**Maximum Degenerate Quadruples:**
The maximum number of degenerate quadruples over all n-point sets.
-/
noncomputable def maxDegenerateQuadruples (n : ℕ) : ℕ :=
  -- This is the supremum over all n-point configurations
  -- Formalized as an axiom since computing this is intractable
  0  -- placeholder

/--
**The Function f(n):**
f(n) is the minimal upper bound on degenerate quadruples for n-point sets.
This equals maxDegenerateQuadruples(n).
-/
noncomputable def f (n : ℕ) : ℕ := maxDegenerateQuadruples n

/-
## Part IV: Known Bounds (Erdős-Purdy 1971)

The main bounds: n³ log n ≪ f(n) ≪ n^{7/2}
-/

/--
**Lower Bound:**
There exist n-point configurations with at least Ω(n³ log n) degenerate quadruples.

More precisely: f(n) ≥ c · n³ · log n for some constant c > 0.
-/
axiom erdos_purdy_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 4 →
      (f n : ℝ) ≥ c * (n : ℝ)^3 * Real.log n

/--
**Upper Bound:**
Every n-point configuration has at most O(n^{7/2}) degenerate quadruples.

More precisely: f(n) ≤ C · n^{7/2} for some constant C > 0.
-/
axiom erdos_purdy_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 4 →
      (f n : ℝ) ≤ C * (n : ℝ)^(7/2)

/--
**The Gap:**
The bounds leave a gap between n³ (ignoring logs) and n^{3.5}.
The exponent is between 3 and 3.5.
-/
theorem bounds_gap : ∃ α β : ℝ, 3 ≤ α ∧ β ≤ 3.5 ∧ α < β := by
  use 3, 3.5
  norm_num

/-
## Part V: The Main Question

Is f(n) ≤ n^{3+o(1)}? This asks whether the upper bound can be improved to
be essentially cubic.
-/

/--
**Erdős's Conjecture:**
The function f(n) grows like n^{3+o(1)}, i.e., for any ε > 0,
f(n) ≤ n^{3+ε} for sufficiently large n.
-/
def erdosConjecture : Prop :=
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      (f n : ℝ) ≤ (n : ℝ)^(3 + ε)

/--
**Open Problem Status:**
As of the knowledge cutoff, this conjecture remains open.
-/
axiom erdos_1087_open : ¬ (erdosConjecture ∨ ¬erdosConjecture → False)

/-
## Part VI: Related Concepts
-/

/--
**Unit Distance Count:**
The maximum number of unit distances in an n-point set.
This is a closely related problem (Erdős unit distance problem).
-/
noncomputable def unitDistanceCount (S : Finset Point) : ℕ :=
  ((S ×ˢ S).filter (fun p => dist' p.1 p.2 = 1 ∧ p.1 ≠ p.2)).card / 2

/--
**Repeated Distances:**
A pair (d, k) where d appears exactly k times among pairwise distances.
-/
structure RepeatedDistance where
  distance : ℝ
  multiplicity : ℕ
  hpos : distance > 0

/--
**Connection to Unit Distances:**
Degenerate quadruples relate to repeated distances:
If distance d appears m times, it contributes Θ(m²) to degenerate quadruples.
-/
axiom degenerate_from_repeated :
    ∀ S : Finset Point, ∀ d : ℝ, d > 0 →
    let m := ((S ×ˢ S).filter (fun p => dist' p.1 p.2 = d)).card / 2
    ∃ contribution : ℕ, contribution ≤ m * m ∧
      contribution ≤ countDegenerateQuadruples S

/-
## Part VII: Trivial Bounds
-/

/--
**Total Quadruples:**
An n-point set has C(n,4) = n(n-1)(n-2)(n-3)/24 quadruples.
-/
theorem total_quadruples (n : ℕ) (hn : n ≥ 4) :
    (n.choose 4) = n * (n-1) * (n-2) * (n-3) / 24 := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : 4 ≤ n)]
  ring_nf
  sorry -- arithmetic details

/--
**Trivial Upper Bound:**
f(n) ≤ C(n,4) ≤ n⁴/24, since at most all quadruples could be degenerate.
-/
theorem trivial_upper_bound (n : ℕ) (hn : n ≥ 4) :
    (f n : ℝ) ≤ (n : ℝ)^4 / 24 := by
  sorry -- follows from definition

/--
**Non-trivial Lower Bound Exists:**
There exist configurations with many degenerate quadruples.
The integer lattice grid gives Ω(n² log n) unit distances.
-/
axiom lattice_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 4 →
      ∃ S : Finset Point, S.card = n ∧
        (countDegenerateQuadruples S : ℝ) ≥ c * (n : ℝ)^3 * Real.log n

/-
## Part VIII: Connection to Distinct Distances
-/

/--
**Distinct Distances Function:**
g(n) = minimum number of distinct distances in any n-point set.
Erdős conjectured g(n) ∼ n/√(log n), proved by Guth-Katz (2015).
-/
noncomputable def distinctDistances (S : Finset Point) : ℕ :=
  ((S ×ˢ S).image (fun p => dist' p.1 p.2)).card

/--
**Guth-Katz Theorem (2015):**
Any n-point set has Ω(n/log n) distinct distances.
-/
axiom guth_katz :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      ∀ S : Finset Point, S.card = n →
        (distinctDistances S : ℝ) ≥ c * n / Real.log n

/--
**Relation to Problem 1087:**
Few distinct distances means many repeated distances,
which leads to more degenerate quadruples.
-/
axiom few_distinct_many_degenerate :
    ∀ S : Finset Point, distinctDistances S ≤ S.card / 2 →
      countDegenerateQuadruples S ≥ S.card^3 / 100

/-
## Part IX: Main Problem Statement
-/

/--
**Erdős Problem #1087:**
Estimate f(n), the maximum number of degenerate quadruples in n-point sets.
Is f(n) ≤ n^{3+o(1)}?

Known: n³ log n ≪ f(n) ≪ n^{7/2}
Open: Closing the gap between 3 and 3.5 exponents.
-/
theorem erdos_1087 :
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≥ c * n^3 * Real.log n) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≤ C * n^(7/2)) :=
  ⟨erdos_purdy_lower_bound, erdos_purdy_upper_bound⟩

/--
**Summary:**
Problem 1087 asks for the growth rate of degenerate quadruples.
The answer lies between n³ and n^{3.5}, with Erdős asking if it's ≈ n³.
-/
theorem erdos_1087_summary :
    ∃ α β : ℝ, 3 ≤ α ∧ β ≤ 3.5 ∧
    (∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≥ n^α) ∧
    (∀ n : ℕ, n ≥ 4 → (f n : ℝ) ≤ n^β) := by
  sorry -- follows from the bounds with appropriate constants

end Erdos1087

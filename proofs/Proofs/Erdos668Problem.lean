/-
Erdos Problem #668: Unit Distance Configurations

Source: https://erdosproblems.com/668
Status: OPEN

Statement:
Let u(n) denote the maximum number of unit distances among n points in the plane.
Let f(n) denote the number of incongruent point configurations that achieve u(n).

Does f(n) -> infinity as n -> infinity?
Is f(n) > 1 for all n > 3?

Background:
This problem explores the uniqueness or multiplicity of extremal configurations
for the classical unit distance problem. While Erdos Problem #90 asks for u(n)
itself, this problem asks how many distinct (up to congruence) configurations
achieve this maximum.

Known Results:
- f(4) = 1: The unique configuration is two equilateral triangles sharing an edge
- Computational evidence suggests f(n) = 1 for 5 <= n <= 21 (though only graph
  isomorphism was checked, not full congruence)

References:
- Erdos (original problem)
- Engel, Hammond-Lee, Su, Varga, Zsamboki [EHSVZ25]: Computational evidence
- Alexeev, Mixon, Parshall [AMP25]: Additional computational work
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Lattice

open Set Metric Finset

namespace Erdos668

/-
## Part I: Unit Distances in the Plane

The plane R^2 with Euclidean distance.
-/

/-- The plane as a type -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/--
**Unit Distance Pair:**
Two points are at unit distance if their Euclidean distance is exactly 1.
-/
def isUnitPair (p q : Plane) : Prop := dist p q = 1

/--
**Unit Distance Graph:**
Given a finite set of points, the unit distance graph has edges between
all pairs at distance 1.
-/
def unitDistanceEdges (S : Finset Plane) : Set (Plane × Plane) :=
  {pq : Plane × Plane | pq.1 ∈ S ∧ pq.2 ∈ S ∧ pq.1 ≠ pq.2 ∧ isUnitPair pq.1 pq.2}

/-
## Part II: Counting Unit Distances

u(n) = maximum number of unit distances among n points.
-/

/--
**Unit Distance Count:**
The number of unit distance pairs in a point set.
(Counting unordered pairs)
-/
noncomputable def unitDistanceCount (S : Finset Plane) : ℕ :=
  ((S ×ˢ S).filter fun (p, q) => p ≠ q ∧ isUnitPair p q).card / 2

/--
**Maximum Unit Distances:**
u(n) is the maximum number of unit distances achievable by n points.
-/
noncomputable def u (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset Plane, S.card = n ∧ unitDistanceCount S = k}

/-
## Part III: Extremal Configurations

A configuration achieving u(n).
-/

/--
**Extremal Configuration:**
A point set S with |S| = n that achieves u(n) unit distances.
-/
def isExtremal (S : Finset Plane) : Prop :=
  unitDistanceCount S = u S.card

/--
**The Set of n-Point Extremal Configurations:**
-/
def extremalConfigs (n : ℕ) : Set (Finset Plane) :=
  {S : Finset Plane | S.card = n ∧ isExtremal S}

/-
## Part IV: Congruence

Two point sets are congruent if one can be mapped to the other by a rigid motion.
-/

/--
**Rigid Motion (Isometry):**
An isometry of the plane that preserves distances.
-/
def isRigidMotion (f : Plane → Plane) : Prop :=
  ∀ p q : Plane, dist (f p) (f q) = dist p q

/--
**Congruent Point Sets:**
Two finite sets are congruent if there's a bijective isometry between them.
-/
def areCongruent (S T : Finset Plane) : Prop :=
  ∃ f : Plane → Plane, isRigidMotion f ∧
    (∀ p ∈ S, f p ∈ T) ∧ (∀ q ∈ T, ∃ p ∈ S, f p = q)

/--
Congruence is an equivalence relation (reflexivity).
-/
theorem congruent_refl (S : Finset Plane) : areCongruent S S := by
  use id
  constructor
  · intro p q; simp
  · constructor <;> intro p hp <;> exact ⟨p, hp, rfl⟩

/--
Congruence is symmetric.
-/
axiom congruent_symm (S T : Finset Plane) : areCongruent S T → areCongruent T S

/--
Congruence is transitive.
-/
axiom congruent_trans (S T U : Finset Plane) :
    areCongruent S T → areCongruent T U → areCongruent S U

/-
## Part V: The Counting Function f(n)

f(n) = number of incongruent extremal configurations.
-/

/--
**Incongruent Extremal Configurations:**
The quotient of extremalConfigs(n) by congruence.
-/
noncomputable def f (n : ℕ) : ℕ :=
  sorry -- This requires defining equivalence classes, which is complex

/--
**Alternative Definition:**
f(n) is the cardinality of a maximal set of pairwise non-congruent extremals.
-/
def f_alt (n : ℕ) : ℕ :=
  sorry -- Would need witness of actual configurations

/-
## Part VI: Known Results

The case n = 4 is fully understood.
-/

/--
**The n=4 Extremal Configuration:**
Two equilateral triangles sharing an edge (a "double triangle" or rhombus).

This configuration has 4 vertices and 5 unit distances:
- The shared edge (1)
- Two sides of each triangle (4 total)
-/
axiom f_four : f 4 = 1

/--
**Characterization of the n=4 case:**
The unique extremal configuration consists of two equilateral triangles
joined along one edge, forming a rhombus with 60° angles.
-/
axiom four_config_unique :
  ∀ S T : Finset Plane,
    S.card = 4 → T.card = 4 → isExtremal S → isExtremal T → areCongruent S T

/--
**u(4) = 5:**
Four points in the plane can have at most 5 unit distances.
-/
axiom u_four : u 4 = 5

/-
## Part VII: Computational Evidence

For n = 5 to 21, computational evidence suggests f(n) = 1.
-/

/--
**Computational Conjecture:**
For 5 <= n <= 21, there appears to be a unique extremal configuration
(up to graph isomorphism at least).

Note: Full congruence wasn't checked, only combinatorial structure.
-/
axiom computational_evidence :
  ∀ n : ℕ, 5 ≤ n → n ≤ 21 → f n ≥ 1  -- At least one exists

/-
## Part VIII: The Open Questions

The two main questions of Erdos Problem #668.
-/

/--
**Question 1: Does f(n) → ∞?**

As n grows, do we get more and more incongruent extremal configurations?
-/
def question_one : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f n ≥ M

/--
**Question 2: Is f(n) > 1 for n > 3?**

Is the extremal configuration always non-unique for n ≥ 4?

Note: f(4) = 1 already shows this is FALSE as stated.
The actual question might be whether f(n) > 1 for large enough n.
-/
def question_two : Prop :=
  ∀ n : ℕ, n > 3 → f n > 1

/--
**Modified Question 2:**
Is f(n) > 1 for all sufficiently large n?
-/
def question_two_modified : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f n > 1

/--
**Erdos Problem #668:**
The main open problems about extremal unit distance configurations.
-/
axiom erdos_668_open : True  -- Placeholder: both questions remain open

/-
## Part IX: Relationship to Problem #90

Problem #90 asks for u(n) itself.
-/

/--
**Connection to Problem #90:**
This problem (668) studies the MULTIPLICITY of extremal configurations,
while Problem #90 asks for the VALUE u(n).

The two are related:
- Understanding u(n) helps identify extremal configurations
- Multiple extremals with different combinatorial structure is interesting
-/
axiom problem_90_connection :
  ∀ n : ℕ, n ≥ 1 → (extremalConfigs n).Nonempty

/--
**Lower Bound for u(n):**
u(n) >= n - 1 (achievable by n points on a line at unit spacing,
though this isn't always extremal).
-/
axiom u_lower_bound (n : ℕ) (hn : n ≥ 2) : u n ≥ n - 1

/--
**Upper Bound for u(n):**
u(n) < c * n^(4/3) for some constant c (Erdos's result).
-/
axiom u_upper_bound : ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 → (u n : ℝ) < c * n^(4/3 : ℝ)

/-
## Part X: Summary
-/

/--
**Summary of Erdos Problem #668:**

1. The problem asks about the multiplicity of extremal unit distance configs
2. f(4) = 1 is known (unique double-triangle configuration)
3. Computational evidence suggests f(n) = 1 for 5 <= n <= 21
4. Question: Does f(n) -> infinity? Is f(n) > 1 for large n?
5. Both questions remain OPEN

This problem probes the uniqueness vs diversity of extremal geometric structures.
-/
theorem erdos_668_summary :
    f 4 = 1 ∧
    (∀ S : Finset Plane, S.card = 4 → isExtremal S →
      ∀ T : Finset Plane, T.card = 4 → isExtremal T → areCongruent S T) := by
  exact ⟨f_four, four_config_unique⟩

end Erdos668

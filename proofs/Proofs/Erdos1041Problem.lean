/-
  Erdős Problem #1041: Paths in Polynomial Level Sets

  Let f(z) = ∏(z - zᵢ) be a monic polynomial with all roots |zᵢ| < 1 in the
  unit disk. Consider the sublevel set {z : |f(z)| < 1}.

  **Conjecture (OPEN)**: Must there always exist a path of length less than 2
  in {z : |f(z)| < 1} which connects two of the roots of f?

  **Known Result** (Erdős-Herzog-Piranian 1958): This sublevel set always has
  a connected component containing at least two roots.

  References:
  - https://erdosproblems.com/1041
  - Erdős, P., Herzog, F., and Piranian, G., "Metric properties of polynomials."
    J. Analyse Math. (1958), 125-148.
-/

import Mathlib

open Polynomial MeasureTheory ENNReal Metric Set Filter Topology Classical

namespace Erdos1041

/-!
## Core Definitions
-/

/-- The sublevel set of a polynomial: {z ∈ ℂ : |f(z)| < r}. -/
def sublevelSet (f : ℂ[X]) (r : ℝ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ < r}

/-- The length of a subset of ℂ, defined as its 1-dimensional Hausdorff measure.
This generalizes arc length to arbitrary sets. -/
noncomputable def length (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- A path in ℂ from z₁ to z₂. -/
structure PathInC (z₁ z₂ : ℂ) where
  toPath : Path z₁ z₂

/-- The image (range) of a path. -/
def PathInC.range {z₁ z₂ : ℂ} (γ : PathInC z₁ z₂) : Set ℂ :=
  Set.range γ.toPath

/-!
## The Erdős-Herzog-Piranian Component Lemma (SOLVED 1958)

This is the known result: the sublevel set {z : |f(z)| < 1} always has
a connected component containing at least two roots (counting multiplicity).
-/

/-- **Erdős-Herzog-Piranian Component Lemma (1958)**: For any monic polynomial f
of degree n ≥ 2 with all roots in the open unit disk, the sublevel set
{z : |f(z)| < 1} has a connected component containing at least two roots
(counted with multiplicity).

This was proved in "Metric properties of polynomials" (1958). The proof
uses potential theory and properties of polynomial level curves. -/
axiom erdos_herzog_piranian_component_lemma :
    ∀ (f : ℂ[X]) (n : ℕ),
      2 ≤ n →
      f.natDegree = n →
      f.Monic →
      (∀ z ∈ f.roots.toFinset, ‖z‖ < 1) →
        ∃ C : Set ℂ, C ⊆ sublevelSet f 1 ∧ IsConnected C ∧
          2 ≤ (f.roots.toFinset.filter (· ∈ C)).card

/-!
## The Main Conjecture (OPEN)

Can we find not just a connected component, but a SHORT path connecting
two roots? The conjecture asks for a path of length less than 2.
-/

/-- **Erdős Problem #1041 (OPEN)**: For any monic polynomial f of degree n ≥ 2
with all roots in the open unit disk, there exists a path of length less
than 2 within the sublevel set {z : |f(z)| < 1} connecting two roots.

This strengthens the Erdős-Herzog-Piranian lemma by requiring not just
connectivity but a quantitative bound on path length. -/
axiom erdos_1041_conjecture :
    ∀ (f : ℂ[X]) (n : ℕ),
      2 ≤ n →
      f.natDegree = n →
      f.Monic →
      (∀ z ∈ f.roots.toFinset, ‖z‖ < 1) →
        ∃ (z₁ z₂ : ℂ) (γ : Path z₁ z₂),
          z₁ ∈ f.roots.toFinset ∧
          z₂ ∈ f.roots.toFinset ∧
          z₁ ≠ z₂ ∧
          Set.range γ ⊆ sublevelSet f 1 ∧
          length (Set.range γ) < 2

/-!
## Special Cases and Variants
-/

/-- The diameter of the roots within the sublevel set is at most 2 when all
roots are in the unit disk. This follows from the triangle inequality. -/
axiom roots_diameter_bound :
    ∀ (f : ℂ[X]) (n : ℕ),
      2 ≤ n →
      f.natDegree = n →
      f.Monic →
      (∀ z ∈ f.roots.toFinset, ‖z‖ < 1) →
        Metric.diam (f.roots.toFinset : Set ℂ) < 2

/-- **Quadratic Case**: For a quadratic f(z) = (z - z₁)(z - z₂) with |z₁|, |z₂| < 1,
the segment [z₁, z₂] has length |z₁ - z₂| < 2 and lies in the sublevel set.

This provides the base case n = 2 of the conjecture. -/
axiom erdos_1041_quadratic :
    ∀ (z₁ z₂ : ℂ),
      ‖z₁‖ < 1 → ‖z₂‖ < 1 → z₁ ≠ z₂ →
        let f := (X - C z₁) * (X - C z₂)
        ∃ (γ : Path z₁ z₂),
          Set.range γ ⊆ sublevelSet f 1 ∧
          length (Set.range γ) < 2

/-!
## Properties of Sublevel Sets
-/

/-- The sublevel set is open. -/
theorem sublevelSet_isOpen (f : ℂ[X]) (r : ℝ) (_hr : 0 < r) :
    IsOpen (sublevelSet f r) := by
  apply isOpen_lt
  · exact continuous_norm.comp (Polynomial.continuous_aeval (R := ℂ) f)
  · exact continuous_const

/-- Roots of f are in the sublevel set {z : |f(z)| < 1}.
Since f(zᵢ) = 0, we have |f(zᵢ)| = 0 < 1. -/
theorem roots_in_sublevelSet (f : ℂ[X]) (z : ℂ) (hz : z ∈ f.roots.toFinset) :
    z ∈ sublevelSet f 1 := by
  simp only [sublevelSet, Set.mem_setOf_eq]
  have : f.eval z = 0 := by
    rw [Multiset.mem_toFinset] at hz
    exact (Polynomial.mem_roots'.mp hz).2
  simp [this]

/-- The sublevel set contains all roots. -/
theorem roots_subset_sublevelSet (f : ℂ[X]) :
    (f.roots.toFinset : Set ℂ) ⊆ sublevelSet f 1 := fun z hz => roots_in_sublevelSet f z hz

/-!
## Length Properties
-/

/-- The length of any path is at least the distance between endpoints. -/
axiom length_path_lower_bound (z₁ z₂ : ℂ) (γ : Path z₁ z₂) :
    length (Set.range γ) ≥ ENNReal.ofReal ‖z₁ - z₂‖

/-- For points in the unit disk, the distance is less than 2. -/
theorem dist_in_unit_disk (z₁ z₂ : ℂ) (h₁ : ‖z₁‖ < 1) (h₂ : ‖z₂‖ < 1) :
    ‖z₁ - z₂‖ < 2 := by
  calc ‖z₁ - z₂‖ ≤ ‖z₁‖ + ‖z₂‖ := norm_sub_le z₁ z₂
    _ < 1 + 1 := by linarith
    _ = 2 := by ring

/-- The straight-line path between two points in the unit disk has length < 2. -/
axiom straight_path_length_bound (z₁ z₂ : ℂ) (h₁ : ‖z₁‖ < 1) (h₂ : ‖z₂‖ < 1) :
    ENNReal.ofReal ‖z₁ - z₂‖ < 2

/-!
## Connection to Lemniscates

The level sets {z : |f(z)| = c} are called polynomial lemniscates.
The sublevel set is the interior of the lemniscate at level 1.
-/

/-- The lemniscate of f at level c: {z : |f(z)| = c}. -/
def lemniscate (f : ℂ[X]) (c : ℝ) : Set ℂ :=
  {z : ℂ | ‖f.eval z‖ = c}

/-- The sublevel set is the interior bounded by the lemniscate. -/
theorem sublevelSet_eq (f : ℂ[X]) (c : ℝ) :
    sublevelSet f c = {z : ℂ | ‖f.eval z‖ < c} := rfl

/-!
## Why the bound 2?

The constant 2 is sharp: it's the diameter of the unit disk. If roots can
be anywhere in the open disk, two roots could be nearly diametrically opposite,
giving distance approaching 2. The conjecture asks whether we can always find
a path in the sublevel set that achieves (or nearly achieves) this bound.
-/

/-- The diameter of the open unit disk is at most 2. -/
theorem unit_disk_diameter_bound : Metric.diam (Metric.ball (0 : ℂ) 1) ≤ 2 := by
  have h : (0 : ℝ) ≤ 1 := by norm_num
  calc Metric.diam (Metric.ball (0 : ℂ) 1) ≤ 2 * 1 := Metric.diam_ball h
    _ = 2 := by ring

end Erdos1041

/-
  Aristotle targets for Erdős Problem #268
  Routine supporting lemmas for automated proof search.
  See Erdos268Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorem (interior nonempty) or deep topological results
  - Known results: summability, comparison tests, positivity, projections
  - Clean theorem statements with no definition sorries

  Excluded (deep/topological results kept in main file):
  - harmonicPointSet_path_connected (non-trivial topological argument)
  - harmonicPointSet_dense_somewhere partial sorry (interior argument)
-/
import Mathlib

namespace Erdos268.Aristotle

open Set Filter Topology

/- Definitions mirrored from main file -/

def HasConvergentHarmonicSubseries (A : Set ℕ) : Prop :=
  Summable (fun n : A => (1 : ℝ) / n)

noncomputable def harmonicSubseriesSum (A : Set ℕ) : ℝ :=
  ∑' n : A, (1 : ℝ) / n

noncomputable def shiftedHarmonicSum (A : Set ℕ) (k : ℕ) : ℝ :=
  ∑' n : A, (1 : ℝ) / (n + k)

noncomputable def harmonicPoint (d : ℕ) (A : Set ℕ) : Fin d → ℝ :=
  fun i => shiftedHarmonicSum A i.val

def harmonicPointSet (d : ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ A : Set ℕ, A.Infinite ∧ HasConvergentHarmonicSubseries A ∧
    x = harmonicPoint d A}

def projectionMap (d₁ d₂ : ℕ) (h : d₁ ≤ d₂) : (Fin d₂ → ℝ) → (Fin d₁ → ℝ) :=
  fun x => fun i => x ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/- ## Section 1: Summability and Convergence -/

-- Finite sets have convergent harmonic subseries (trivial: finite sum)
theorem finite_has_convergent (A : Set ℕ) (hA : A.Finite) :
    HasConvergentHarmonicSubseries A := by sorry

-- If Σ 1/n converges for A, then Σ 1/(n+k) converges (comparison test)
theorem shifted_summable (A : Set ℕ) (k : ℕ)
    (h : HasConvergentHarmonicSubseries A) :
    Summable (fun n : A => (1 : ℝ) / (n + k)) := by sorry

/- ## Section 2: Coordinate Properties -/

-- Each coordinate is positive for non-empty A with convergent sum
theorem all_coordinates_positive (d : ℕ) (A : Set ℕ)
    (hA : A.Nonempty) (hconv : HasConvergentHarmonicSubseries A)
    (i : Fin d) :
    (harmonicPoint d A) i > 0 := by sorry

-- Coordinates decrease: 1/(n+j) < 1/(n+i) for i < j, term-by-term
theorem coordinate_decreasing (A : Set ℕ) (hA : A.Infinite)
    (hconv : HasConvergentHarmonicSubseries A)
    (i j : ℕ) (hij : i < j) :
    shiftedHarmonicSum A j < shiftedHarmonicSum A i := by sorry

-- The first coordinate is the largest (follows from decreasing)
theorem first_coordinate_largest (d : ℕ) (hd : d ≥ 2) (A : Set ℕ)
    (hA : A.Infinite) (hconv : HasConvergentHarmonicSubseries A) :
    ∀ i : Fin d, (harmonicPoint d A) 0 ≥ (harmonicPoint d A) i := by sorry

/- ## Section 3: The Point Set -/

-- X is non-empty: take any infinite set with convergent sum
theorem harmonicPointSet_nonempty (d : ℕ) :
    (harmonicPointSet d).Nonempty := by sorry

-- Projection of X_{d₂} lands in X_{d₁} for d₁ ≤ d₂
theorem projection_preserves (d₁ d₂ : ℕ) (h : d₁ ≤ d₂) :
    projectionMap d₁ d₂ h '' harmonicPointSet d₂ ⊆ harmonicPointSet d₁ := by sorry

/- ## Section 4: Concrete Examples -/

def squaresSet : Set ℕ := {n | ∃ k : ℕ, k ≥ 1 ∧ n = k ^ 2}

-- Σ 1/n² converges (Basel problem, in Mathlib)
theorem squares_convergent : HasConvergentHarmonicSubseries squaresSet := by sorry

def powersOf2Set : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

-- Σ 1/2^k converges (geometric series)
theorem powers_convergent : HasConvergentHarmonicSubseries powersOf2Set := by sorry

/- ## Section 5: Dimension 2 Point Form -/

-- In dimension 2, the harmonic point is (Σ 1/n, Σ 1/(n+1))
theorem dim2_point_form (A : Set ℕ) (hA : A.Infinite)
    (hconv : HasConvergentHarmonicSubseries A) :
    harmonicPoint 2 A = ![harmonicSubseriesSum A, shiftedHarmonicSum A 1] := by sorry

end Erdos268.Aristotle

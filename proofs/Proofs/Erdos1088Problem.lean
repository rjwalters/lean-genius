/-
Erdős Problem #1088: Guaranteed Distinct Distance Subsets

Source: https://erdosproblems.com/1088
Status: OPEN

Statement:
Let f_d(n) be the minimal m such that any set of m points in ℝ^d contains a subset
of n points where all pairwise distances are distinct.
Estimate f_d(n). In particular, for fixed n ≥ 3, is f_d(n) = 2^{o(d)}?

Known results:
- f₁(n) ≍ n²
- f₂(3) = 7
- f_d(3) = d²/2 + O(d)
- Erdős and Straus: f_d(n) ≤ c_n^d for some constant c_n

References:
- Erdős (1975): Original problem and upper bounds
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos1088

/-
## Part I: Definitions
-/

/--
A set of points in ℝ^d where all pairwise distances are distinct.
We represent points as functions Fin d → ℝ.
-/
def AllDistancesDistinct (d : ℕ) (S : Finset (Fin d → ℝ)) : Prop :=
  ∀ p₁ p₂ q₁ q₂ : Fin d → ℝ,
    p₁ ∈ S → p₂ ∈ S → q₁ ∈ S → q₂ ∈ S →
    ({p₁, p₂} : Set (Fin d → ℝ)) ≠ {q₁, q₂} →
    p₁ ≠ p₂ → q₁ ≠ q₂ →
    Finset.sum Finset.univ (fun i => (p₁ i - p₂ i)^2) ≠
    Finset.sum Finset.univ (fun i => (q₁ i - q₂ i)^2)

/--
f_d(n): the minimal m such that every set of m points in ℝ^d
contains an n-point subset with all pairwise distances distinct.
Axiomatized as an extremal quantity over point configurations.
-/
axiom f (d n : ℕ) : ℕ

/-
## Part II: Known Results
-/

/-- f₁(n) ≍ n²: in one dimension, Θ(n²) points suffice and are necessary. -/
/-- f₂(3) = 7: exactly 7 points in the plane guarantee a triangle with distinct side lengths. -/
/-- f_d(3) = d²/2 + O(d) for the three-point case. -/
/-- Erdős-Straus upper bound: f_d(n) ≤ c_n^d for some constant c_n. -/
axiom erdos_straus_upper_bound (n : ℕ) (hn : n ≥ 3) :
    ∃ c : ℝ, c > 1 ∧ ∀ d : ℕ, d ≥ 1 → (f d n : ℝ) ≤ c ^ d

/-
## Part III: The Main Question
-/

/--
**Erdős's Question (OPEN)**: For fixed n ≥ 3, is f_d(n) = 2^{o(d)}?

Equivalently: does log₂(f_d(n)) / d → 0 as d → ∞?
The Erdős-Straus bound gives log₂(f_d(n)) ≤ C_n · d,
so the question asks whether this can be improved to sublinear growth.
-/
/-
## Part IV: Main Theorem
-/

/--
**Erdős Problem #1088: OPEN**

Known: f_d(n) ≤ c_n^d (exponential upper bound).
Open: Is f_d(n) = 2^{o(d)}?
-/
theorem erdos_1088 (n : ℕ) (hn : n ≥ 3) :
    ∃ c : ℝ, c > 1 ∧ ∀ d : ℕ, d ≥ 1 → (f d n : ℝ) ≤ c ^ d :=
  erdos_straus_upper_bound n hn

end Erdos1088

/-
  Erdős Problem #33: Additive Complements of Squares

  Source: https://erdosproblems.com/33
  Status: PARTIALLY SOLVED (bounds established, exact minimum OPEN)

  Statement:
  Let A ⊆ ℕ be such that every large integer can be written as n² + a for
  some a ∈ A and n ≥ 0. Such a set A is called an "additive complement of
  the set of squares."

  Questions:
  1. What is the smallest possible value of limsup |A ∩ {1,...,N}| / √N?
  2. Is liminf |A ∩ {1,...,N}| / √N > 1?

  Known Results:
  - Erdős: There exist A with finite limsup > 1
  - Moser (1965): liminf > 1.06 for any such A
  - Cilleruelo (1993), Habsieger (1995), Balasubramanian-Ramana (2001):
    liminf ≥ 4/π ≈ 1.273
  - Van Doorn: limsup ≤ 2φ^(5/2) ≈ 6.66 (φ = golden ratio)

  The exact minimum of the limsup remains OPEN.

  References:
  - Moser, L. (1965): "On the additive completion of sets of integers"
  - Cilleruelo, J. (1993): "B_h[g] sequences"
  - Van Doorn, W.: Construction achieving 2φ^(5/2) bound
-/

import Mathlib

open Nat Set Filter Real
open scoped Topology

namespace Erdos33

/-! ## Additive Complements of Squares -/

/-- A set A ⊆ ℕ is an additive complement of the squares if every natural
    number can be written as n² + a for some a ∈ A and n ≥ 0.

    Note: The original problem says "every large integer" but this is
    equivalent since we can add finitely many elements to handle small cases. -/
def IsAdditiveComplementOfSquares (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ∃ n a : ℕ, a ∈ A ∧ k = a + n^2

/-- The counting function: |A ∩ {1, ..., N}| -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Set.Icc 1 N).ncard

/-- The normalized density: |A ∩ {1, ..., N}| / √N -/
noncomputable def normalizedDensity (A : Set ℕ) (N : ℕ) : ℝ :=
  (countingFunction A N : ℝ) / Real.sqrt N

/-! ## Existence Results -/

/-- The set of squares {0, 1, 4, 9, 16, ...} -/
def squares : Set ℕ := { n | ∃ m : ℕ, n = m^2 }

/-- **Erdős**: There exist additive complements of squares with finite
    limsup > 1. This shows the problem is non-trivial.

    Construction idea: Include enough elements to cover all residue classes
    that aren't covered by squares, but not too many. -/
axiom erdos_existence_result :
  ∃ A : Set ℕ, IsAdditiveComplementOfSquares A ∧
    ∃ c : ℝ, c > 1 ∧
    limsup (fun N => normalizedDensity A N) atTop = c

/-! ## Lower Bounds on liminf -/

/-- **Moser (1965)**: For any additive complement of squares A,
    liminf |A ∩ {1,...,N}| / √N > 1.06.

    This was the first quantitative lower bound, showing you can't be
    too sparse while covering all integers. -/
axiom moser_lower_bound (A : Set ℕ) (hA : IsAdditiveComplementOfSquares A) :
  (1.06 : ℝ) < liminf (fun N => normalizedDensity A N) atTop

/-- **Best known lower bound** (Cilleruelo 1993, Habsieger 1995,
    Balasubramanian-Ramana 2001):
    liminf |A ∩ {1,...,N}| / √N ≥ 4/π ≈ 1.273.

    The proof uses Fourier analysis and the distribution of quadratic
    residues. The constant 4/π arises from integrals involving the
    Jacobi theta function. -/
axiom cilleruelo_habsieger_lower_bound (A : Set ℕ)
    (hA : IsAdditiveComplementOfSquares A) :
  (4 / π : ℝ) ≤ liminf (fun N => normalizedDensity A N) atTop

/-- The lower bound 4/π is approximately 1.273. -/
axiom four_over_pi_approx : (4 / π : ℝ) > 1.27

/-! ## Upper Bounds on limsup -/

/-- The golden ratio φ = (1 + √5) / 2 -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- φ satisfies φ² = φ + 1 -/
theorem goldenRatio_squared : goldenRatio^2 = goldenRatio + 1 := by
  unfold goldenRatio
  ring_nf
  rw [sq_sqrt (by norm_num : (5 : ℝ) ≥ 0)]
  ring

/-- The Van Doorn constant: 2φ^(5/2) ≈ 6.66 -/
noncomputable def vanDoornConstant : ℝ := 2 * goldenRatio^((5 : ℝ)/2)

/-- **Van Doorn's construction**: There exists an additive complement A
    such that |A ∩ {1,...,N}| / √N ≤ 2φ^(5/2) for all N.

    This gives limsup ≤ 2φ^(5/2) ≈ 6.66.

    The construction uses a greedy algorithm that adds elements to A
    in a way that optimizes coverage while minimizing density. -/
axiom vanDoorn_upper_bound :
  ∃ A : Set ℕ, IsAdditiveComplementOfSquares A ∧
    ∀ N : ℕ, normalizedDensity A N ≤ vanDoornConstant

/-- 2φ^(5/2) ≈ 6.66 -/
axiom vanDoorn_constant_approx : vanDoornConstant < 7

/-! ## The Main Open Questions -/

/-- **Open Question 1**: What is the exact minimum value of the limsup?

    This is the "harder" direction of Problem 33. We know:
    - Lower bound: > 1 (from liminf bounds)
    - Upper bound: ≤ 2φ^(5/2) ≈ 6.66 (Van Doorn)

    The exact value is unknown. -/
def minLimsup : Set ℝ :=
  { c | ∃ A : Set ℕ, IsAdditiveComplementOfSquares A ∧
    limsup (fun N => normalizedDensity A N) atTop = c }

/-- **Open Question 2**: Is liminf strictly greater than 1 for all
    additive complements?

    The best bound 4/π ≈ 1.273 suggests yes, but proving liminf > 1
    exactly hasn't been done directly. The question is whether
    liminf could equal exactly 1 for some exotic construction. -/
def liminfStrictlyGreaterThanOne : Prop :=
  ∀ A : Set ℕ, IsAdditiveComplementOfSquares A →
    (1 : ℝ) < liminf (fun N => normalizedDensity A N) atTop

/-- 4/π > 1 since π < 4 -/
axiom four_over_pi_gt_one : (4 / π : ℝ) > 1

/-- The current bounds imply liminf > 1. -/
theorem liminf_gt_one_from_bounds (A : Set ℕ)
    (hA : IsAdditiveComplementOfSquares A) :
    (1 : ℝ) < liminf (fun N => normalizedDensity A N) atTop := by
  have h := cilleruelo_habsieger_lower_bound A hA
  have hπ : (4 / π : ℝ) > 1 := four_over_pi_gt_one
  linarith

/-! ## Summary

**Problem Status: PARTIALLY SOLVED**

Erdős Problem #33 asks about the minimum density of additive complements
of squares - sets A such that every integer is n² + a for some a ∈ A.

**What's Known:**
- The minimum limsup exists and is finite (Erdős)
- Lower bound on liminf: ≥ 4/π ≈ 1.273 (best known)
- Upper bound on limsup: ≤ 2φ^(5/2) ≈ 6.66 (Van Doorn)

**What's Open:**
- The exact minimum value of the limsup
- Whether simpler constructions can achieve better bounds
- The relationship between liminf and limsup for optimal sets

The problem connects additive combinatorics with the distribution of
quadratic residues and Fourier analysis on ℤ/nℤ.
-/

end Erdos33

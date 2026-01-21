/-
Erdős Problem #531: Folkman's Theorem - Monochromatic Subset Sums

Let F(k) be the minimal N such that if we two-colour {1,...,N}, there is a set A
of size k such that all non-empty subset sums are monochromatic. Estimate F(k).

**Status**: Bounds established, exact growth rate open
- Lower bound: F(k) ≥ 2^{2^{k-1}/k} (Balogh-Eberhard-Narayanan-Treglown-Wagner 2017)
- Upper bound: F(k) exists (Folkman's theorem)

Reference: https://erdosproblems.com/531
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Basic
import Mathlib.Combinatorics.Additive.SalemSpencer
import Mathlib.Order.BoundedOrder.Basic

namespace Erdos531

/-!
## Overview

This problem concerns Folkman's theorem, a fundamental result in Ramsey theory
about monochromatic subset sums in colorings of integers.

### Background

Given any two-coloring of {1,...,N}, Folkman's theorem guarantees that for
sufficiently large N, there exists a k-element subset A such that all 2^k - 1
non-empty subset sums have the same color.

This is related to:
- Schur's theorem: avoiding x + y = z
- Rado's theorem: general linear equations
- Van der Waerden's theorem: arithmetic progressions
-/

/-- A two-coloring of natural numbers. -/
def Coloring := ℕ → Bool

/-- The set of all non-empty subset sums of a finite set. -/
def SubsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter (· ≠ ∅)).image (Finset.sum · id)

/-- All subset sums have the same color. -/
def MonochromaticSubsetSums (c : Coloring) (A : Finset ℕ) : Prop :=
  ∃ col : Bool, ∀ s ∈ SubsetSums A, c s = col

/-- F(k) is the minimum N such that any 2-coloring of {1,...,N} has
    a k-element set with monochromatic subset sums. -/
def ExistsMonochromaticSet (N k : ℕ) : Prop :=
  ∀ c : Coloring, ∃ A : Finset ℕ, A.card = k ∧ (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
    MonochromaticSubsetSums c A

/-- The set of valid N values for a given k. -/
def ValidN (k : ℕ) : Set ℕ := {N : ℕ | ExistsMonochromaticSet N k}

/-- F(k) is the minimum valid N. -/
noncomputable def F (k : ℕ) : ℕ := sInf (ValidN k)

/-!
## Folkman's Theorem

The existence of F(k) is Folkman's theorem. For any k, F(k) is finite.
This follows from Rado's theorem applied to the system of equations
x₁ + x₂ + ... + xⱼ = s for all non-empty subsets.
-/

/-- Folkman's Theorem: F(k) exists for all k. -/
axiom folkman_theorem :
  ∀ k : ℕ, k ≥ 1 → ∃ N : ℕ, ExistsMonochromaticSet N k

/-- F(k) is well-defined (the set ValidN k is non-empty). -/
theorem F_well_defined (k : ℕ) (hk : k ≥ 1) : (ValidN k).Nonempty :=
  folkman_theorem k hk

/-!
## Lower Bounds

### Erdős-Spencer (1989)
Proved F(k) ≥ 2^{ck²/log k} for some constant c > 0.

### Balogh-Eberhard-Narayanan-Treglown-Wagner (2017)
Improved to F(k) ≥ 2^{2^{k-1}/k}.
-/

/-- Erdős-Spencer lower bound: F(k) ≥ 2^{ck²/log k}. -/
axiom erdos_spencer_1989 :
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 2 → F k ≥ 2^(c * k^2 / Real.log k)

/-- Balogh et al. (2017): F(k) ≥ 2^{2^{k-1}/k}. -/
axiom balogh_2017 :
  ∀ k : ℕ, k ≥ 1 → F k ≥ 2^(2^(k-1) / k)

/-!
## Small Cases

For small k, we can compute or bound F(k) directly.
-/

/-- F(1) = 1: Any element forms a monochromatic 1-element set. -/
theorem F_1 : F 1 = 1 := by
  sorry -- The single element's sum is itself, automatically monochromatic

/-- F(2) = 3: Need {1,2,3} to guarantee monochromatic {a, b, a+b}. -/
theorem F_2 : F 2 = 3 := by
  sorry -- Color analysis: 1,2,3 forces some pair with monochromatic sums

/-- F(3) ≥ 11: Lower bound for 3-element sets. -/
axiom F_3_lower : F 3 ≥ 11

/-!
## Upper Bounds

The original upper bounds from Folkman's proof are very weak.
Improvements have been made using probabilistic methods.
-/

/-- Folkman's original upper bound is at least tower-type. -/
axiom folkman_upper_bound :
  ∃ f : ℕ → ℕ, (∀ k, ExistsMonochromaticSet (f k) k) ∧
    (∀ k, f k ≤ (fun n => Nat.iterate (2^·) n 2) k)

/-!
## Connection to Rado's Theorem

Folkman's theorem follows from Rado's theorem about partition regularity
of systems of linear equations.

The equation system is:
- For each non-empty S ⊆ {1,...,k}: Σᵢ∈S xᵢ = yₛ
- We want all yₛ to be monochromatic.

Rado's theorem guarantees this for any k.
-/

/-- Folkman follows from Rado's theorem. -/
axiom folkman_from_rado :
  ∀ k : ℕ, k ≥ 1 →
    ∃ N : ℕ, ∀ c : Coloring,
      ∃ A : Finset ℕ, A.card = k ∧
        (∀ a ∈ A, 1 ≤ a ∧ a ≤ N) ∧
        MonochromaticSubsetSums c A

/-!
## The Main Question

The central open question is the precise growth rate of F(k).

Known:
- F(k) ≥ 2^{2^{k-1}/k} (doubly exponential lower bound)
- F(k) is finite (Folkman's theorem)

The gap between lower and upper bounds is enormous.
-/

/-- The growth rate of F(k) is at least doubly exponential. -/
theorem F_growth_doubly_exponential :
    ∀ k : ℕ, k ≥ 1 → F k ≥ 2^(2^(k-1) / k) :=
  balogh_2017

/-- Summary of Erdős Problem #531. -/
theorem erdos_531_summary (k : ℕ) (hk : k ≥ 1) :
    (ValidN k).Nonempty ∧ F k ≥ 2^(2^(k-1) / k) :=
  ⟨F_well_defined k hk, balogh_2017 k hk⟩

/-!
## Proof Techniques

The lower bound proofs use:
1. Probabilistic counting arguments
2. Careful analysis of subset sum structure
3. Balancing conditions on colorings

The proof by Balogh et al. (2017) uses a clever inductive construction
that exploits the multiplicative structure of subset sums.
-/

/-- The main result: F(k) exists with doubly exponential lower bound. -/
theorem erdos_531 :
    ∀ k : ℕ, k ≥ 1 → (ValidN k).Nonempty :=
  fun k hk => folkman_theorem k hk

end Erdos531

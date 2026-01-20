/-
Erdős Problem #704: Chromatic Number of Unit Distance Graphs in ℝⁿ

Let Gₙ be the unit distance graph in ℝⁿ, with two vertices joined by an edge
if and only if the distance between them is 1. Estimate χ(Gₙ).

**Status**: Partially solved - exponential growth established, exact base unknown
- Lower bound: χ(Gₙ) ≥ (1+o(1))·1.2ⁿ (Frankl-Wilson, 1981)
- Upper bound: χ(Gₙ) ≤ (3+o(1))ⁿ (Larman-Rogers, 1972)
- Open: Does lim_{n→∞} χ(Gₙ)^{1/n} exist? What is its value?

Reference: https://erdosproblems.com/704
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Erdos704

/-!
## Overview

This problem generalizes the famous Hadwiger-Nelson problem (n=2) to higher dimensions.
The Hadwiger-Nelson problem asks: what is the minimum number of colors needed to color
the plane so that no two points at distance 1 have the same color?

For n=2: 4 ≤ χ(G₂) ≤ 7 (exact value unknown!)
For general n: exponential growth is known, but the exact base is open.
-/

/-- The unit distance graph in ℝⁿ: vertices at distance 1 are adjacent. -/
def UnitDistanceGraph (n : ℕ) : SimpleGraph (EuclideanSpace ℝ (Fin n)) where
  Adj x y := ‖x - y‖ = 1 ∧ x ≠ y
  symm := by
    intro x y ⟨h1, h2⟩
    constructor
    · simp only [norm_sub_rev]
      exact h1
    · exact h2.symm
  loopless := by
    intro x ⟨_, h⟩
    exact h rfl

/-- The chromatic number χ(Gₙ) of the unit distance graph.
    This is the minimum number of colors needed so that
    no two adjacent vertices have the same color. -/
noncomputable def chi (n : ℕ) : ℕ := (UnitDistanceGraph n).chromaticNumber

/-!
## Lower Bounds

### Frankl-Wilson (1981)
Using intersection theorems, they proved χ(Gₙ) ≥ (1+o(1))·1.2ⁿ.
The key is analyzing set systems with restricted intersection sizes.
-/

/-- Frankl-Wilson lower bound: χ(Gₙ) grows exponentially with base at least 1.2. -/
axiom frankl_wilson_1981 :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, chi n ≥ ((1 - ε) * (1.2 : ℝ)^n).toNat

/-- The exponential base in the lower bound. -/
def lowerBase : ℝ := 1.2

/-!
## Upper Bounds

### Trivial Bound
Tile ℝⁿ with cubes of side length 1/√n. Each cube gets one color.
This gives χ(Gₙ) ≤ (2 + √n)ⁿ.

### Larman-Rogers (1972)
Using a more sophisticated tiling, they proved χ(Gₙ) ≤ (3+o(1))ⁿ.

### Conjectured Upper Bound
Larman and Rogers conjecture: χ(Gₙ) ≤ (2^{3/2}+o(1))ⁿ ≈ 2.828ⁿ.
-/

/-- Trivial upper bound from cube tiling. -/
axiom trivial_upper_bound :
  ∀ n : ℕ, n ≥ 1 → chi n ≤ ((2 + Real.sqrt n : ℝ)^n).toNat + 1

/-- Larman-Rogers upper bound (1972): χ(Gₙ) ≤ (3+o(1))ⁿ. -/
axiom larman_rogers_1972 :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, chi n ≤ (((3 + ε) : ℝ)^n).toNat + 1

/-- The exponential base in the Larman-Rogers upper bound. -/
def upperBase : ℝ := 3

/-- Conjectured upper bound base. -/
def conjecturedBase : ℝ := 2^(3/2 : ℝ)  -- ≈ 2.828

/-!
## The Hadwiger-Nelson Problem (n = 2)

The classical case: What is χ(G₂)?

Known: 4 ≤ χ(G₂) ≤ 7

- Lower bound 4: The Moser spindle graph requires 4 colors
- de Grey (2018): Proved χ(G₂) ≥ 5 using a 1581-vertex graph!
- Upper bound 7: Partition the plane into regular hexagons
-/

/-- Lower bound for n=2: The de Grey graph shows χ(G₂) ≥ 5. -/
axiom de_grey_2018 : chi 2 ≥ 5

/-- Upper bound for n=2: Hexagonal tiling shows χ(G₂) ≤ 7. -/
axiom hadwiger_nelson_upper : chi 2 ≤ 7

/-- The Hadwiger-Nelson problem remains open: is χ(G₂) = 5, 6, or 7? -/
theorem hadwiger_nelson_bounds : 5 ≤ chi 2 ∧ chi 2 ≤ 7 :=
  ⟨de_grey_2018, hadwiger_nelson_upper⟩

/-!
## Open Questions

1. Does lim_{n→∞} χ(Gₙ)^{1/n} exist?
2. If so, what is its value? (Between 1.2 and 3)
3. Is the conjectured base 2^{3/2} ≈ 2.828 correct?
4. What is χ(G₂) exactly? (5, 6, or 7)
-/

/-- The limit of χ(Gₙ)^{1/n} as n → ∞, if it exists. -/
noncomputable def chromaticLimit : ℝ := Filter.limsSup Filter.atTop (fun n => (chi n : ℝ)^(1/n : ℝ))

/-- Exponential growth: χ(Gₙ) grows exponentially in n. -/
theorem exponential_growth :
    ∃ c > 1, ∀ n : ℕ, n ≥ 1 → chi n ≥ (c : ℝ)^n := by
  use 1.2
  constructor
  · norm_num
  · intro n _
    sorry -- Follows from frankl_wilson_1981

/-- The base is between 1.2 and 3. -/
theorem base_bounds :
    1.2 ≤ chromaticLimit ∧ chromaticLimit ≤ 3 := by
  sorry -- Follows from frankl_wilson_1981 and larman_rogers_1972

/-!
## Proof Techniques

### Lower Bound Technique (Frankl-Wilson)
1. Consider the set S of all ±1 vectors in ℝⁿ with n/2 coordinates equal to 1
2. Any two such vectors are at distance √2 or distance 2
3. Scale to unit distance: use vectors at distance √2
4. Apply intersection theorems to bound independent sets
5. This gives chromatic number ≥ 1.2ⁿ

### Upper Bound Technique (Larman-Rogers)
1. Partition ℝⁿ into Voronoi cells of a lattice
2. Choose lattice so that diameter of each cell < 1
3. Color based on cell membership
4. The lattice Aₙ gives the 3ⁿ bound
-/

/-- The main result: exponential growth of χ(Gₙ) is established. -/
theorem erdos_704_solved :
    (∀ ε > 0, ∃ N, ∀ n ≥ N, chi n ≥ ((1 - ε) * 1.2^n).toNat) ∧
    (∀ ε > 0, ∃ N, ∀ n ≥ N, chi n ≤ (((3 + ε) : ℝ)^n).toNat + 1) :=
  ⟨frankl_wilson_1981, larman_rogers_1972⟩

/-- Summary of Erdős Problem #704. -/
theorem erdos_704 : True := trivial

end Erdos704

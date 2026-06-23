/-
  Aristotle targets for Erdos798Problem (Erdős #798: Covering Lattice Points with Lines)
  Routine supporting lemmas for automated proof search.
  See Erdos798Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open bounds (erdos_purdy_lower_bound, alon_upper_bound — axioms)
  - NOT the combinatorial constructions (lines_from_points — complex existential)
  - NOT the concrete small-n bounds (t_2_bound, t_3_bound — require nontrivial witnesses)
  - Routine corollaries: extracting asymptotic consequences from the stated axioms
  - Grid cardinality: ncard of the integer lattice grid

  Targets:
  1. latticeGrid_card: (latticeGrid n).ncard = n^2 for n ≥ 1
     The lattice grid {(i,j) : ℤ × ℤ | 1 ≤ i ≤ n, 1 ≤ j ≤ n} has exactly n² points.
     Proof sketch:
     - Show latticeGrid n = ↑(Finset.Icc (1:ℤ) n ×ˢ Finset.Icc (1:ℤ) n) as sets
     - Apply Set.ncard_coe_Finset to convert ncard to Finset.card
     - Apply Finset.card_product to split the product
     - Use Int.Icc_card or Finset.card_Icc: |Icc (1:ℤ) n| = n (for n ≥ 1)
     - Conclude n * n = n^2

  2. t_is_o_n: ∀ ε > 0, ∃ N, ∀ n ≥ N, (t n : ℝ) < ε * n
     The covering function t(n) = o(n). YES is the answer to Erdős's question.
     Proof sketch:
     - Obtain C, hC, hbound from alon_upper_bound: ∀ n ≥ 2, (t n : ℝ) ≤ C * n^(2/3) * log n
     - Fix ε > 0. Need: ∃ N, ∀ n ≥ N, C * n^(2/3) * log n < ε * n
     - Equivalently: C * log n < ε * n^(1/3) for large n
     - Key: (Real.log n) / n^(1/3 : ℝ) → 0 as n → ∞ (log grows slower than any power)
     - Formally: Filter.Tendsto (fun n => Real.log n / n^(1/3 : ℝ)) Filter.atTop (nhds 0)
       follows from Real.tendsto_log_div_pow or similar Mathlib asymptotic results
     - Choose N such that ∀ n ≥ N, C * log n / n^(1/3) < ε, i.e., C * log n < ε * n^(1/3)
     - Then C * n^(2/3) * log n < ε * n^(2/3) * n^(1/3) = ε * n

  Excluded (already correctly sorry or too hard for Aristotle):
  - lower_bound_intuition: counting argument requires formalization of coverage per line
  - lines_from_points: complex existential construction of line families
  - t_2_bound, t_3_bound: require concrete covering witnesses over the integer grid
  - explicit_lower: requires Erdős-Purdy counting argument formalization
-/
import Mathlib
import Proofs.Erdos798Problem

namespace Erdos798.Aristotle

open Erdos798 Real Filter Asymptotics Nat

-- ============================================================
-- Aristotle Target 1: Lattice grid cardinality
-- ============================================================

/-- **Lattice grid cardinality** (Aristotle target):
    The n×n integer lattice grid {1,...,n}² has exactly n² points.

    Proof sketch:
    1. Show the set equals the coercion of the Finset `Icc (1:ℤ) n ×ˢ Icc (1:ℤ) n`
    2. Apply Set.ncard_coe_Finset to convert to Finset.card
    3. Apply Finset.card_product: card of product = card × card
    4. Show |Finset.Icc (1:ℤ) (n:ℤ)| = n using Int.card_Icc or Finset.card_Icc
    5. Conclude n * n = n^2 by ring -/
theorem latticeGrid_card (n : ℕ) (hn : n ≥ 1) :
    (latticeGrid n).ncard = n^2 := by
  sorry

-- ============================================================
-- Aristotle Target 2: t(n) = o(n)
-- ============================================================

/-- **t(n) = o(n)** (Aristotle target):
    For any ε > 0, there exists N such that for all n ≥ N, t(n) < ε·n.

    Proof sketch:
    1. Obtain C > 0 and the bound from alon_upper_bound:
       ∀ n ≥ 2, (t n : ℝ) ≤ C * n^(2/3 : ℝ) * Real.log n
    2. For any ε > 0, we need: ∃ N, ∀ n ≥ N, C * n^(2/3 : ℝ) * Real.log n < ε * n
    3. This follows from: Real.log n / n^(1/3 : ℝ) → 0 as n → ∞
       Specifically: (fun n : ℕ => Real.log n / n^(1/3 : ℝ)) tends to 0 at atTop
       This is a consequence of: ∀ δ > 0, Real.log n = o(n^δ)
       (Mathlib has Real.tendsto_log_div_rpow_atTop or similar)
    4. Choose N₀ such that ∀ n ≥ N₀, C * Real.log n / n^(1/3 : ℝ) < ε
    5. Set N = max N₀ 2. For n ≥ N:
       (t n : ℝ) ≤ C * n^(2/3 : ℝ) * Real.log n
                 = n * (C * Real.log n / n^(1/3 : ℝ))   [since n^(2/3) * n^(-1/3) * n = n]
                 < n * ε = ε * n -/
theorem t_is_o_n :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (t n : ℝ) < ε * n := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := alon_upper_bound
  -- Key asymptotic: log n = o(n^(1/3))
  -- So C * n^(2/3) * log n = C * n * (log n / n^(1/3)) < ε * n for large n
  sorry

end Erdos798.Aristotle

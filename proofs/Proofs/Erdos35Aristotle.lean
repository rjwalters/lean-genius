/-
  Aristotle targets for Erdős Problem #35
  Routine supporting lemmas for automated proof search.
  See Erdos35Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT Plünnecke's inequality (deep 1970 result)
  - NOT Lagrange's four-square theorem (deep)
  - NOT Goldbach-dependent results
  - Routine Finset cardinality, density bounds, and real analysis
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos35Aristotle

open Finset Set

-- Routine: Filtering a singleton set gives card at most 1.
-- Used in: schnirelmannDensity_le_one (counting function on {1}).
theorem filter_singleton_card_le (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 2 \ {0}).filter P).card ≤ 1 := by
  sorry

-- Routine: Finset.range 2 \ {0} = {1}
-- Needed for density calculations at N=1.
theorem range2_sdiff_zero : Finset.range 2 \ {0} = {1} := by
  sorry

-- Routine: If 0 ∈ B and a ∈ A, then a ∈ A + B (sumset).
-- Used in: density_mono_sumset (A ⊆ A + B when 0 ∈ B).
theorem mem_sumset_of_zero_mem (A B : Set ℕ) (h0 : (0 : ℕ) ∈ B) (a : ℕ) (ha : a ∈ A) :
    a ∈ {n | ∃ x ∈ A, ∃ y ∈ B, n = x + y} := by
  sorry

-- Routine: The counting function is monotone in N.
-- |A ∩ {1,...,N}| ≤ |A ∩ {1,...,M}| when N ≤ M.
theorem counting_mono (A : Set ℕ) (N M : ℕ) (hNM : N ≤ M) :
    ((Finset.range (N + 1) \ {0}).filter (· ∈ A)).card ≤
    ((Finset.range (M + 1) \ {0}).filter (· ∈ A)).card := by
  sorry

-- Routine: The counting function is bounded by N.
-- |A ∩ {1,...,N}| ≤ N for any A.
theorem counting_le_N (A : Set ℕ) (N : ℕ) :
    ((Finset.range (N + 1) \ {0}).filter (· ∈ A)).card ≤ N := by
  sorry

-- Routine: For α ∈ [0,1] and k = 1, the power bound is trivial.
-- α^0 = 1 ≥ α + α(1-α)/1 = α(2-α) for α ∈ [0,1].
theorem power_bound_k1 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α ^ (1 - 1 / (1 : ℝ)) ≥ α + α * (1 - α) / 1 := by
  sorry

-- Routine: For α = 0, the power bound holds trivially.
-- 0^anything = 0 ≥ 0 + 0/k = 0.
theorem power_bound_alpha_zero (k : ℕ) (hk : k ≥ 1) :
    (0 : ℝ) ^ (1 - 1 / (k : ℝ)) ≥ 0 + 0 * (1 - 0) / k := by
  sorry

-- Routine: For α = 1, both sides equal 1.
-- 1^anything = 1, and 1 + 1*(1-1)/k = 1.
theorem power_bound_alpha_one (k : ℕ) (hk : k ≥ 1) :
    (1 : ℝ) ^ (1 - 1 / (k : ℝ)) ≥ 1 + 1 * (1 - 1) / k := by
  sorry

-- Routine: Infimum of values in [0,1] is in [0,1].
-- Used to show Schnirelmann density is in [0,1].
theorem iInf_nonneg_of_nonneg {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : 0 ≤ ⨅ i, f i := by
  sorry

-- Routine: division by positive number preserves ≤.
-- If a/n ≤ 1 when a ≤ n, for density ratio computations.
theorem ratio_le_one_of_card_le (a n : ℕ) (hn : n > 0) (h : a ≤ n) :
    (a : ℝ) / n ≤ 1 := by
  sorry

end Erdos35Aristotle

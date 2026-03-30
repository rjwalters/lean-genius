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

open Finset Set Classical

-- Routine: Finset.range 2 \ {0} = {1}
theorem range2_sdiff_zero : Finset.range 2 \ {0} = {1} := by
  ext x; simp [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton]; omega

-- Routine: Filtering a singleton set gives card at most 1.
-- Used in: schnirelmannDensity_le_one (counting function on {1}).
theorem filter_singleton_card_le (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range 2 \ {0}).filter P).card ≤ 1 := by
  rw [range2_sdiff_zero]
  simp [Finset.filter_singleton]
  split <;> simp

-- Routine: If 0 ∈ B and a ∈ A, then a ∈ A + B (sumset).
-- Used in: density_mono_sumset (A ⊆ A + B when 0 ∈ B).
theorem mem_sumset_of_zero_mem (A B : Set ℕ) (h0 : (0 : ℕ) ∈ B) (a : ℕ) (ha : a ∈ A) :
    a ∈ {n | ∃ x ∈ A, ∃ y ∈ B, n = x + y} := by
  exact ⟨a, ha, 0, h0, by omega⟩

/-
PROBLEM
Routine: The counting function is monotone in N.
|A ∩ {1,...,N}| ≤ |A ∩ {1,...,M}| when N ≤ M.

PROVIDED SOLUTION
Apply Finset.card_le_card after showing the filter of the smaller range is a subset of the filter of the larger range. The key is that range (N+1) \ {0} ⊆ range (M+1) \ {0} when N ≤ M, so filtering both by the same predicate preserves the subset relation.
-/
theorem counting_mono (A : Set ℕ) (N M : ℕ) (hNM : N ≤ M) :
    ((Finset.range (N + 1) \ {0}).filter (· ∈ A)).card ≤
    ((Finset.range (M + 1) \ {0}).filter (· ∈ A)).card := by
  exact Finset.card_mono fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_sdiff.mpr ⟨ Finset.mem_range.mpr <| by linarith [ Finset.mem_range.mp <| Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ], by aesop ⟩, Finset.mem_filter.mp hx |>.2 ⟩

/-
PROBLEM
Routine: The counting function is bounded by N.
|A ∩ {1,...,N}| ≤ N for any A.

PROVIDED SOLUTION
The filtered set is a subset of range(N+1) \ {0}, which has card at most N (since range(N+1) has N+1 elements and we remove 0 which is in range(N+1) when N+1 > 0, giving exactly N elements; when N = 0, range 1 \ {0} = ∅ which has card 0 ≤ 0). Use card_filter_le and then show card(range(N+1) \ {0}) ≤ N by cases or by computing card_sdiff.
-/
theorem counting_le_N (A : Set ℕ) (N : ℕ) :
    ((Finset.range (N + 1) \ {0}).filter (· ∈ A)).card ≤ N := by
  grind

/-
PROBLEM
Routine: For α ∈ [0,1] and k = 1, the power bound is trivial.
α^0 = 1 ≥ α + α(1-α)/1 = α(2-α) for α ∈ [0,1].

PROVIDED SOLUTION
Simplify: 1 - 1/1 = 0, so α^0 = 1 (using rpow). The RHS simplifies to α + α*(1-α) = α(2-α) = 2α - α². We need 1 ≥ 2α - α², i.e., α² - 2α + 1 ≥ 0, i.e., (α-1)² ≥ 0 which is always true. First show the exponent is 0 by norm_num, then use rpow_zero or the fact that x^(0:ℝ) = 1 for x ≥ 0 (need α > 0 or handle α = 0 separately), then nlinarith or nlinarith [sq_nonneg (α - 1)].
-/
theorem power_bound_k1 (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α ^ (1 - 1 / (1 : ℝ)) ≥ α + α * (1 - α) / 1 := by
  norm_num ; nlinarith [ sq_nonneg ( α - 1 ) ]

-- Routine: For α = 0, the power bound holds trivially.
theorem power_bound_alpha_zero (k : ℕ) (hk : k ≥ 1) :
    (0 : ℝ) ^ (1 - 1 / (k : ℝ)) ≥ 0 + 0 * (1 - 0) / k := by
  simp
  positivity

-- Routine: For α = 1, both sides equal 1.
theorem power_bound_alpha_one (k : ℕ) (hk : k ≥ 1) :
    (1 : ℝ) ^ (1 - 1 / (k : ℝ)) ≥ 1 + 1 * (1 - 1) / k := by
  simp [Real.one_rpow]

-- Routine: Infimum of nonneg values is nonneg.
theorem iInf_nonneg_of_nonneg {ι : Type*} [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : 0 ≤ ⨅ i, f i :=
  le_ciInf hf

-- Routine: a/n ≤ 1 when a ≤ n for positive n.
theorem ratio_le_one_of_card_le (a n : ℕ) (hn : n > 0) (h : a ≤ n) :
    (a : ℝ) / n ≤ 1 := by
  rw [div_le_one (Nat.cast_pos.mpr hn)]
  exact Nat.cast_le.mpr h

end Erdos35Aristotle
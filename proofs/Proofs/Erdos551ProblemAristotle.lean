/-
  Aristotle targets for Erdos551Problem
  Routine supporting lemmas for automated proof search.
  See Erdos551Problem.lean for the main formalization.

  These lemmas provide building blocks for the Ramsey number formalization:
  - ConjecturedFormula algebra and bounds
  - Threshold comparisons (Bondy-Erdős vs Nikiforov vs KLS)
  - Lower bound graph component structure via integer division
  - Cycle graph adjacency properties
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace Erdos551.Aristotle

open SimpleGraph Finset

/-
  ## Section 1: ConjecturedFormula Properties

  The formula R(C_k, K_n) = (k-1)(n-1) + 1 needs many routine algebraic
  properties for the main proof.
-/

def ConjecturedFormula (k n : ℕ) : ℕ := (k - 1) * (n - 1) + 1

-- Specific values used in verification of small cases
theorem formula_val_3_3 : ConjecturedFormula 3 3 = 5 := by sorry

theorem formula_val_4_3 : ConjecturedFormula 4 3 = 7 := by sorry

theorem formula_val_5_3 : ConjecturedFormula 5 3 = 9 := by sorry

theorem formula_val_4_4 : ConjecturedFormula 4 4 = 10 := by sorry

theorem formula_val_5_4 : ConjecturedFormula 5 4 = 13 := by sorry

theorem formula_val_5_5 : ConjecturedFormula 5 5 = 17 := by sorry

theorem formula_val_6_3 : ConjecturedFormula 6 3 = 11 := by sorry

-- The formula matches 2k-1 when n=3
theorem formula_n3 (k : ℕ) (hk : k ≥ 3) :
    ConjecturedFormula k 3 = 2 * k - 1 := by sorry

-- Monotonicity in k alone
theorem formula_mono_k (k₁ k₂ n : ℕ) (hk : k₁ ≤ k₂) (hn : n ≥ 1) :
    ConjecturedFormula k₁ n ≤ ConjecturedFormula k₂ n := by sorry

-- Monotonicity in n alone
theorem formula_mono_n (k n₁ n₂ : ℕ) (hk : k ≥ 1) (hn : n₁ ≤ n₂) :
    ConjecturedFormula k n₁ ≤ ConjecturedFormula k n₂ := by sorry

-- Strict monotonicity in k
theorem formula_strict_mono_k (k₁ k₂ n : ℕ) (hk : k₁ < k₂) (hn : n ≥ 2) :
    ConjecturedFormula k₁ n < ConjecturedFormula k₂ n := by sorry

-- Strict monotonicity in n
theorem formula_strict_mono_n (k n₁ n₂ : ℕ) (hk : k ≥ 2) (hn : n₁ < n₂) :
    ConjecturedFormula k n₁ < ConjecturedFormula k n₂ := by sorry

-- Lower bound: formula is always at least 1
theorem formula_ge_one (k n : ℕ) : ConjecturedFormula k n ≥ 1 := by sorry

-- Formula grows at least linearly in k
theorem formula_ge_k (k n : ℕ) (hn : n ≥ 2) :
    ConjecturedFormula k n ≥ k := by sorry

-- Formula grows at least linearly in n
theorem formula_ge_n (k n : ℕ) (hk : k ≥ 2) :
    ConjecturedFormula k n ≥ n := by sorry

-- Lower bound vertex count equals formula minus 1
theorem lower_bound_vertex_count (k n : ℕ) (hk : k ≥ 1) (hn : n ≥ 1) :
    (k - 1) * (n - 1) = ConjecturedFormula k n - 1 := by sorry

/-
  ## Section 2: Threshold Comparisons

  The three thresholds: Bondy-Erdős (quadratic), Nikiforov (linear),
  KLS (near-logarithmic). Routine arithmetic comparisons.
-/

def BondyErdosThreshold (n : ℕ) : ℕ := n ^ 2 - 1
def NikiforovThreshold (n : ℕ) : ℕ := 4 * n + 2

-- Nikiforov strictly improves on Bondy-Erdős for n ≥ 5
theorem nikiforov_lt_bondy_erdos_5 :
    NikiforovThreshold 5 < BondyErdosThreshold 5 := by sorry

theorem nikiforov_lt_bondy_erdos_10 :
    NikiforovThreshold 10 < BondyErdosThreshold 10 := by sorry

theorem nikiforov_lt_bondy_erdos_100 :
    NikiforovThreshold 100 < BondyErdosThreshold 100 := by sorry

-- General comparison for n ≥ 5
theorem nikiforov_lt_bondy_erdos (n : ℕ) (hn : n ≥ 5) :
    NikiforovThreshold n < BondyErdosThreshold n := by sorry

-- At n=4, Nikiforov does NOT improve (they are equal or Nikiforov is worse)
theorem nikiforov_ge_bondy_erdos_4 :
    NikiforovThreshold 4 ≥ BondyErdosThreshold 4 := by sorry

-- Bondy-Erdős threshold values
theorem bondy_erdos_val_3 : BondyErdosThreshold 3 = 8 := by sorry

theorem bondy_erdos_val_5 : BondyErdosThreshold 5 = 24 := by sorry

theorem bondy_erdos_val_10 : BondyErdosThreshold 10 = 99 := by sorry

-- Nikiforov threshold values
theorem nikiforov_val_3 : NikiforovThreshold 3 = 14 := by sorry

theorem nikiforov_val_5 : NikiforovThreshold 5 = 22 := by sorry

theorem nikiforov_val_10 : NikiforovThreshold 10 = 42 := by sorry

theorem nikiforov_val_100 : NikiforovThreshold 100 = 402 := by sorry

-- Threshold ratio: Nikiforov saves roughly n²-4n-3 over Bondy-Erdős
theorem threshold_improvement (n : ℕ) (hn : n ≥ 5) :
    BondyErdosThreshold n - NikiforovThreshold n = n ^ 2 - 4 * n - 3 := by sorry

/-
  ## Section 3: Lower Bound Graph Component Properties

  The lower bound graph has (n-1) disjoint copies of K_{k-1}.
  Integer division determines component membership.
-/

-- Component index is bounded
theorem component_index_bound (k n : ℕ) (hk : k ≥ 2)
    (i : Fin ((k - 1) * (n - 1))) :
    i.val / (k - 1) < n - 1 := by sorry

-- Vertices in the same component have close indices
theorem same_component_close (k n : ℕ) (hk : k ≥ 2)
    (i j : ℕ) (hq : i / (k - 1) = j / (k - 1))
    (hi : i < (k - 1) * (n - 1)) (hj : j < (k - 1) * (n - 1)) :
    (i : ℤ) - j < k - 1 ∧ (j : ℤ) - i < k - 1 := by sorry

-- Each component has exactly k-1 vertices
theorem component_size (k n c : ℕ) (hk : k ≥ 2) (hc : c < n - 1) :
    (Finset.filter (fun i : Fin ((k - 1) * (n - 1)) => i.val / (k - 1) = c)
      Finset.univ).card = k - 1 := by sorry

-- Total number of components
theorem num_components (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ 2) :
    (Finset.image (fun i : Fin ((k - 1) * (n - 1)) => i.val / (k - 1))
      Finset.univ).card = n - 1 := by sorry

-- A component is too small for a k-cycle: each has only k-1 vertices
theorem component_too_small_for_cycle (k : ℕ) (hk : k ≥ 3) :
    k - 1 < k := by sorry

-- Vertices in different components are distinct
theorem different_components_ne (k n : ℕ) (hk : k ≥ 2)
    (i j : ℕ) (hi : i < (k - 1) * (n - 1)) (hj : j < (k - 1) * (n - 1))
    (hdiff : i / (k - 1) ≠ j / (k - 1)) :
    i ≠ j := by sorry

/-
  ## Section 4: Cycle Graph Adjacency

  Properties of the cycle graph C_k defined via modular adjacency.
-/

-- Successor adjacency in C_k
theorem cycle_adj_succ (k : ℕ) (hk : k ≥ 3) (i : Fin k) :
    (i.val + 1) % k < k := by sorry

-- Modular arithmetic for cycle adjacency
theorem cycle_mod_bound (k : ℕ) (hk : k ≥ 1) (a : ℕ) :
    a % k < k := by sorry

-- In C_k, vertex 0 is adjacent to vertex 1
theorem cycle_0_adj_1 (k : ℕ) (hk : k ≥ 3) :
    (0 + 1) % k = 1 := by sorry

-- In C_k, vertex k-1 is adjacent to vertex 0
theorem cycle_last_adj_0 (k : ℕ) (hk : k ≥ 3) :
    ((k - 1) + 1) % k = 0 := by sorry

-- C_k has exactly k edges (as an undirected graph on Fin k)
-- Each vertex has degree 2
theorem cycle_degree_two (k : ℕ) (hk : k ≥ 3) (i : Fin k) :
    ∃ j₁ j₂ : Fin k, j₁ ≠ j₂ ∧ j₁ ≠ i ∧ j₂ ≠ i ∧
      ((i.val + 1) % k = j₁.val ∨ (j₁.val + 1) % k = i.val) ∧
      ((i.val + 1) % k = j₂.val ∨ (j₂.val + 1) % k = i.val) := by sorry

/-
  ## Section 5: Exception Case Arithmetic

  The (3,3) exception: C_3 = K_3, so R(C_3,K_3) = R(K_3,K_3) = 6.
  Formula gives (3-1)(3-1)+1 = 5 ≠ 6.
-/

-- The formula gives 5 at (3,3)
theorem exception_formula_val : ConjecturedFormula 3 3 = 5 := by sorry

-- 5 ≠ 6 (the formula is wrong at (3,3))
theorem five_ne_six : 5 ≠ 6 := by sorry

-- For all other k ≥ n ≥ 3 with (k,n) ≠ (3,3), we have k ≥ 4 or n ≥ 4
theorem non_exception_cases (k n : ℕ) (hkn : k ≥ n) (hn : n ≥ 3)
    (hne : (k, n) ≠ (3, 3)) :
    k ≥ 4 ∨ n ≥ 4 := by sorry

end Erdos551.Aristotle

/-
  Erdős Problem #629: List Chromatic Number of Bipartite Graphs

  Source: https://erdosproblems.com/629
  Status: OPEN (asymptotic behavior not fully determined)

  Statement:
  The list chromatic number χ_L(G) is the minimal k such that for any assignment
  of a list of k colors to each vertex, a proper coloring can be chosen from the
  lists. Determine the minimal number of vertices n(k) of a bipartite graph G
  such that χ_L(G) > k.

  Known Results:
  - n(2) = 6 (Erdős-Rubin-Taylor 1980)
  - n(3) = 14 (Hanson-MacGillivray-Toft 1996)
  - Original bounds: 2^{k-1} < n(k) < k² · 2^{k+2}
  - Improved lower: 2^k · (k/log k)^{1/2} ≪ n(k) (Radhakrishnan-Srinivasan 2000)
  - Recursive upper: n(k) ≤ k · n(k-2) + 2^k

  Related to Problem #901 via: m(k) ≤ n(k) ≤ m(k+1)
  where m(k) is the smallest family of k-sets without Property B.

  Tags: graph-theory, chromatic-number, list-coloring, bipartite-graphs
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Erdos629

open SimpleGraph Finset

/- ## Part I: List Coloring Definitions -/

/-- A color list assignment gives each vertex a set of available colors. -/
def ColorListAssignment (V : Type*) (C : Type*) := V → Finset C

/-- A coloring respects a list assignment if each vertex gets a color from its list. -/
def RespectsLists {V C : Type*} (L : ColorListAssignment V C) (f : V → C) : Prop :=
  ∀ v : V, f v ∈ L v

/-- A coloring is proper if adjacent vertices have different colors. -/
def IsProperColoring {V : Type*} [DecidableEq V] (G : SimpleGraph V) (f : V → C) : Prop :=
  ∀ u v : V, G.Adj u v → f u ≠ f v

/-- A graph is k-list-colorable if for any k-list assignment, a proper coloring exists. -/
def IsKListColorable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C] (L : ColorListAssignment V C),
    (∀ v, (L v).card ≥ k) →
    ∃ f : V → C, RespectsLists L f ∧ IsProperColoring G f

/-- The list chromatic number χ_L(G) is the minimal k for k-list-colorability. -/
noncomputable def listChromaticNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | IsKListColorable G k}

/- ## Part II: Bipartite Graphs -/

/-- A graph is bipartite if its vertices can be 2-colored. -/
def IsBipartite {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ f : V → Fin 2, IsProperColoring G f

/-- Every bipartite graph has chromatic number at most 2. -/
theorem bipartite_chromatic_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsBipartite G) : G.chromaticNumber ≤ 2 := by
  sorry

/-- For bipartite graphs, ordinary χ(G) ≤ 2 but χ_L(G) can be arbitrarily large! -/
theorem bipartite_list_chromatic_unbounded :
    ∀ k : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsBipartite G ∧ listChromaticNumber G > k := by
  sorry

/- ## Part III: The Function n(k) -/

/-- n(k) = minimal vertex count of bipartite G with χ_L(G) > k. -/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    Fintype.card V = m ∧ IsBipartite G ∧ listChromaticNumber G > k}

/-- n(k) is well-defined (the infimum exists). -/
theorem n_well_defined (k : ℕ) : n k > 0 := by
  sorry

/-- n is monotone: larger k requires more vertices. -/
theorem n_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) : n k₁ ≤ n k₂ := by
  sorry

/- ## Part IV: Exact Values -/

/-- Erdős-Rubin-Taylor (1980): n(2) = 6. -/
theorem n_2_eq_6 : n 2 = 6 := by
  sorry

/-- Hanson-MacGillivray-Toft (1996): n(3) = 14. -/
theorem n_3_eq_14 : n 3 = 14 := by
  sorry

/- ## Part V: Original Bounds (Erdős-Rubin-Taylor 1980) -/

/-- Original lower bound: 2^{k-1} < n(k). -/
theorem ert_lower_bound (k : ℕ) (hk : k ≥ 1) : 2 ^ (k - 1) < n k := by
  sorry

/-- Original upper bound: n(k) < k² · 2^{k+2}. -/
theorem ert_upper_bound (k : ℕ) (hk : k ≥ 1) : n k < k ^ 2 * 2 ^ (k + 2) := by
  sorry

/- ## Part VI: Improved Bounds -/

/-- Radhakrishnan-Srinivasan (2000) improved lower bound.
    2^k · (k / log k)^{1/2} ≪ n(k) -/
theorem rs_lower_bound :
    ∀ ε > 0, ∀ᶠ k in Filter.atTop,
      (2 : ℝ) ^ k * (k / Real.log k) ^ (1/2 : ℝ) * (1 - ε) < n k := by
  sorry

/-- Hanson-MacGillivray-Toft recursive upper bound: n(k) ≤ k · n(k-2) + 2^k. -/
theorem hmt_recursive_upper (k : ℕ) (hk : k ≥ 2) :
    n k ≤ k * n (k - 2) + 2 ^ k := by
  sorry

/- ## Part VII: Connection to Property B -/

/-- m(k) = smallest family of k-sets without Property B.
    Property B means having a 2-coloring of the ground set with no monochromatic set. -/
noncomputable def propertyB_threshold (k : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ (F : Finset (Finset (Fin m))),
    (∀ S ∈ F, S.card = k) ∧
    ¬∃ f : Fin m → Fin 2, ∀ S ∈ F, ∃ x y : Fin m, x ∈ S ∧ y ∈ S ∧ f x ≠ f y}

/-- Key connection: m(k) ≤ n(k) ≤ m(k+1).
    This relates list coloring to Property B (Problem #901). -/
theorem n_property_b_bounds (k : ℕ) (hk : k ≥ 1) :
    propertyB_threshold k ≤ n k ∧ n k ≤ propertyB_threshold (k + 1) := by
  sorry

/- ## Part VIII: Constructions -/

/-- The complete bipartite graph K_{m,n}. -/
def completeBipartite (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) where
  Adj := fun u v => match u, v with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := by
    intro u v h
    cases u <;> cases v <;> simp_all [h]
  loopless := by
    intro v
    cases v <;> simp

/-- Complete bipartite graphs are bipartite (obviously). -/
theorem completeBipartite_is_bipartite (m n : ℕ) :
    IsBipartite (completeBipartite m n) := by
  sorry

/-- K_{n,n} has list chromatic number ≈ log₂ n + 1. -/
theorem knn_list_chromatic (n : ℕ) (hn : n ≥ 2) :
    Nat.clog 2 n ≤ listChromaticNumber (completeBipartite n n) ∧
    listChromaticNumber (completeBipartite n n) ≤ Nat.clog 2 n + 2 := by
  sorry

/- ## Part IX: Asymptotic Behavior -/

/-- n(k) grows exponentially in k. -/
theorem n_exponential_growth :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ k in Filter.atTop, c₁ * 2 ^ k < (n k : ℝ) ∧ (n k : ℝ) < c₂ * k ^ 2 * 2 ^ k := by
  sorry

/-- The precise exponent is not known - this is what makes the problem OPEN. -/
def ExactAsymptoticConjecture : Prop :=
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
    ∀ ε > 0, ∀ᶠ k in Filter.atTop,
      2 ^ k * (k : ℝ) ^ (α - ε) < n k ∧ (n k : ℝ) < 2 ^ k * (k : ℝ) ^ (α + ε)

end Erdos629

/-
  ## Summary

  This file formalizes Erdős Problem #629 on list chromatic numbers of bipartite graphs.

  **Status**: OPEN (exact asymptotic behavior unknown)

  **The Problem**: Find n(k) = minimum vertices in a bipartite graph G with χ_L(G) > k.

  **Key Results**:
  - Exact values: n(2) = 6, n(3) = 14
  - Original bounds (1980): 2^{k-1} < n(k) < k² · 2^{k+2}
  - Improved lower (2000): 2^k · (k/log k)^{1/2} ≪ n(k)
  - Connection to Property B: m(k) ≤ n(k) ≤ m(k+1)

  **Key Insight**: Bipartite graphs have χ(G) ≤ 2, but χ_L(G) can be arbitrarily large!
  This surprising gap between ordinary and list chromatic number is the heart of the problem.

  **What we formalize**:
  1. List coloring and list chromatic number definitions
  2. The function n(k) and its basic properties
  3. Exact values n(2) = 6, n(3) = 14
  4. Original and improved bounds
  5. Connection to Property B (Problem #901)
  6. Complete bipartite graph constructions

  **Key sorries**:
  - `n_2_eq_6`, `n_3_eq_14`: Exact values require careful constructions
  - `rs_lower_bound`: Probabilistic method result
  - `n_property_b_bounds`: Connection to hypergraph coloring

  **Open question**: Determine the exact asymptotic behavior of n(k).
-/

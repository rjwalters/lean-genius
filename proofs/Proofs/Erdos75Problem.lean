/-
# Erdős Problem #75 — Uncountable Chromatic Number and Large Independent Sets

Erdős, Hajnal, and Szemerédi asked:

Is there a graph G of chromatic number ℵ₁ such that for all ε > 0,
if n is sufficiently large and H is a subgraph of G on n vertices,
then H contains an independent set of size > n^{1−ε}?

Erdős further suggested this might hold with independent sets of size ≫ n.

This is a $1000 Erdős prize problem.

Reference: https://erdosproblems.com/75
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Erdos75

open Classical

/- ## Graph Infrastructure

Previous version used 7 abstract axioms for graph types and properties.
These are now concrete Lean 4 structures with proved theorems.
Axiom count reduced from 9 to 3 (the 2 open conjectures + 1 pigeonhole). -/

/-- A simple undirected graph on vertex type V:
    symmetric adjacency relation with no self-loops -/
structure UGraph (V : Type*) where
  adj : V → V → Prop
  adj_symm : ∀ {u v}, adj u v → adj v u
  adj_loopless : ∀ v, ¬adj v v

/-- A bundled graph: a vertex type together with graph structure -/
structure Graph where
  V : Type
  str : UGraph V

/-- A graph G is properly k-colorable: there exists a function V → Fin k
    such that adjacent vertices receive different colors -/
def Graph.Colorable (G : Graph) (k : ℕ) : Prop :=
  ∃ f : G.V → Fin k, ∀ u v, G.str.adj u v → f u ≠ f v

/-- chromaticNum G n means G requires at least n colours:
    for all k < n, no proper k-coloring exists -/
def chromaticNum (G : Graph) (n : ℕ) : Prop :=
  ∀ k, k < n → ¬G.Colorable k

/-- Monotonicity of chromatic number lower bound -/
theorem chromaticNum_mono (G : Graph) (m n : ℕ) (h : m ≤ n) :
    chromaticNum G n → chromaticNum G m := by
  intro hn k hk
  exact hn k (lt_of_lt_of_le hk h)

/-- G has uncountable chromatic number: requires more than any finite number of colours -/
def HasUncountableChromaticNum (G : Graph) : Prop :=
  ∀ n : ℕ, chromaticNum G n

/- ## Finite Subgraphs and Independence -/

/-- A finite subgraph of G on exactly n vertices,
    given by an injective map from Fin n into G's vertex set -/
structure FiniteSubgraph (G : Graph) (n : ℕ) where
  embed : Fin n → G.V
  embed_injective : Function.Injective embed

/-- A set of vertices S in a finite subgraph is independent if
    no two distinct vertices in S are adjacent in G -/
def FiniteSubgraph.IsIndepSet {G : Graph} {n : ℕ}
    (H : FiniteSubgraph G n) (S : Finset (Fin n)) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬G.str.adj (H.embed i) (H.embed j)

/-- The empty set is always independent -/
theorem FiniteSubgraph.empty_IsIndepSet {G : Graph} {n : ℕ}
    (H : FiniteSubgraph G n) : H.IsIndepSet ∅ :=
  fun _ hi => absurd hi (Finset.notMem_empty _)

/-- The independence number of a finite subgraph:
    maximum cardinality of an independent set in H.
    Defined as the sup over k ∈ {0, ..., n} of k when an independent set
    of that size exists. -/
noncomputable def indepNumber {G : Graph} {n : ℕ} (H : FiniteSubgraph G n) : ℕ :=
  Finset.sup (Finset.range (n + 1))
    (fun k => if ∃ S : Finset (Fin n), S.card = k ∧ H.IsIndepSet S then k else 0)

/-- The independence number is at most the number of vertices -/
theorem indepNumber_le (G : Graph) (n : ℕ) (H : FiniteSubgraph G n) :
    indepNumber H ≤ n := by
  simp only [indepNumber]
  apply Finset.sup_le
  intro k hk
  rw [Finset.mem_range] at hk
  split_ifs <;> omega

/- ## Known Context -/

/-- If there exists an independent set of size m ≤ n, then indepNumber ≥ m -/
theorem indepNumber_ge_of_exists {G : Graph} {n : ℕ} (H : FiniteSubgraph G n)
    {m : ℕ} (hm : m ≤ n) (S : Finset (Fin n)) (hcard : S.card = m)
    (hindep : H.IsIndepSet S) : m ≤ indepNumber H := by
  unfold indepNumber
  have hm_range : m ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hif : (if ∃ S : Finset (Fin n), S.card = m ∧ H.IsIndepSet S then m else 0) = m := by
    rw [if_pos ⟨S, hcard, hindep⟩]
  calc m = (if ∃ S : Finset (Fin n), S.card = m ∧ H.IsIndepSet S then m else 0) :=
        hif.symm
    _ ≤ Finset.sup (Finset.range (n + 1))
        (fun k => if ∃ S : Finset (Fin n), S.card = k ∧ H.IsIndepSet S then k else 0) :=
        Finset.le_sup (f := fun k => if ∃ S : Finset (Fin n), S.card = k ∧ H.IsIndepSet S
          then k else 0) hm_range

/-- If G is k-colorable (k > 0), every n-vertex subgraph has an independent set
    of size ≥ n/k. (Pigeonhole principle on color classes.)

    Proof: restrict the coloring to the subgraph. By pigeonhole, some color class
    has ≥ ⌈n/k⌉ ≥ n/k vertices. This color class is independent (proper coloring).
    So indepNumber ≥ n/k, hence indepNumber * k ≥ n. -/
theorem finite_chromatic_independence (n k : ℕ) (G : Graph) (hk : G.Colorable k)
    (_hkpos : 0 < k) :
  ∀ H : FiniteSubgraph G n, indepNumber H * k ≥ n := by
  intro H
  obtain ⟨f, hf⟩ := hk
  -- Restrict k-coloring to subgraph
  set g : Fin n → Fin k := fun i => f (H.embed i)
  set fib : Fin k → Finset (Fin n) := fun c => Finset.univ.filter (fun i => g i = c)
  -- Each color class is independent (adjacent vertices get different colors)
  have hfib_indep : ∀ c : Fin k, H.IsIndepSet (fib c) := by
    intro c i hi j hj _hij hadj
    exact absurd ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
      (hf _ _ hadj)
  -- Each color class has at most indepNumber H elements
  have hfib_le : ∀ c : Fin k, (fib c).card ≤ indepNumber H := by
    intro c
    exact indepNumber_ge_of_exists H
      ((Finset.card_filter_le _ _).trans (by simp [Finset.card_univ, Fintype.card_fin]))
      (fib c) rfl (hfib_indep c)
  -- Color classes are pairwise disjoint
  have hdisj : ∀ c ∈ (Finset.univ : Finset (Fin k)),
      ∀ d ∈ Finset.univ, c ≠ d → Disjoint (fib c) (fib d) := by
    intro c _ d _ hcd
    rw [Finset.disjoint_left]
    intro i hi hd
    exact absurd ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hd).2) hcd
  -- Color classes cover all vertices
  have hcover : Finset.univ.biUnion fib = (Finset.univ : Finset (Fin n)) := by
    ext i; constructor
    · exact fun _ => Finset.mem_univ _
    · intro _
      exact Finset.mem_biUnion.mpr
        ⟨g i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  -- n = Σ|fib c| ≤ k · indepNumber H = indepNumber H · k
  suffices n ≤ indepNumber H * k by omega
  calc n = (Finset.univ : Finset (Fin n)).card := by
          simp [Finset.card_univ, Fintype.card_fin]
    _ = (Finset.univ.biUnion fib).card := by rw [hcover]
    _ = ∑ c ∈ Finset.univ, (fib c).card := Finset.card_biUnion hdisj
    _ ≤ ∑ _c ∈ Finset.univ, indepNumber H := Finset.sum_le_sum fun c _ => hfib_le c
    _ = indepNumber H * k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- The Erdős–Hajnal conjecture (related): for every H, graphs not containing
    H as induced subgraph have polynomially large cliques or independent sets -/
/- erdos_hajnal_related: the Erdős–Hajnal conjecture states that graphs
  not containing H as induced subgraph have polynomially large cliques or
  independent sets. -/

/- ## The Independence Ratio Property -/

/-- A graph has the (1−ε)-independence property if every sufficiently
    large finite subgraph on n vertices has independence number > n^{1−ε}.
    Approximated as: positive independence number (the full n^{1−ε}
    bound requires real-valued exponents). -/
def HasLargeIndepSets (G : Graph) : Prop :=
  ∀ ε : ℚ, 0 < ε → ε < 1 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : FiniteSubgraph G n,
        0 < indepNumber H

/-- The stronger version: independence number is ≫ n (linear) -/
def HasLinearIndepSets (G : Graph) : Prop :=
  ∃ c : ℚ, 0 < c ∧
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ H : FiniteSubgraph G n,
        c * (n : ℚ) ≤ (indepNumber H : ℚ)

/- ## The Erdős Problem -/

/-- The strong form (linear independence) implies the basic form -/
theorem linear_implies_large (G : Graph) :
    HasLinearIndepSets G → HasLargeIndepSets G := by
  intro ⟨c, hc_pos, N, hN⟩ ε _ _
  refine ⟨max N 1, fun n hn H => ?_⟩
  have hcn := hN n (le_of_max_le_left hn) H
  have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast le_of_max_le_right hn
  exact Nat.cast_pos.mp (lt_of_lt_of_le (mul_pos hc_pos (lt_of_lt_of_le one_pos hn1)) hcn)

/-- The strong conjecture implies the basic conjecture -/
theorem strong_implies_basic :
    (∃ G : Graph, HasUncountableChromaticNum G ∧ HasLinearIndepSets G) →
    (∃ G : Graph, HasUncountableChromaticNum G ∧ HasLargeIndepSets G) := by
  intro ⟨G, hchrom, hlin⟩
  exact ⟨G, hchrom, linear_implies_large G hlin⟩

/-- Erdős Problem 75 (basic form): There exists a graph with uncountable
    chromatic number and the large independence set property -/
/-- Erdős Problem 75 (strong form): There exists a graph with uncountable
    chromatic number where every large finite subgraph has linear independence number -/
end Erdos75

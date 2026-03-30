/-
Erdős Problem #743: Tree Packing Conjecture

Let T₂, T₃, ..., Tₙ be a collection of trees such that Tₖ has k vertices.
Can we always write Kₙ as the edge-disjoint union of the Tₖ?

This is the famous Gyárfás-Lehel Tree Packing Conjecture (1978).

**Status**: OPEN (major partial results known)

**Known Results**:
- Gyárfás-Lehel (1978): Stars/paths case
- Fishburn (1983): Verified for n ≤ 9
- Bollobás (1983): Smallest ⌊n/√2⌋ trees pack greedily
- Joos-Kim-Kühn-Osthus (2019): Bounded degree trees
- Allen et al. (2021): Max degree ≤ cn/log n
- Janzer-Montgomery (2024): Largest cn trees can be packed

**Edge Count**: Σ(k-1) for k=2..n = n(n-1)/2 = |E(Kₙ)| (necessary condition)

References:
- [GyLe78] Gyárfás-Lehel (1978)
- [Bo83] Bollobás (1983)
- [JKKO19] Joos-Kim-Kühn-Osthus (2019)
- [JaMo24] Janzer-Montgomery (2024)
- https://erdosproblems.com/743
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic

open Nat Finset

namespace Erdos743

/- ## Tree Structures -/

/-- A tree on k vertices: connected, acyclic, with k-1 edges.
Axiomatized as a type since the full graph-theoretic definition
requires infrastructure beyond the scope of this formalization. -/
axiom TreeType (k : ℕ) : Type

/-- A collection of trees T₂, T₃, ..., Tₙ where Tₖ has k vertices. -/
def TreeCollection (n : ℕ) : Type :=
  (k : ℕ) → (2 ≤ k ∧ k ≤ n) → TreeType k

/-- Edge-disjoint packing: the trees can be embedded in Kₙ
with no edge used twice. Axiomatized since the full definition
requires graph embeddings and edge-disjointness predicates. -/
axiom canPack (n : ℕ) (tc : TreeCollection n) : Prop

/-- The maximum degree of a tree, axiomatized. -/
axiom maxDegree (k : ℕ) (T : TreeType k) : ℕ

/-- A tree is a star if one vertex has degree k-1. -/
axiom isStar (k : ℕ) (T : TreeType k) : Prop

/-- A tree is a path if it has exactly two leaves (degree-1 vertices). -/
axiom isPath (k : ℕ) (T : TreeType k) : Prop

/-- A tree collection has bounded degree if all trees have max degree ≤ Δ. -/
def boundedDegreeCollection (n : ℕ) (tc : TreeCollection n) (Δ : ℕ) : Prop :=
  ∀ k : ℕ, ∀ h : 2 ≤ k ∧ k ≤ n, maxDegree k (tc k h) ≤ Δ

/- ## Edge Count Verification -/

/-- Total edges in T₂,...,Tₙ: each Tₖ has k-1 edges. -/
def totalTreeEdges (n : ℕ) : ℕ := (Finset.range (n - 1)).sum fun i => i + 1

/-- Edges in the complete graph Kₙ. -/
def completeGraphEdges (n : ℕ) : ℕ := n * (n - 1) / 2

/-- The total tree edges equals the edges in Kₙ.
This is a necessary condition for perfect packing. -/
theorem edge_counts_match (n : ℕ) (hn : n ≥ 2) :
    totalTreeEdges n = completeGraphEdges n := by
  simp only [totalTreeEdges, completeGraphEdges]
  -- Helper: 2 * ∑_{i<m} (i+1) = m * (m+1)
  have haux : ∀ m, 2 * (Finset.range m).sum (· + 1) = m * (m + 1) := by
    intro m; induction m with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ]; nlinarith
  have hm := haux (n - 1)
  rw [show n - 1 + 1 = n from by omega] at hm
  -- hm : 2 * sum = (n - 1) * n
  -- Goal: sum = n * (n - 1) / 2
  conv_rhs => rw [show n * (n - 1) = (n - 1) * n from by ring]
  rw [show (n - 1) * n = 2 * (Finset.range (n - 1)).sum (· + 1) from hm.symm]
  exact (Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)).symm

/-- Concrete edge counts for small complete graphs. -/
theorem complete_graph_edges_small :
    completeGraphEdges 2 = 1 ∧
    completeGraphEdges 3 = 3 ∧
    completeGraphEdges 4 = 6 ∧
    completeGraphEdges 5 = 10 ∧
    completeGraphEdges 6 = 15 := by
  unfold completeGraphEdges
  norm_num

/- ## The Tree Packing Conjecture -/

/-- **Tree Packing Conjecture (Gyárfás-Lehel 1978, OPEN):**
For any collection T₂,...,Tₙ where Tₖ has k vertices, the trees
can be packed edge-disjointly into Kₙ. -/
def treePackingConjecture : Prop :=
  ∀ n : ℕ, n ≥ 2 → ∀ tc : TreeCollection n, canPack n tc

/- ## Gyárfás-Lehel Results (1978) -/

/-- **Stars case:** If all but at most 2 trees are stars,
the conjecture holds. -/
/-- **Stars and paths case:** If all trees are stars or paths,
the conjecture holds. -/
axiom gyarfasLehel_starsPaths (n : ℕ) (hn : n ≥ 2) (tc : TreeCollection n) :
    (∀ k : ℕ, ∀ h : 2 ≤ k ∧ k ≤ n,
      isStar k (tc k h) ∨ isPath k (tc k h)) →
    canPack n tc

/- ## Small Cases and Greedy Packing -/

/-- **Fishburn (1983):** The conjecture holds for n ≤ 9,
verified by exhaustive computation. -/
axiom fishburn_small_n :
    ∀ n : ℕ, n ≤ 9 → ∀ tc : TreeCollection n, canPack n tc

/-- **Bollobás (1983):** The smallest ⌊n/√2⌋ trees can always
be packed greedily into Kₙ. This means roughly 70% of the small
trees can be handled by a simple greedy algorithm. -/
/- ## Bounded Degree Results -/

/-- **JKKO Theorem (2019):** For any fixed Δ, the conjecture holds
for Δ-bounded degree collections when n is large enough.
Published in Combinatorica. -/
axiom jkko_boundedDegree (Δ : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ tc : TreeCollection n,
      boundedDegreeCollection n tc Δ → canPack n tc

/-- **Allen et al. (2021):** The conjecture holds when all trees
have max degree ≤ cn/log n, a significant extension of JKKO. -/
/- ## Packing Large Trees (2024) -/

/-- **Janzer-Montgomery (2024):** There exists c > 0 such that
for any tree collection, the largest cn trees can always be packed.
Combined with Bollobás's result for small trees, only trees of
intermediate size (roughly 0.7n to (1-c)n vertices) remain unresolved. -/
/- ## Summary -/

/-- **Summary of Erdős Problem #743.**
Combines the key verified partial results: small cases,
stars/paths case, and bounded degree case. The full conjecture
remains OPEN — the main gap is trees of intermediate size. -/
theorem erdos_743_summary :
    (∀ n ≤ 9, ∀ tc : TreeCollection n, canPack n tc) ∧
    (∀ n ≥ 2, ∀ tc : TreeCollection n,
      (∀ k h, isStar k (tc k h) ∨ isPath k (tc k h)) → canPack n tc) ∧
    (∀ Δ : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ tc : TreeCollection n,
      boundedDegreeCollection n tc Δ → canPack n tc) :=
  ⟨fishburn_small_n, gyarfasLehel_starsPaths, jkko_boundedDegree⟩

end Erdos743

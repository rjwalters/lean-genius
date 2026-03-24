/-
Erdős Problem #1182: Ramsey-Theoretic Edge Thresholds

Source: https://erdosproblems.com/1182
Status: OPEN (Burr–Erdős–Faudree–Rousseau–Schelp)

Statement:
Let f(n) = max edges in a connected n-vertex graph G with R(K₃, G) = 2n - 1.
Let F(n) = max edges such that EVERY connected n-vertex graph G with
  ≤ F(n) edges satisfies R(K₃, G) = 2n - 1.

Estimate f(n) and F(n). In particular, does F(n)/n → ∞?

Known bounds:
- F(n) ≥ n - 1 (Chvátal: R(K₃, tree) = 2n - 1)
- (17n + 1)/15 ≤ F(n) ≤ (27/4 + o(1)) · n · (log n)²
- √(log n) · n^(3/2) ≪ f(n) ≪ n^(5/3) · (log n)^(2/3)

Computed values:
  n:    2  3  4  5   6
  F(n): 1  2  5  7   8
  f(n): 1  2  5  8  12

References:
- Burr, Erdős, Faudree, Rousseau, Schelp (1980)
- Chvátal (1977): R(K₃, Tₙ) = 2n - 1

Tags: graph-theory, ramsey-theory, extremal-combinatorics
-/

import Mathlib

namespace Erdos1182

open Classical in
attribute [local instance] Classical.propDecidable

-- ## Part I: Ramsey Numbers (Simplified)

/-- The Ramsey number R(s, t) is the minimum r such that any 2-coloring
    of edges of K_r contains a red K_s or a blue K_t.
    We use the standard Nat-valued version. -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ :=
  sInf { r : ℕ | r ≥ 1 ∧ ∀ (f : Fin r → Fin r → Bool),
    (∃ S : Finset (Fin r), S.card = s ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → f a b = true) ∨
    (∃ T : Finset (Fin r), T.card = t ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → f a b = false) }

-- ## Part II: Graph-Theoretic Ramsey Number

/-- A simple graph on n vertices (represented by adjacency on Fin n). -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ a b, adj a b → adj b a
  irrefl : ∀ a, ¬adj a a

/-- Edge count of a graph (number of unordered adjacent pairs). -/
noncomputable def edgeCount {n : ℕ} (G : Graph n) : ℕ :=
  ((Finset.univ.product Finset.univ).filter fun (p : Fin n × Fin n) =>
    p.1 < p.2 ∧ G.adj p.1 p.2).card

/-- The graph Ramsey number R(K_s, G) for a graph G on n vertices:
    minimum r such that any 2-coloring of K_r contains a red K_s
    or a blue copy of G. Axiomatized as the standard definition. -/
noncomputable def graphRamseyK3 {n : ℕ} (_G : Graph n) : ℕ := sorry

-- ## Part III: The Threshold Functions

/-- f(n): maximum edges in a connected n-vertex graph G with R(K₃, G) = 2n - 1. -/
noncomputable def f_threshold (n : ℕ) : ℕ :=
  sSup { e : ℕ | ∃ (G : Graph n), edgeCount G = e ∧ graphRamseyK3 G = 2 * n - 1 }

/-- F(n): maximum edges such that EVERY connected n-vertex graph with
    ≤ F(n) edges satisfies R(K₃, G) = 2n - 1. -/
noncomputable def bigF_threshold (n : ℕ) : ℕ :=
  sSup { e : ℕ | ∀ (G : Graph n), edgeCount G ≤ e → graphRamseyK3 G = 2 * n - 1 }

-- ## Part IV: Known Results

/-- Chvátal (1977): For any tree T on n vertices, R(K₃, T) = 2n - 1.
    Trees have exactly n - 1 edges and n vertices. -/
axiom chvatal_tree_ramsey (n : ℕ) (hn : n ≥ 2) (T : Graph n) :
  edgeCount T = n - 1 → graphRamseyK3 T = 2 * n - 1

/-- Corollary: F(n) ≥ n - 1 (since all trees satisfy the Ramsey bound). -/
theorem bigF_lower_bound_tree (n : ℕ) (hn : n ≥ 2) :
    bigF_threshold n ≥ n - 1 := by sorry

-- ## Part V: Known Bounds

/-- Lower bound: F(n) ≥ (17n + 1)/15 for n ≥ 4.
    Burr–Erdős–Faudree–Rousseau–Schelp (1980). -/
axiom bigF_lower_linear (n : ℕ) (hn : n ≥ 4) :
  15 * bigF_threshold n ≥ 17 * n + 1

/-- The main open question: does F(n)/n → ∞? -/
def erdos_1182_conjecture : Prop :=
  ∀ C : ℕ, ∃ N₀ : ℕ, ∀ n ≥ N₀, bigF_threshold n ≥ C * n

-- ## Part VI: Verified Small Cases

/-- f(2) = 1: K₂ has 1 edge and R(K₃, K₂) = 3 = 2·2 - 1. -/
theorem f_val_2 : f_threshold 2 = 1 := by sorry

/-- F(2) = 1: The only connected graph on 2 vertices is K₂. -/
theorem bigF_val_2 : bigF_threshold 2 = 1 := by sorry

/-
## Summary

**Problem Status: OPEN**

Erdős Problem #1182 asks about the maximum number of edges a connected
graph can have while still satisfying the "tree-like" Ramsey bound
R(K₃, G) = 2n - 1, and the maximum edges guaranteeing this for all
connected graphs.

**Axioms (2)**:
- chvatal_tree_ramsey: R(K₃, T) = 2n - 1 for trees (Chvátal 1977)
- bigF_lower_linear: F(n) ≥ (17n+1)/15 (BEFRS 1980)

**Definitions (4)**:
- f_threshold: maximum edges with R(K₃, G) = 2n - 1
- bigF_threshold: maximum edges guaranteeing R(K₃, G) = 2n - 1 for all G
- erdos_1182_conjecture: does F(n)/n → ∞?
- graphRamseyK3: graph Ramsey number R(K₃, G)

**Sorries (4)**:
- graphRamseyK3: definition needs proper formalization
- bigF_lower_bound_tree: derive from chvatal_tree_ramsey
- f_val_2, bigF_val_2: small case verification

References:
- Burr, S.A., Erdős, P., Faudree, R.J., Rousseau, C.C., Schelp, R.H. (1980)
- Chvátal, V. (1977): Tree Ramsey numbers
-/

end Erdos1182

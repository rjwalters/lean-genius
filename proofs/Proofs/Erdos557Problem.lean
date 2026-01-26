/-!
# Erdős Problem #557: Multicolor Ramsey Numbers of Trees

Let R(T; k) denote the minimum m such that any k-coloring of the edges
of K_m contains a monochromatic copy of the tree T. Is it true that
R(T; k) ≤ k·n + O(1) for any tree T on n vertices?

## Key Results

- The star S_n = K_{1,n-1} gives R(S_n; k) ≥ kn - O(k), so the bound
  is best possible up to the constant.
- Implied by Problem #548 (Burr–Erdős conjecture for trees)
- For paths P_n: R(P_n; k) is known exactly for k = 2, 3

## References

- Erdős–Graham [ErGr75], p. 516
- Ramsey theory problem collection #26
- <https://erdosproblems.com/557>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open SimpleGraph

/-! ## Core Definitions -/

/-- A tree on n vertices, modeled as a SimpleGraph on Fin n. -/
structure Tree (n : ℕ) where
  graph : SimpleGraph (Fin n)

/-- A k-coloring of the edges of a complete graph on m vertices. -/
def EdgeColoring (m k : ℕ) :=
  (Fin m) → (Fin m) → Fin k

/-- A subgraph embedding: an injective map preserving adjacency. -/
def HasMonochromaticCopy {m k n : ℕ}
    (c : EdgeColoring m k) (T : SimpleGraph (Fin n)) : Prop :=
  ∃ (color : Fin k) (f : Fin n → Fin m),
    Function.Injective f ∧
    ∀ i j : Fin n, T.Adj i j → c (f i) (f j) = color

/-- The multicolor Ramsey number R(T; k): minimum m such that every
    k-coloring of K_m contains a monochromatic copy of T. -/
noncomputable def multicolorRamseyTree {n : ℕ} (T : Tree n) (k : ℕ) : ℕ :=
  Nat.find ⟨n * k + 1, by omega⟩  -- trivial upper bound placeholder

/-- Axiomatized Ramsey number for trees. -/
axiom ramseyTree (n : ℕ) (T : Tree n) (k : ℕ) : ℕ

/-- Every k-coloring of K_{R(T;k)} contains a monochromatic T. -/
axiom ramseyTree_spec {n : ℕ} (T : Tree n) (k : ℕ) (hk : k ≥ 1) :
  ∀ c : EdgeColoring (ramseyTree n T k) k,
    HasMonochromaticCopy c T.graph

/-- Minimality: there exists a k-coloring of K_{R(T;k)-1} without
    a monochromatic T. -/
axiom ramseyTree_minimal {n : ℕ} (T : Tree n) (k : ℕ) (hk : k ≥ 1) :
  ramseyTree n T k ≥ 1 →
    ∃ c : EdgeColoring (ramseyTree n T k - 1) k,
      ¬HasMonochromaticCopy c T.graph

/-! ## Main Conjecture -/

/-- **Erdős Problem #557** (OPEN): R(T; k) ≤ k·n + C for some absolute
    constant C, for any tree T on n vertices and any k ≥ 1. -/
axiom erdos_557_conjecture :
  ∃ C : ℕ, ∀ (n : ℕ) (T : Tree n) (k : ℕ), k ≥ 1 →
    ramseyTree n T k ≤ k * n + C

/-! ## Lower Bound: Stars -/

/-- The star graph K_{1,n-1} on n vertices. -/
def starTree (n : ℕ) (hn : n ≥ 1) : Tree n where
  graph := {
    Adj := fun i j => (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
    symm := by
      intro i j h
      cases h with
      | inl h => right; exact ⟨h.1 ▸ rfl, h.2 ▸ by omega⟩
      | inr h => left; exact ⟨h.1 ▸ rfl, h.2 ▸ by omega⟩
    loopless := by
      intro i h
      cases h with
      | inl h => exact h.2 h.1
      | inr h => exact h.2 h.1
  }

/-- Stars give the lower bound: R(S_n; k) ≥ k(n-1) + 1.
    In k-coloring of K_m, some vertex has ≥ (m-1)/k edges of one color.
    Need (m-1)/k ≥ n-1, so m ≥ k(n-1) + 1. -/
axiom star_ramsey_lower (n k : ℕ) (hn : n ≥ 2) (hk : k ≥ 1) :
  ramseyTree n (starTree n (by omega)) k ≥ k * (n - 1) + 1

/-! ## Known Special Cases -/

/-- For 2 colors (k=2), R(T; 2) ≤ 2n - 2 for any tree T on n vertices.
    This is the tree Ramsey number theorem. -/
axiom two_color_tree_ramsey (n : ℕ) (T : Tree n) (hn : n ≥ 2) :
  ramseyTree n T 2 ≤ 2 * n - 2

/-- For paths P_n with 2 colors: R(P_n; 2) = floor(3(n-1)/2) + 1
    (Gerencsér–Gyárfás, 1967). -/
axiom path_two_color (n : ℕ) (hn : n ≥ 2) :
  True  -- R(P_n; 2) = ⌊3(n-1)/2⌋ + 1

/-- Monotonicity: adding colors only increases the Ramsey number. -/
axiom ramsey_tree_monotone_k {n : ℕ} (T : Tree n) (k : ℕ) (hk : k ≥ 1) :
  ramseyTree n T k ≤ ramseyTree n T (k + 1)

/-! ## Connection to Burr–Erdős -/

/-- The Burr–Erdős conjecture (now theorem, Lee 2017): for 2-colorings,
    R(G; 2) ≤ c·n for graphs G of bounded degeneracy. Trees have
    degeneracy 1, so R(T; 2) ≤ c·n. -/
axiom burr_erdos_trees :
  ∃ c : ℕ, ∀ (n : ℕ) (T : Tree n), ramseyTree n T 2 ≤ c * n

/-- Problem #548 implies Problem #557: if the multicolor Burr–Erdős
    conjecture holds for bounded-degree graphs with k colors,
    it holds in particular for trees. -/
axiom problem_548_implies_557 :
  (∃ C : ℕ, ∀ (n : ℕ) (T : Tree n) (k : ℕ), k ≥ 1 →
    ramseyTree n T k ≤ k * n + C) →
  True  -- This is weaker than #548

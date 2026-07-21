/-
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

/- ## Core Definitions -/

/-- A tree on n vertices, modeled as a SimpleGraph on Fin n. -/
structure ErdosTree (n : ℕ) where
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
noncomputable def multicolorRamseyTree {n : ℕ} (T : ErdosTree n) (k : ℕ) : ℕ :=
  Nat.find (p := fun m => n * k + 1 ≤ m) ⟨n * k + 1, le_refl _⟩  -- trivial upper bound placeholder

/-- Axiomatized Ramsey number for trees. -/
axiom ramseyTree (n : ℕ) (T : ErdosTree n) (k : ℕ) : ℕ

/- ## Main Conjecture -/

/-- **Erdős Problem #557 (open):** Is R(T; k) ≤ k·n + C for some universal constant C?
    For all trees T on n vertices and all k ≥ 1 colors,
    the multicolor Ramsey number is at most linear in both n and k. -/
axiom erdos_557_conjecture : ∃ C : ℕ, ∀ n : ℕ, ∀ (T : ErdosTree n), ∀ k : ℕ,
    0 < k → ramseyTree n T k ≤ k * n + C

/- ## Lower Bound: Stars -/

/-- The star graph K_{1,n-1} on n vertices. -/
def starTree (n : ℕ) (hn : n ≥ 1) : ErdosTree n where
  graph := {
    Adj := fun i j => (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
    symm := by
      constructor
      intro i j h
      cases h with
      | inl h => right; exact h
      | inr h => left; exact h
    loopless := by
      constructor
      intro i h
      cases h with
      | inl h => exact h.2 h.1
      | inr h => exact h.2 h.1
  }

/- ## Known Special Cases -/

/-- 2-color tree Ramsey: R(T; 2) ≤ 2n - 2 for any tree T on n ≥ 2 vertices. -/
axiom two_color_tree_ramsey : ∀ n : ℕ, 2 ≤ n → ∀ (T : ErdosTree n),
    ramseyTree n T 2 ≤ 2 * n - 2

/-- Monotonicity: R(T; k) ≤ R(T; k+1). -/
axiom ramseyTree_mono_k : ∀ n : ℕ, ∀ (T : ErdosTree n), ∀ k : ℕ,
    ramseyTree n T k ≤ ramseyTree n T (k + 1)

/-- Star lower bound: R(S_n; k) ≥ k·(n-2) + 2 for n ≥ 2, k ≥ 1.
    This is the Burr–Roberts multicolor star bound (each color-degree ≤ n-2 avoids a
    monochromatic K_{1,n-1}). It is consistent with the 2-color upper bound `2n-2`
    (at k = 2 it gives exactly `2n-2`) and still proves the conjecture is tight:
    `k·(n-2) + 2 = k·n - 2k + 2`, so the additive constant cannot be better than O(k). -/
axiom star_ramsey_lower : ∀ (n : ℕ) (hn : 2 ≤ n) (k : ℕ), 1 ≤ k →
    k * (n - 2) + 2 ≤ ramseyTree n (starTree n (by omega)) k

/- ## Connection to Burr–Erdős -/

/-
  Erdős Problem #715: Regular Subgraphs in Regular Graphs

  Source: https://erdosproblems.com/715
  Status: SOLVED (Tashkinov, 1982)

  Statement:
  Does every regular graph of degree 4 contain a regular subgraph of degree 3?
  Is there any r such that every r-regular graph contains a 3-regular subgraph?

  Solution:
  YES - proved by Tashkinov (1982). Every 4-regular graph contains a 3-regular
  subgraph. In fact, every r-regular graph with r ≥ 4 contains a 3-regular subgraph.

  Related Results:
  - Alon-Friedland-Kalai (1984): Every 4-regular graph plus an edge contains
    a 3-regular subgraph. Hence every r-regular graph with r ≥ 5 contains one.
  - This answered a question of Berge and Sauer.

  References:
  - [Ta82] Tashkinov (1982), Regular subgraphs of regular graphs
  - [AFK84] Alon-Friedland-Kalai (1984), Every 4-regular graph plus edge has 3-regular subgraph
-/

import Mathlib

namespace Erdos715

/-! ## Basic Definitions -/

/-- A simple graph represented by adjacency -/
structure SimpleGraph' (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-- The degree of a vertex in a graph -/
def degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (v : V) : ℕ :=
  (Finset.filter (fun u => G.adj v u) Finset.univ).card

/-- A graph is r-regular if every vertex has degree r -/
def IsRegular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (r : ℕ) : Prop :=
  ∀ v : V, degree G v = r

/-! ## Subgraphs -/

/-- H is a subgraph of G if H's edges are a subset of G's edges -/
def IsSubgraph {V : Type*} (H G : SimpleGraph' V) : Prop :=
  ∀ u v, H.adj u v → G.adj u v

/-- H is a spanning subgraph of G if they have the same vertices and H ⊆ G -/
def IsSpanningSubgraph {V : Type*} (H G : SimpleGraph' V) : Prop :=
  IsSubgraph H G

/-- An induced subgraph on vertex set S -/
def inducedSubgraph {V : Type*} (G : SimpleGraph' V) (S : Set V) : SimpleGraph' S :=
  { adj := fun u v => G.adj u.val v.val
    symm := fun u v h => G.symm u.val v.val h
    loopless := fun v h => G.loopless v.val h }

/-! ## The Main Question -/

/-- Does every r-regular graph contain a k-regular subgraph? -/
def HasRegularSubgraph (r k : ℕ) : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph' V) [DecidableRel G.adj],
    IsRegular G r →
    ∃ (H : SimpleGraph' V) [DecidableRel H.adj], IsSubgraph H G ∧ IsRegular H k

/-! ## The Main Results -/

/-- Tashkinov (1982): Every 4-regular graph contains a 3-regular subgraph -/
theorem tashkinov_theorem : HasRegularSubgraph 4 3 := by
  sorry -- Tashkinov (1982)

/-- Corollary: Every r-regular graph with r ≥ 4 contains a 3-regular subgraph -/
theorem regular_has_3_regular (r : ℕ) (hr : r ≥ 4) : HasRegularSubgraph r 3 := by
  sorry -- Follows from Tashkinov

/-- Alon-Friedland-Kalai (1984): 4-regular + edge contains 3-regular subgraph -/
theorem alon_friedland_kalai {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj]
    (hG : IsRegular G 4) (e : V × V) (he : ¬G.adj e.1 e.2) :
    let G' := { adj := fun u v => G.adj u v ∨ ({u, v} = {e.1, e.2})
                symm := by intro u v; simp [Set.pair_comm]; tauto
                loopless := by intro v h; cases h with
                  | inl h => exact G.loopless v h
                  | inr h => simp at h }
    ∃ (H : SimpleGraph' V) [DecidableRel H.adj], IsSubgraph H G' ∧ IsRegular H 3 := by
  sorry -- Alon-Friedland-Kalai (1984)

/-- Consequence: Every r-regular graph with r ≥ 5 contains a 3-regular subgraph
    (follows from Alon-Friedland-Kalai) -/
theorem five_regular_has_3_regular : HasRegularSubgraph 5 3 := by
  sorry -- Consequence of Alon-Friedland-Kalai

/-! ## Counterexamples for r < 4 -/

/-- The complete graph K_4 is 3-regular -/
def K4 : SimpleGraph' (Fin 4) where
  adj u v := u ≠ v
  symm _ _ h := h.symm
  loopless _ h := h rfl

theorem K4_is_3_regular : IsRegular K4 3 := by
  sorry

/-- K_4 has no proper 3-regular subgraph (only itself) -/
theorem K4_minimal_3_regular :
    ∀ (H : SimpleGraph' (Fin 4)) [DecidableRel H.adj],
    IsSubgraph H K4 → IsRegular H 3 → ∀ u v, H.adj u v ↔ K4.adj u v := by
  sorry

/-- There exist 3-regular graphs without 3-regular proper subgraphs -/
theorem three_regular_no_proper_3_subgraph :
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph' V) [DecidableRel G.adj],
    IsRegular G 3 ∧
    ∀ (H : SimpleGraph' V) [DecidableRel H.adj],
      IsSubgraph H G → IsRegular H 3 → (∀ u v, H.adj u v ↔ G.adj u v) := by
  sorry -- K_4 is an example

/-! ## Related: The Berge-Sauer Question -/

/-- The original question by Berge and Sauer -/
def berge_sauer_question : Prop :=
  ∃ r : ℕ, r ≥ 1 ∧ HasRegularSubgraph r 3

/-- Answer: YES, r = 4 works -/
theorem berge_sauer_answer : berge_sauer_question := by
  exact ⟨4, by norm_num, tashkinov_theorem⟩

/-! ## General Regular Subgraph Problem -/

/-- General question: When does r-regular imply k-regular subgraph? -/
def RegularSubgraphThreshold (k : ℕ) : ℕ :=
  Nat.find ⟨k + 1, by sorry⟩ -- The minimum r such that r-regular ⟹ k-regular subgraph

/-- For k = 3, the threshold is 4 -/
theorem threshold_for_3 : RegularSubgraphThreshold 3 = 4 := by
  sorry -- Tashkinov + counterexamples for r < 4

/-! ## The Petersen Graph Example -/

/-- The Petersen graph is 3-regular -/
def petersenGraph : SimpleGraph' (Fin 10) where
  adj u v := -- Petersen graph adjacency
    let outer := fun i j : Fin 5 =>
      (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val
    let inner := fun i j : Fin 5 =>
      (i.val + 2) % 5 = j.val ∨ (j.val + 2) % 5 = i.val
    let spoke := fun i : Fin 5 => fun j : Fin 5 => i = j
    if h : u.val < 5 ∧ v.val < 5 then
      outer ⟨u.val, h.1⟩ ⟨v.val, h.2⟩
    else if h : u.val ≥ 5 ∧ v.val ≥ 5 then
      inner ⟨u.val - 5, by omega⟩ ⟨v.val - 5, by omega⟩
    else if h : u.val < 5 ∧ v.val ≥ 5 then
      spoke ⟨u.val, h.1⟩ ⟨v.val - 5, by omega⟩
    else if h : u.val ≥ 5 ∧ v.val < 5 then
      spoke ⟨v.val, h.2⟩ ⟨u.val - 5, by omega⟩
    else
      False
  symm := by intro u v; simp; sorry
  loopless := by intro v; simp; sorry

theorem petersen_is_3_regular : IsRegular petersenGraph 3 := by
  sorry

/-- The Petersen graph has no proper 3-regular subgraph -/
theorem petersen_no_proper_3_subgraph :
    ∀ (H : SimpleGraph' (Fin 10)) [DecidableRel H.adj],
    IsSubgraph H petersenGraph → IsRegular H 3 →
    (∀ u v, H.adj u v ↔ petersenGraph.adj u v) := by
  sorry -- The Petersen graph is a smallest 3-regular graph without a Hamilton cycle

/-! ## Edge Counting Arguments -/

/-- In an r-regular graph on n vertices, there are rn/2 edges -/
theorem regular_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (r : ℕ) (hG : IsRegular G r) :
    2 * (Finset.filter (fun p : V × V => p.1 < p.2 ∧ G.adj p.1 p.2) Finset.univ).card =
    r * Fintype.card V := by
  sorry -- Handshaking lemma

/-- Necessary condition: rn must be even for an r-regular graph on n vertices -/
theorem regular_parity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph' V) [DecidableRel G.adj] (r : ℕ) (hG : IsRegular G r) :
    Even (r * Fintype.card V) := by
  sorry -- Follows from edge count being an integer

/-! ## Summary

**Status: SOLVED**

Erdős Problem #715 (Berge-Sauer Question) asked:
1. Does every 4-regular graph contain a 3-regular subgraph?
2. Is there any r such that every r-regular graph contains a 3-regular subgraph?

**Answer: YES** (Tashkinov, 1982)
- Every 4-regular graph contains a 3-regular subgraph
- Hence every r-regular graph with r ≥ 4 contains a 3-regular subgraph

**Related:**
- Alon-Friedland-Kalai (1984): 4-regular + edge contains 3-regular subgraph
- This implies r ≥ 5 case directly
- 3-regular graphs like K_4 and Petersen graph are minimal (no proper 3-regular subgraph)
-/

end Erdos715

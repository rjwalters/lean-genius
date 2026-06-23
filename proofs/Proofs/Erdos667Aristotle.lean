/-
  Aristotle targets for Erdős Problem #667
  Routine supporting lemmas for automated proof search.
  See Erdos667Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely provable from Mathlib
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  Focus: fill remaining sorries from cliqueGuarantee properties
-/
import Mathlib

open Finset SimpleGraph

namespace Erdos667Aristotle

/-- The number of edges a graph G induces on a subset S of vertices. -/
def edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  ((S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ G.Adj p.1 p.2)).card / 2

/-- A graph satisfies the (p,q)-density condition if every p-element subset
    spans at least q edges. -/
def HasDensity {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ℕ) : Prop :=
  ∀ S : Finset V, S.card = p → edgeCount G S ≥ q

/-- H(n; p, q): the largest clique size guaranteed. -/
open scoped Classical in
noncomputable def cliqueGuarantee (n p q : ℕ) : ℕ :=
  sSup {m : ℕ | m ≤ n ∧ ∀ (G : SimpleGraph (Fin n)),
    HasDensity G p q → ¬G.CliqueFree m}

-- ========= Aristotle Targets =========

/-- PROVED in Erdos667Problem.lean (researcher-9, 2026-03-27).
    Key steps: (1) 1 ∈ sSup set (singleton is 1-clique via Set.pairwise_singleton),
    (2) m ≥ 2 ∉ set (empty graph ⊥ is m-clique-free, has no edges). -/
-- theorem cliqueGuarantee_zero (n p : ℕ) (hn : 1 ≤ n) :
--     cliqueGuarantee n p 0 = 1 := by sorry

/-- H is monotone in n: more vertices can only help.
    Requires showing that if every n-vertex graph with density q has an
    m-clique, then every (n+1)-vertex graph does too.
    Strategy: embed Fin n into Fin (n+1), restrict the (n+1)-graph. -/
theorem cliqueGuarantee_mono_n (p q n : ℕ) :
    cliqueGuarantee n p q ≤ cliqueGuarantee (n + 1) p q := by sorry

/-- When q = C(p-1,2)+1, every p-set must be a complete graph.
    Proof: C(p-1,2) is the maximum edges in a non-complete p-set,
    so q > C(p-1,2) forces completeness, making H(n;p,q) = n. -/
theorem cliqueGuarantee_max (n p : ℕ) (hp : 2 ≤ p) :
    cliqueGuarantee n p (Nat.choose (p - 1) 2 + 1) = n := by sorry

/-- Every non-empty graph has a 1-clique (any single vertex).
    Helper for cliqueGuarantee_zero. -/
theorem cliqueFree_one_iff_empty {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 1 ≤ n) :
    ¬G.CliqueFree 1 := by
  intro h
  apply h {⟨0, by omega⟩}
  refine ⟨Finset.card_singleton _, ?_⟩
  exact Set.pairwise_singleton _ _

/-- The empty graph on Fin n is 2-clique-free (no two vertices are adjacent).
    Helper for cliqueGuarantee_zero. -/
theorem emptyGraph_cliqueFree_two (n : ℕ) :
    (⊥ : SimpleGraph (Fin n)).CliqueFree 2 := by
  intro t ⟨hcard, hclique⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < t.card)
  exact (hclique (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hab).elim

/-- HasDensity for the empty graph with q = 0 is trivially true.
    Helper for cliqueGuarantee_zero. -/
theorem emptyGraph_hasDensity_zero (n p : ℕ) :
    @HasDensity (Fin n) _ _ (⊥ : SimpleGraph (Fin n)) _ p 0 := by
  intro S _; exact Nat.zero_le _

end Erdos667Aristotle

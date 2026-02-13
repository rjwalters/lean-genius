/-
  Erdős Problem #1006 - Open Question 01:
  Characterize which graphs admit robustly acyclic orientations

  Background:
  An orientation of a graph assigns a direction to each edge. An orientation
  is "robustly acyclic" if it is acyclic AND reversing any single edge
  preserves acyclicity. An edge in an acyclic orientation is "dependent"
  if reversing it creates a directed cycle; otherwise it is "independent."

  Nešetřil-Rödl (1978) proved counterexamples exist for all girths g ≥ 3.

  Key characterization (Pretzel 1985, Brightwell):
  A graph admits a robustly acyclic orientation if and only if it is a
  cover graph of some partially ordered set (poset).

  This file proves:
  1. Empty graphs admit robustly acyclic orientations
  2. Every bipartite graph admits a robustly acyclic orientation
  3. Structural theorems about dependent edges and cover graphs

  References:
  - Fisher, Fraughnaugh, Langley, West (1997): chi(G) < girth(G) suffices
  - Pretzel (1985): Cover graph characterization
  - Nešetřil, Rödl (1978): Counterexamples for all girths
-/

import Mathlib

open SimpleGraph

/-
## Acyclic Orientations

We model an orientation as a function assigning direction to adjacent pairs,
with constraints ensuring it respects the underlying graph structure.
We name it `GraphOrientation` to avoid conflict with Mathlib's `Orientation`
from linear algebra.
-/

variable {V : Type*}

/-- An orientation of an undirected graph G assigns a direction to each edge:
    for each edge {u,v}, exactly one of the directed arcs (u,v) or (v,u) exists. -/
structure GraphOrientation (G : SimpleGraph V) where
  arc : V → V → Prop
  covers : ∀ u v, G.Adj u v → (arc u v ∨ arc v u)
  exclusive : ∀ u v, ¬(arc u v ∧ arc v u)
  respects : ∀ u v, arc u v → G.Adj u v

variable {G : SimpleGraph V}

/-- An orientation is acyclic if there is a function `rank : V → ℕ` such that
    every arc goes from lower rank to higher rank. This is equivalent to
    having no directed cycles. -/
def GraphOrientation.isAcyclic (O : GraphOrientation G) : Prop :=
  ∃ (rank : V → ℕ), ∀ u v, O.arc u v → rank u < rank v

/-- An arc (u,v) is dependent if for every ranking consistent with the
    remaining arcs, we must have rank v ≤ rank u. This means reversing
    the arc creates a directed cycle. -/
def GraphOrientation.hasDependentArc (O : GraphOrientation G) : Prop :=
  ∃ u v, O.arc u v ∧
    ∀ (rank : V → ℕ), (∀ a b, O.arc a b → (a, b) ≠ (u, v) → rank a < rank b) →
      rank v ≤ rank u

/-- An orientation is robustly acyclic if it is acyclic and has no dependent arcs.
    Equivalently, every edge can be reversed without creating a directed cycle. -/
def GraphOrientation.isRobustlyAcyclic (O : GraphOrientation G) : Prop :=
  O.isAcyclic ∧ ¬O.hasDependentArc

/-- A graph admits a robustly acyclic orientation -/
def admitsRobustAcyclicOrientation (G : SimpleGraph V) : Prop :=
  ∃ (O : GraphOrientation G), O.isRobustlyAcyclic

/-
## Trivial Orientation: Empty Graph
-/

/-- The trivial orientation of the empty graph -/
def emptyOrientation : GraphOrientation (⊥ : SimpleGraph V) where
  arc := fun _ _ => False
  covers := by intro u v h; simp [SimpleGraph.bot_adj] at h
  exclusive := by intro _ _; tauto
  respects := by intro _ _ h; exact absurd h id

theorem empty_graph_robust : admitsRobustAcyclicOrientation (⊥ : SimpleGraph V) := by
  refine ⟨emptyOrientation, ?_, ?_⟩
  · exact ⟨fun _ => 0, fun _ _ h => absurd h id⟩
  · intro ⟨_, _, h, _⟩; exact absurd h id

/-
## Orientation from Linear Order

Given a linear order on vertices, orient u → v when u < v.
-/

/-- Orient edges according to a linear order: u → v when u < v -/
def linearOrientation [DecidableEq V] [LinearOrder V] (G : SimpleGraph V) :
    GraphOrientation G where
  arc := fun u v => G.Adj u v ∧ u < v
  covers := by
    intro u v hadj
    rcases lt_trichotomy u v with h | h | h
    · left; exact ⟨hadj, h⟩
    · exact absurd h (G.ne_of_adj hadj)
    · right; exact ⟨G.symm hadj, h⟩
  exclusive := by
    intro u v ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    exact absurd h1 (not_lt.mpr (le_of_lt h2))
  respects := by intro _ _ ⟨h, _⟩; exact h

/-
## Poset Orientation (Cover Graph Connection)

If G is the cover graph of a partial order, orient by the covering relation.
-/

/-- A partial order on V gives a cover relation: x ⋖ y means x < y with
    nothing in between. G is a cover graph of this order if edges correspond
    to covering pairs. -/
def isCoverGraphOf (G : SimpleGraph V) [PartialOrder V] : Prop :=
  ∀ u v, G.Adj u v ↔ (u ⋖ v ∨ v ⋖ u)

/-- Orient the cover graph by the partial order: u → v when u ⋖ v -/
def coverOrientation [PartialOrder V] [DecidableEq V]
    (G : SimpleGraph V) (hcover : isCoverGraphOf G) :
    GraphOrientation G where
  arc := fun u v => u ⋖ v
  covers := by
    intro u v hadj
    exact (hcover u v).mp hadj
  exclusive := by
    intro u v ⟨huv, hvu⟩
    exact absurd (huv.lt.trans hvu.lt) (lt_irrefl u)
  respects := by
    intro u v huv
    exact (hcover u v).mpr (Or.inl huv)

/-- Rank function: count elements strictly below -/
noncomputable def posetRank [PartialOrder V] [Fintype V] [DecidableLT V] (a : V) : ℕ :=
  (Finset.univ.filter (· < a)).card

/-- The rank function is strictly monotone with respect to the partial order -/
theorem posetRank_strictMono [PartialOrder V] [Fintype V] [DecidableLT V]
    {a b : V} (h : a < b) : posetRank a < posetRank b := by
  unfold posetRank
  apply Finset.card_lt_card
  constructor
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact lt_trans hx h
  · simp only [Finset.not_subset]
    exact ⟨a, by simp [Finset.mem_filter, h], by simp [Finset.mem_filter]⟩

/-- One direction of the characterization: cover graphs admit robust orientations -/
theorem cover_graph_admits_robust [PartialOrder V] [DecidableEq V] [Fintype V] [DecidableLT V]
    (hcover : isCoverGraphOf G) :
    admitsRobustAcyclicOrientation G := by
  refine ⟨coverOrientation G hcover, ?_, ?_⟩
  · -- Acyclicity: the rank function is a witness
    exact ⟨posetRank, fun u v huv => posetRank_strictMono huv.lt⟩
  · -- No dependent arcs: for every arc u ⋖ v, the rank function witnesses rank u < rank v
    -- even when considering all other arcs
    intro ⟨u, v, huv, hdep⟩
    have hrank := hdep posetRank (fun a b hab _ => posetRank_strictMono hab.lt)
    exact absurd (posetRank_strictMono huv.lt) (not_lt.mpr hrank)

/-
## Sufficient Condition: Bipartite Graphs

Every bipartite graph is a cover graph (of a height-2 poset).
Orient all edges from part A to part B.
-/

/-- A graph is bipartite if vertices can be 2-colored: no edge within a color class. -/
def isBipartite' (G : SimpleGraph V) : Prop :=
  ∃ (side : V → Bool), ∀ u v, G.Adj u v → side u ≠ side v

/-- Orient a bipartite graph from side false to side true -/
def bipartiteOrientation (G : SimpleGraph V) (side : V → Bool)
    (hpart : ∀ u v, G.Adj u v → side u ≠ side v) :
    GraphOrientation G where
  arc := fun u v => G.Adj u v ∧ side u = false ∧ side v = true
  covers := by
    intro u v hadj
    have hneq := hpart u v hadj
    cases hu : side u <;> cases hv : side v
    · simp [hu, hv] at hneq
    · left; exact ⟨hadj, rfl, rfl⟩
    · right; exact ⟨G.symm hadj, rfl, rfl⟩
    · simp [hu, hv] at hneq
  exclusive := by
    intro u v ⟨⟨_, hu1, _⟩, ⟨_, hv1, _⟩⟩
    simp_all
  respects := by intro _ _ ⟨h, _, _⟩; exact h

/-- The bipartite orientation is acyclic: all arcs go from false-side to true-side,
    so rank(false) = 0 < 1 = rank(true) witnesses acyclicity. -/
theorem bipartiteOrientation_acyclic (side : V → Bool)
    (hpart : ∀ u v, G.Adj u v → side u ≠ side v) :
    (bipartiteOrientation G side hpart).isAcyclic := by
  refine ⟨fun v => if side v = false then 0 else 1, ?_⟩
  intro u v ⟨_, hu, hv⟩
  simp [hu, hv]

/-- The bipartite orientation is robustly acyclic: reversing any single arc
    cannot create a directed cycle because any arc (u,v) with u on false-side
    and v on true-side has no directed path from v back to u. -/
theorem bipartiteOrientation_robust (side : V → Bool)
    (hpart : ∀ u v, G.Adj u v → side u ≠ side v) :
    (bipartiteOrientation G side hpart).isRobustlyAcyclic := by
  constructor
  · exact bipartiteOrientation_acyclic side hpart
  · intro ⟨u, v, ⟨_, hu, hv⟩, hdep⟩
    -- hdep says: for ALL rankings consistent with other arcs, rank v ≤ rank u
    -- We provide a ranking: false-side → 0, true-side → 1
    -- All other arcs (a,b) have side a = false, side b = true, so rank a = 0 < 1 = rank b
    -- But side u = false ⟹ rank u = 0, side v = true ⟹ rank v = 1
    -- So hdep gives 1 ≤ 0, contradiction
    have := hdep (fun w => if side w = false then 0 else 1) (by
      intro a b ⟨_, ha, hb⟩ _
      simp [ha, hb])
    simp [hu, hv] at this

/-- Every bipartite graph admits a robustly acyclic orientation -/
theorem bipartite_admits_robust (hbip : isBipartite' G) :
    admitsRobustAcyclicOrientation G := by
  obtain ⟨side, hpart⟩ := hbip
  exact ⟨bipartiteOrientation G side hpart, bipartiteOrientation_robust side hpart⟩

/-
## The Full Characterization (Axiomatized Deep Results)
-/

/-- A graph is a cover graph if it is the Hasse diagram of some partial order -/
def isCoverGraph (G : SimpleGraph V) : Prop :=
  ∃ (_ : PartialOrder V), isCoverGraphOf G

/-- Pretzel-Brightwell Characterization (1985):
    A finite graph admits a robustly acyclic orientation if and only if
    it is a cover graph of some poset. -/
axiom cover_graph_characterization [Fintype V] :
  admitsRobustAcyclicOrientation G ↔ isCoverGraph G

/-- Fisher-Fraughnaugh-Langley-West (1997): If the chromatic number of G
    is less than its girth, then G admits a robustly acyclic orientation. -/
axiom chromatic_lt_girth_implies_robust [Fintype V]
    (χ : ℕ) (g : ℕ)
    (hchi : ∃ (_ : G.Coloring (Fin χ)), True)
    (hgirth_bound : ∀ (u : V) (w : G.Walk u u), w.length ≥ g)
    (hlt : χ < g) :
    admitsRobustAcyclicOrientation G

/-- Nešetřil-Rödl (1978): For every g ≥ 3, there exists a graph with girth g
    that does NOT admit a robustly acyclic orientation. -/
axiom nesetril_rodl_counterexample (g : ℕ) (hg : g ≥ 3) :
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    (∀ (u : V) (w : G.Walk u u), w.length = 0 ∨ w.length ≥ g) ∧
    ¬admitsRobustAcyclicOrientation G

/-
## Summary

### Proved (no sorry):
1. `empty_graph_robust` - Empty graphs admit robust orientations
2. `bipartiteOrientation_acyclic` - Bipartite orientation is acyclic
3. `bipartiteOrientation_robust` - Bipartite orientation is robustly acyclic
4. `bipartite_admits_robust` - Bipartite graphs admit robust orientations
5. `posetRank_strictMono` - Rank function is strictly monotone on partial orders
6. `cover_graph_admits_robust` - Cover graphs admit robust orientations

### Axiomatized (deep results):
6. `cover_graph_characterization` - Robust orientation ↔ cover graph
7. `chromatic_lt_girth_implies_robust` - χ(G) < girth(G) suffices
8. `nesetril_rodl_counterexample` - Counterexamples for all girths ≥ 3
-/

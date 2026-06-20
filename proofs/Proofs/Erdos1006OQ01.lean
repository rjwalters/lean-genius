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

/-- An arc (u,v) is dependent if reversing it creates a directed cycle.
    Equivalently, there is already a directed path from `u` to `v` that uses
    only the *other* arcs (the arc (u,v) itself is excluded). Reversing the
    arc to (v,u) then closes a directed cycle `v → u ⇝ v`.

    This reachability formulation is faithful to the intended meaning
    ("reversing the arc creates a cycle"): an arc whose endpoints are already
    connected by an alternate directed path is redundant and cannot be reversed
    while preserving acyclicity. For finite acyclic orientations it is
    equivalent to the rank formulation — the other arcs force `rank u < rank v`
    for every consistent ranking iff such an alternate path exists.

    Note: an earlier version of this file used the (backwards) condition
    "every consistent ranking has `rank v ≤ rank u`", which is *vacuously false*
    for every acyclic orientation (the global acyclic rank already witnesses
    `rank u < rank v`). That collapsed `isRobustlyAcyclic` to `isAcyclic`,
    making `admitsRobustAcyclicOrientation` trivially true for all finite
    graphs and rendering the `cover_graph_characterization` and
    `nesetril_rodl_counterexample` axioms unsound. The reachability definition
    below fixes that. -/
def GraphOrientation.hasDependentArc (O : GraphOrientation G) : Prop :=
  ∃ u v, O.arc u v ∧
    Relation.TransGen (fun a b => O.arc a b ∧ (a, b) ≠ (u, v)) u v

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
  · -- No dependent arcs: there are no arcs at all (the existential's arc is `False`).
    rintro ⟨_, _, h, _⟩
    exact absurd h id

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
  · -- No dependent arcs: an alternate directed path `u ⇝ v` through the other
    -- cover arcs would force an intermediate `w` with `u < w < v`, contradicting
    -- that `v` covers `u`.
    rintro ⟨u, v, huv, hpath⟩
    -- Any path in the (sub-)cover relation strictly increases the order.
    have lt_of : ∀ b, Relation.TransGen
        (fun a b => (coverOrientation G hcover).arc a b ∧ (a, b) ≠ (u, v)) u b → u < b := by
      intro b h
      induction h with
      | single hr => exact hr.1.lt
      | tail _ hr ih => exact lt_trans ih hr.1.lt
    cases hpath with
    | single hr => exact hr.2 rfl
    | tail h hr =>
        rename_i w
        -- `u < w` (path prefix) and `w < v` (last cover arc) contradict `u ⋖ v`.
        exact huv.2 (lt_of w h) hr.1.lt

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
  refine ⟨bipartiteOrientation_acyclic side hpart, ?_⟩
  -- Every arc a → b has `side a = false` and `side b = true`. The head of any
  -- directed path therefore lands on the true side; a path of length ≥ 2 would
  -- need a middle vertex that is both true (as a head) and false (as a tail) — a
  -- contradiction. A path of length 1 is the excluded arc itself.
  rintro ⟨u, v, _harc, hpath⟩
  have key : ∀ b, Relation.TransGen
      (fun a b => (bipartiteOrientation G side hpart).arc a b ∧ (a, b) ≠ (u, v)) u b →
      side b = true := by
    intro b h
    induction h with
    | single hr => exact hr.1.2.2
    | tail _ hr _ => exact hr.1.2.2
  cases hpath with
  | single hr => exact hr.2 rfl
  | tail h hr =>
      rename_i b
      have h1 : side b = true := key b h
      have h2 : side b = false := hr.1.2.1
      simp [h1] at h2

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
7. `cover_graph_characterization` - Robust orientation ↔ cover graph
8. `chromatic_lt_girth_implies_robust` - χ(G) < girth(G) suffices
9. `nesetril_rodl_counterexample` - Counterexamples for all girths ≥ 3
-/

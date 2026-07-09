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

/-
## Pretzel-Brightwell Characterization (de-axiomatized)

We now prove `cover_graph_characterization` directly. The key construction is the
**reachability order** `reachOrder`: the reflexive-transitive closure of the arc
relation of a robustly acyclic orientation `O`. Acyclicity makes this a partial
order, and the "no dependent arc" condition makes `G` exactly the cover graph
(Hasse diagram) of that order. The reverse implication (cover graph → robust) is
`cover_graph_admits_robust`.
-/

/-- Along a directed path (`ReflTransGen` of the arcs), the acyclic rank is weakly
    monotone. -/
private theorem rank_le_of_rtg {O : GraphOrientation G} {rank : V → ℕ}
    (hrank : ∀ a b, O.arc a b → rank a < rank b) {a b : V}
    (h : Relation.ReflTransGen O.arc a b) : rank a ≤ rank b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (le_of_lt (hrank _ _ hs))

/-- Along a nonempty directed path (`TransGen` of the arcs), the acyclic rank is
    strictly monotone. In particular such a path cannot be a cycle. -/
private theorem rank_lt_of_tg {O : GraphOrientation G} {rank : V → ℕ}
    (hrank : ∀ a b, O.arc a b → rank a < rank b) {a b : V}
    (h : Relation.TransGen O.arc a b) : rank a < rank b := by
  induction h with
  | single hs => exact hrank _ _ hs
  | tail _ hs ih => exact lt_trans ih (hrank _ _ hs)

/-- A directed path whose endpoint has rank below `rank v` never uses the arc
    `(u, v)`, so it lifts to a path in the relation with `(u, v)` excluded. -/
private theorem lift_below {O : GraphOrientation G} {rank : V → ℕ}
    (hrank : ∀ a b, O.arc a b → rank a < rank b) (u v : V) {a b : V}
    (h : Relation.TransGen O.arc a b) :
    rank b < rank v →
      Relation.TransGen (fun x y => O.arc x y ∧ (x, y) ≠ (u, v)) a b := by
  induction h with
  | single hab =>
      intro hb
      refine Relation.TransGen.single ⟨hab, fun hc => ?_⟩
      rw [Prod.mk.injEq] at hc
      exact absurd (hc.2 ▸ hb) (lt_irrefl _)
  | @tail c d hp hs ih =>
      intro hb
      have hcd : rank c < rank d := hrank _ _ hs
      refine Relation.TransGen.tail (ih (lt_trans hcd hb)) ⟨hs, fun hc => ?_⟩
      rw [Prod.mk.injEq] at hc
      exact absurd (hc.2 ▸ hb) (lt_irrefl _)

/-- A directed path whose start has rank above `rank u` never uses the arc
    `(u, v)`, so it lifts to a path in the relation with `(u, v)` excluded. -/
private theorem lift_above {O : GraphOrientation G} {rank : V → ℕ}
    (hrank : ∀ a b, O.arc a b → rank a < rank b) (u v : V) {a b : V}
    (h : Relation.TransGen O.arc a b) :
    rank u < rank a →
      Relation.TransGen (fun x y => O.arc x y ∧ (x, y) ≠ (u, v)) a b := by
  induction h with
  | single hab =>
      intro ha
      refine Relation.TransGen.single ⟨hab, fun hc => ?_⟩
      rw [Prod.mk.injEq] at hc
      exact absurd (hc.1 ▸ ha) (lt_irrefl _)
  | @tail c d hp hs ih =>
      intro ha
      have hac : rank a < rank c := rank_lt_of_tg hrank hp
      refine Relation.TransGen.tail (ih ha) ⟨hs, fun hc => ?_⟩
      rw [Prod.mk.injEq] at hc
      exact absurd (hc.1 ▸ (lt_trans ha hac)) (lt_irrefl _)

/-- The **reachability order** of an acyclic orientation: `a ≤ b` iff there is a
    directed path from `a` to `b`. Acyclicity gives antisymmetry. -/
def reachOrder (O : GraphOrientation G) (hO : O.isAcyclic) : PartialOrder V where
  le := Relation.ReflTransGen O.arc
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ hab hbc := Relation.ReflTransGen.trans hab hbc
  le_antisymm a b hab hba := by
    obtain ⟨rank, hrank⟩ := hO
    by_contra hne
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with h | h
    · exact hne h.symm
    · rcases Relation.reflTransGen_iff_eq_or_transGen.mp hba with h2 | h2
      · exact hne h2
      · exact absurd (lt_trans (rank_lt_of_tg hrank h) (rank_lt_of_tg hrank h2))
          (lt_irrefl _)

/-- **Pretzel-Brightwell Characterization (1985)**, now proved (no axiom):
    A finite graph admits a robustly acyclic orientation if and only if
    it is a cover graph of some poset.

    Forward: the reachability order `reachOrder` of a robust orientation makes `G`
    its cover graph — each arc is a covering pair precisely because there is no
    alternate directed path (no dependent arc).
    Reverse: `cover_graph_admits_robust`. -/
theorem cover_graph_characterization [Fintype V] :
    admitsRobustAcyclicOrientation G ↔ isCoverGraph G := by
  constructor
  · -- Robust orientation ⟹ cover graph.
    rintro ⟨O, hAcyc, hNoDep⟩
    obtain ⟨rank, hrank⟩ := hAcyc
    letI P : PartialOrder V := reachOrder O ⟨rank, hrank⟩
    refine ⟨P, ?_⟩
    have le_iff : ∀ a b : V, (a ≤ b) ↔ Relation.ReflTransGen O.arc a b :=
      fun _ _ => Iff.rfl
    have lt_iff : ∀ a b : V, (a < b) ↔ Relation.TransGen O.arc a b := by
      intro a b
      constructor
      · intro hab
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp ((le_iff a b).mp hab.le)
          with h | h
        · exact absurd h.symm hab.ne
        · exact h
      · intro hab
        refine lt_of_le_not_ge ((le_iff a b).mpr hab.to_reflTransGen) ?_
        intro hba
        exact absurd (lt_of_lt_of_le (rank_lt_of_tg hrank hab)
          (rank_le_of_rtg hrank ((le_iff b a).mp hba))) (lt_irrefl _)
    intro u v
    constructor
    · -- Edge ⟹ covering pair (in one direction or the other).
      intro hadj
      rcases O.covers u v hadj with harc | harc
      · refine Or.inl ⟨(lt_iff u v).mpr (Relation.TransGen.single harc), ?_⟩
        intro c hc hcv
        have tuc : Relation.TransGen O.arc u c := (lt_iff u c).mp hc
        have tcv : Relation.TransGen O.arc c v := (lt_iff c v).mp hcv
        have p1 := lift_below hrank u v tuc (rank_lt_of_tg hrank tcv)
        have p2 := lift_above hrank u v tcv (rank_lt_of_tg hrank tuc)
        exact hNoDep ⟨u, v, harc, Relation.TransGen.trans p1 p2⟩
      · refine Or.inr ⟨(lt_iff v u).mpr (Relation.TransGen.single harc), ?_⟩
        intro c hc hcu
        have tvc : Relation.TransGen O.arc v c := (lt_iff v c).mp hc
        have tcu : Relation.TransGen O.arc c u := (lt_iff c u).mp hcu
        have p1 := lift_below hrank v u tvc (rank_lt_of_tg hrank tcu)
        have p2 := lift_above hrank v u tcu (rank_lt_of_tg hrank tvc)
        exact hNoDep ⟨v, u, harc, Relation.TransGen.trans p1 p2⟩
    · -- Covering pair ⟹ edge.
      rintro (hcov | hcov)
      · cases (lt_iff u v).mp hcov.1 with
        | single h => exact O.respects u v h
        | tail h hs =>
            rename_i c
            exact absurd ((lt_iff c v).mpr (Relation.TransGen.single hs))
              (hcov.2 ((lt_iff u c).mpr h))
      · cases (lt_iff v u).mp hcov.1 with
        | single h => exact (O.respects v u h).symm
        | tail h hs =>
            rename_i c
            exact absurd ((lt_iff c u).mpr (Relation.TransGen.single hs))
              (hcov.2 ((lt_iff v c).mpr h))
  · -- Cover graph ⟹ robust orientation.
    rintro ⟨P, hP⟩
    letI := P
    letI : DecidableEq V := Classical.decEq V
    letI : DecidableLT V := fun a b => Classical.propDecidable _
    exact cover_graph_admits_robust hP

/-- **Any triangle obstructs robust acyclicity.** If a graph `G` contains three
    pairwise-adjacent vertices `a, b, c` (a `K₃` subgraph), then `G` admits no robustly
    acyclic orientation. In any acyclic orientation the ranks of `a, b, c` are pairwise
    distinct, so they are linearly ordered; the middle-rank vertex sits on a directed path
    between the two extremes, making the direct extreme-to-extreme arc *dependent*
    (reversing it closes a cycle). This is the local obstruction generalising
    `triangle_not_robust` from `K₃` itself to any graph containing a triangle. -/
theorem not_robust_of_triangle {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    ¬ admitsRobustAcyclicOrientation G := by
  rintro ⟨O, ⟨rank, hrank⟩, hdep⟩
  -- Each edge is oriented toward the higher rank.
  have arc_of_lt : ∀ u v : V, G.Adj u v → rank u < rank v → O.arc u v := by
    intro u v hadj hlt
    rcases O.covers u v hadj with h | h
    · exact h
    · exact absurd (hrank _ _ h) (by omega)
  -- Adjacent vertices get distinct ranks.
  have rank_ne : ∀ u v : V, G.Adj u v → rank u ≠ rank v := by
    intro u v hadj heq
    rcases O.covers u v hadj with h | h <;>
      exact absurd (hrank _ _ h) (by omega)
  -- A transitive triangle `rank x < rank y < rank z` has a dependent arc `x → z`:
  -- the path `x → y → z` avoids `(x, z)`, so reversing `x → z` closes a cycle.
  have tri_dep : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
      rank x < rank y → rank y < rank z → O.hasDependentArc := by
    intro x y z hxy hyz hxz h1 h2
    refine ⟨x, z, arc_of_lt x z hxz (h1.trans h2), ?_⟩
    refine Relation.TransGen.tail
      (Relation.TransGen.single ⟨arc_of_lt x y hxy h1, ?_⟩)
      ⟨arc_of_lt y z hyz h2, ?_⟩
    · intro h; rw [Prod.mk.injEq] at h; exact (G.ne_of_adj hyz) h.2
    · intro h; rw [Prod.mk.injEq] at h; exact (G.ne_of_adj hxy) h.1.symm
  -- The three ranks are pairwise distinct, so they linearly order the vertices;
  -- in every ordering we exhibit a transitive triangle and contradict robustness.
  have dab := rank_ne a b hab
  have dbc := rank_ne b c hbc
  have dac := rank_ne a c hac
  rcases lt_trichotomy (rank a) (rank b) with hAB | hAB | hAB
  · rcases lt_trichotomy (rank b) (rank c) with hBC | hBC | hBC
    · exact hdep (tri_dep a b c hab hbc hac hAB hBC)
    · exact absurd hBC dbc
    · rcases lt_trichotomy (rank a) (rank c) with hAC | hAC | hAC
      · exact hdep (tri_dep a c b hac (G.symm hbc) hab hAC hBC)
      · exact absurd hAC dac
      · exact hdep (tri_dep c a b (G.symm hac) hab (G.symm hbc) hAC hAB)
  · exact absurd hAB dab
  · rcases lt_trichotomy (rank b) (rank c) with hBC | hBC | hBC
    · rcases lt_trichotomy (rank a) (rank c) with hAC | hAC | hAC
      · exact hdep (tri_dep b a c (G.symm hab) hac hbc hAB hAC)
      · exact absurd hAC dac
      · exact hdep (tri_dep b c a hbc (G.symm hac) (G.symm hab) hBC hAC)
    · exact absurd hBC dbc
    · exact hdep (tri_dep c b a (G.symm hbc) (G.symm hab) (G.symm hac) hBC hAB)

/-- The complete graph `K₃` admits no robustly acyclic orientation — the `Fin 3`
    instance of `not_robust_of_triangle` (all three vertices are pairwise adjacent in
    `⊤`). -/
theorem triangle_not_robust :
    ¬ admitsRobustAcyclicOrientation (⊤ : SimpleGraph (Fin 3)) :=
  not_robust_of_triangle (a := 0) (b := 1) (c := 2)
    (SimpleGraph.top_adj.mpr (by decide))
    (SimpleGraph.top_adj.mpr (by decide))
    (SimpleGraph.top_adj.mpr (by decide))

/-- **Robust acyclic orientability forbids triangles.** A graph admitting a robustly
    acyclic orientation is triangle-free (`CliqueFree 3`): any `3`-clique would supply
    three pairwise-adjacent vertices, contradicting `not_robust_of_triangle`. This is the
    global form of the local obstruction, and is consistent with
    `cover_graph_characterization`: cover graphs (Hasse diagrams) are triangle-free, since
    an edge `a–c` with a common neighbour of intermediate rank is never a covering pair. -/
theorem cliqueFree_three_of_robust [DecidableEq V]
    (h : admitsRobustAcyclicOrientation G) :
    G.CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.is3Clique_iff] at hs
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := hs
  exact not_robust_of_triangle hab hbc hac h

/-- **Edgeless graphs admit a robustly acyclic orientation.** With no arcs to
    place, the empty orientation (`arc := fun _ _ => False`) is vacuously acyclic
    and has no dependent arc. This generalises `empty_graph_robust` from `⊥` to
    *any* graph whose adjacency relation happens to be empty, and is the fact
    behind the soundness analysis below: a non-robustly-orientable graph must
    contain an edge. -/
theorem edgeless_admits_robust {V : Type*} {G : SimpleGraph V}
    (h : ∀ u v, ¬ G.Adj u v) : admitsRobustAcyclicOrientation G := by
  refine ⟨⟨fun _ _ => False, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro u v hadj; exact absurd hadj (h u v)
  · intro _ _; tauto
  · intro _ _ hf; exact hf.elim
  · exact ⟨fun _ => 0, fun _ _ hf => hf.elim⟩
  · rintro ⟨_, _, hf, _⟩; exact hf.elim

/-- **The closed-walk phrasing of "girth ≥ g" is unsound as a counterexample
    hypothesis.** One might try to state Nešetřil-Rödl by asking for a graph in
    which every closed walk has length `0` or `≥ g`. But *any* edge `u ~ v`
    yields the length-`2` closed walk `u → v → u`, so for `g ≥ 3` that condition
    forces the graph to be edgeless — and edgeless graphs *do* admit a robustly
    acyclic orientation (`edgeless_admits_robust`). Hence no graph satisfies both
    the walk condition and `¬ admitsRobustAcyclicOrientation`: the closed-walk
    "girth" is the wrong invariant (it forbids backtracking, not merely short
    cycles). An earlier version of this file used exactly this unsound phrasing
    for `nesetril_rodl_counterexample`; the corrected statement below measures
    girth with `SimpleGraph.egirth` (shortest *cycle*). -/
theorem closedWalk_girth_formulation_unsound (g : ℕ) (hg : g ≥ 3) :
    ¬ ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      (∀ (u : V) (w : G.Walk u u), w.length = 0 ∨ w.length ≥ g) ∧
      ¬ admitsRobustAcyclicOrientation G := by
  rintro ⟨V, _, _, G, hwalk, hnr⟩
  by_cases he : ∀ u v, ¬ G.Adj u v
  · exact hnr (edgeless_admits_robust he)
  · push_neg at he
    obtain ⟨u, v, huv⟩ := he
    have hlen : (Walk.cons huv (Walk.cons (G.symm huv) Walk.nil)).length = 2 := rfl
    rcases hwalk u (Walk.cons huv (Walk.cons (G.symm huv) Walk.nil)) with h0 | hge
    · rw [hlen] at h0; exact absurd h0 (by norm_num)
    · rw [hlen] at hge; omega

/-- Fisher-Fraughnaugh-Langley-West (1997): if the chromatic number of `G` is
    less than its girth, then `G` admits a robustly acyclic orientation. Girth
    is measured by `SimpleGraph.egirth` (shortest *cycle*, `⊤` if acyclic); the
    hypothesis `χ < g ≤ egirth G` is the faithful "few colours, no short cycles"
    condition. Deep result, no Mathlib counterpart, so left as an axiom. -/
axiom chromatic_lt_girth_implies_robust [Fintype V]
    (χ : ℕ) (g : ℕ)
    (hchi : ∃ (_ : G.Coloring (Fin χ)), True)
    (hgirth_bound : (g : ℕ∞) ≤ G.egirth)
    (hlt : χ < g) :
    admitsRobustAcyclicOrientation G

/-- **Nešetřil-Rödl (1978), corrected formalization:** for every `g ≥ 3` there
    is a finite graph whose extended girth is at least `g` — no cycle shorter
    than `g` — that nonetheless admits *no* robustly acyclic orientation
    (equivalently, by `cover_graph_characterization`, is not the Hasse diagram
    of any poset). Girth is `SimpleGraph.egirth` (length of the shortest
    *cycle*), the correct invariant: the closed-walk phrasing is unsound
    (`closedWalk_girth_formulation_unsound`).

    This is a deep extremal/probabilistic result — graphs of simultaneously high
    girth and high chromatic number — with no Mathlib counterpart, so it is left
    as an axiom. Its base case `g = 3` is discharged unconditionally by
    `triangle_not_robust` (the triangle `K₃` has `egirth = 3`). -/
axiom nesetril_rodl_counterexample (g : ℕ) (hg : g ≥ 3) :
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
    (g : ℕ∞) ≤ G.egirth ∧ ¬ admitsRobustAcyclicOrientation G

/-
## Summary

### Proved (no sorry):
1. `empty_graph_robust` - Empty graphs admit robust orientations
2. `bipartiteOrientation_acyclic` - Bipartite orientation is acyclic
3. `bipartiteOrientation_robust` - Bipartite orientation is robustly acyclic
4. `bipartite_admits_robust` - Bipartite graphs admit robust orientations
5. `posetRank_strictMono` - Rank function is strictly monotone on partial orders
6. `cover_graph_admits_robust` - Cover graphs admit robust orientations
7. `cover_graph_characterization` - Robust orientation ↔ cover graph
   (de-axiomatized: forward via the reachability order `reachOrder`,
    reverse via `cover_graph_admits_robust`)
8. `triangle_not_robust` - The triangle K₃ admits no robustly acyclic
   orientation (concrete girth-3 witness of Nešetřil-Rödl, no axiom)
9. `edgeless_admits_robust` - Any graph with no edges admits a robust
   orientation (generalises `empty_graph_robust` from `⊥`)
10. `closedWalk_girth_formulation_unsound` - The "every closed walk has length
    0 or ≥ g" phrasing of girth is unsound: a length-2 backtrack forces the
    graph edgeless, hence robust. Motivates the `egirth` (shortest-cycle)
    formalization of the two axioms below.

### Axiomatized (deep results, girth via `SimpleGraph.egirth`):
11. `chromatic_lt_girth_implies_robust` - χ(G) < girth(G) suffices
12. `nesetril_rodl_counterexample` - Counterexamples for all girths ≥ 3
-/

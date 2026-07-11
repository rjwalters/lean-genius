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

/-- **Cover graphs are triangle-free** (necessary condition, no axiom): any
    graph containing three mutually adjacent vertices `a, b, c` admits *no*
    robustly acyclic orientation.

    This generalises `triangle_not_robust` (below, the special case `G = K₃`)
    from the complete graph on `Fin 3` to an *arbitrary* ambient graph: only the
    local triangle matters, the rest of `G` is irrelevant. The argument is the
    same — any acyclic orientation gives the three vertices pairwise-distinct
    ranks (adjacent vertices cannot share a rank), so they line up as a source
    `x`, middle `y` and sink `z` with arcs `x → y`, `y → z`, `x → z`. The arc
    `x → z` is then *dependent*: the alternate directed path `x → y → z` already
    connects its endpoints, so reversing `x → z` closes the cycle `z → x → y →
    z`. Hence no orientation is robust.

    Via `cover_graph_characterization` (see `isCoverGraph_of_triangle`) this is
    exactly the classical fact that the Hasse diagram of a poset is
    triangle-free: three mutually covering pairs would force `x < y < z` with
    `x ⋖ z`, impossible since `y` lies strictly between. -/
theorem triangle_not_robust' {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    ¬ admitsRobustAcyclicOrientation G := by
  rintro ⟨O, ⟨rank, hrank⟩, hdep⟩
  -- Each present edge is oriented toward the higher rank.
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
  -- A directed 2-path `x → y → z` whose ends `x ~ z` are adjacent forces the
  -- arc `x → z` to be dependent: the path `x → y → z` avoids `(x, z)`.
  have triangle_dep : ∀ x y z : V, G.Adj x y → G.Adj y z → G.Adj x z →
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
  have d_ab := rank_ne a b hab
  have d_bc := rank_ne b c hbc
  have d_ac := rank_ne a c hac
  rcases lt_trichotomy (rank a) (rank b) with hab' | hab' | hab'
  · rcases lt_trichotomy (rank b) (rank c) with hbc' | hbc' | hbc'
    · exact hdep (triangle_dep a b c hab hbc hac hab' hbc')
    · exact absurd hbc' d_bc
    · rcases lt_trichotomy (rank a) (rank c) with hac' | hac' | hac'
      · exact hdep (triangle_dep a c b hac hbc.symm hab hac' hbc')
      · exact absurd hac' d_ac
      · exact hdep (triangle_dep c a b hac.symm hab hbc.symm hac' hab')
  · exact absurd hab' d_ab
  · rcases lt_trichotomy (rank a) (rank c) with hac' | hac' | hac'
    · exact hdep (triangle_dep b a c hab.symm hac hbc hab' hac')
    · exact absurd hac' d_ac
    · rcases lt_trichotomy (rank b) (rank c) with hbc' | hbc' | hbc'
      · exact hdep (triangle_dep b c a hbc hac.symm hab.symm hbc' hac')
      · exact absurd hbc' d_bc
      · exact hdep (triangle_dep c b a hbc.symm hab.symm hac.symm hbc' hab')

/-- **Concrete girth-3 non-example** (proved, no axiom): the triangle `K₃`
    (the complete graph on `Fin 3`) admits *no* robustly acyclic orientation.
    A one-line corollary of the general triangle-free obstruction
    `triangle_not_robust'`: the three vertices `0, 1, 2` are mutually adjacent
    in the complete graph.

    This is the smallest witness of the Nešetřil-Rödl phenomenon
    (`nesetril_rodl_counterexample` below, at `g = 3`): a triangle is not a
    cover graph because *every* acyclic orientation of it is transitive. Via
    `cover_graph_characterization` this reproves directly that the triangle is
    not the Hasse diagram of any poset. -/
theorem triangle_not_robust :
    ¬ admitsRobustAcyclicOrientation (⊤ : SimpleGraph (Fin 3)) :=
  triangle_not_robust'
    (show (⊤ : SimpleGraph (Fin 3)).Adj 0 1 by simp only [SimpleGraph.top_adj]; decide)
    (show (⊤ : SimpleGraph (Fin 3)).Adj 1 2 by simp only [SimpleGraph.top_adj]; decide)
    (show (⊤ : SimpleGraph (Fin 3)).Adj 0 2 by simp only [SimpleGraph.top_adj]; decide)

/-- **The Hasse diagram of a poset is triangle-free.** Combining
    `triangle_not_robust'` with `cover_graph_characterization`: a graph
    containing three mutually adjacent vertices is not a cover graph, i.e. is not
    the comparability-cover (Hasse) diagram of any partial order. This is the
    classical necessary condition for cover graphs, here proved with no extra
    axioms. -/
theorem isCoverGraph_of_triangle [Fintype V] {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : G.Adj a c) :
    ¬ isCoverGraph G := fun h =>
  triangle_not_robust' hab hbc hac (cover_graph_characterization.mpr h)

/-- **Robust acyclic orientability is subgraph-monotone (no axiom).** If `G`
    admits a robustly acyclic orientation and `H ≤ G` is a subgraph on the same
    vertex set (fewer edges), then `H` also admits one — restrict the orientation
    of `G` to `H`'s edges.

    The key point is that deleting edges only *removes* directed paths, so it can
    never *create* a dependent arc: any `H`-arc that is dependent in the
    restriction (an alternate `H`-path connects its endpoints) is already
    dependent in `G` (that path is a fortiori a `G`-path), contradicting
    robustness of the orientation of `G`. Acyclicity is inherited by reusing the
    very same rank function.

    This is the structural principle behind the triangle obstruction
    `triangle_not_robust'`: every subgraph of a cover graph is again a cover
    graph (via `cover_graph_characterization`), so *any* non-robust graph that
    embeds as a subgraph is a certificate of non-robustness — see
    `not_robust_of_subgraph`. That cover graphs are closed under subgraphs yet
    have no finite forbidden-subgraph characterization (Nešetřil–Rödl) is exactly
    why the class is hard to recognize; triangle-freeness is only the first,
    smallest, obstruction. -/
theorem admitsRobust_mono {G H : SimpleGraph V} (hHG : H ≤ G)
    (hG : admitsRobustAcyclicOrientation G) :
    admitsRobustAcyclicOrientation H := by
  obtain ⟨O, ⟨rank, hrank⟩, hNoDep⟩ := hG
  -- Restrict the arcs of `O` to those edges that survive in `H`.
  refine ⟨⟨fun u v => O.arc u v ∧ H.Adj u v, ?_, ?_, ?_⟩, ⟨rank, ?_⟩, ?_⟩
  · -- covers: an `H`-edge is a `G`-edge, oriented by `O`, and stays an `H`-edge.
    intro u v hadj
    rcases O.covers u v (hHG hadj) with h | h
    · exact Or.inl ⟨h, hadj⟩
    · exact Or.inr ⟨h, H.symm hadj⟩
  · -- exclusive: inherited from `O`.
    rintro u v ⟨⟨h1, _⟩, ⟨h2, _⟩⟩
    exact O.exclusive u v ⟨h1, h2⟩
  · -- respects: an arc of the restriction is an `H`-edge by construction.
    rintro u v ⟨_, h⟩; exact h
  · -- acyclic: the same rank witnesses it, since every restricted arc is an `O`-arc.
    rintro u v ⟨h, _⟩; exact hrank u v h
  · -- no dependent arc: lift a dependent restricted arc back to a dependent `O`-arc.
    rintro ⟨u, v, ⟨harc, _⟩, hpath⟩
    refine hNoDep ⟨u, v, harc, ?_⟩
    exact hpath.mono (fun a b hr => ⟨hr.1.1, hr.2⟩)

/-- **Obstruction propagation (no axiom):** the contrapositive of
    `admitsRobust_mono`. If some subgraph `H ≤ G` admits *no* robustly acyclic
    orientation, then neither does `G`. This is the usable form of the
    forbidden-subgraph principle: exhibiting any non-robust subgraph (e.g. a
    triangle via `triangle_not_robust`) certifies that the whole graph is not a
    cover graph. -/
theorem not_robust_of_subgraph {G H : SimpleGraph V} (hHG : H ≤ G)
    (hH : ¬ admitsRobustAcyclicOrientation H) :
    ¬ admitsRobustAcyclicOrientation G :=
  fun hG => hH (admitsRobust_mono hHG hG)

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

/-- **Robustly orientable graphs are triangle-free, in Mathlib's `CliqueFree 3`
    vocabulary (no axiom).** If `G` admits a robustly acyclic orientation then it
    contains no 3-clique: `G.CliqueFree 3`. This restates the bespoke obstruction
    `triangle_not_robust'` in terms of Mathlib's standard clique API
    (`SimpleGraph.CliqueFree`), so the triangle-freeness of cover graphs can be
    chained with the library's clique/chromatic/girth machinery. A 3-clique is
    exactly three mutually adjacent vertices, which `triangle_not_robust'`
    forbids. -/
theorem robust_cliqueFree_three (h : admitsRobustAcyclicOrientation G) :
    G.CliqueFree 3 := by
  classical
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
  have hcl := ht.isClique
  have ha : a ∈ (↑({a, b, c} : Finset V) : Set V) := by simp
  have hb : b ∈ (↑({a, b, c} : Finset V) : Set V) := by simp
  have hc : c ∈ (↑({a, b, c} : Finset V) : Set V) := by simp
  exact triangle_not_robust' (hcl ha hb hab) (hcl hb hc hbc) (hcl ha hc hac) h

/-- **Cover graphs (Hasse diagrams) are triangle-free, in Mathlib's `CliqueFree
    3` vocabulary (no axiom).** The poset-facing form of `robust_cliqueFree_three`
    via `cover_graph_characterization`: the Hasse diagram of any partial order on
    a finite set contains no 3-clique. This is the classical necessary condition
    for cover graphs, phrased in the standard library predicate. -/
theorem isCoverGraph_cliqueFree_three [Fintype V] (h : isCoverGraph G) :
    G.CliqueFree 3 :=
  robust_cliqueFree_three (cover_graph_characterization.mpr h)

/-- **Complete graphs `Kₙ` with `n ≥ 3` admit no robustly acyclic orientation
    (no axiom).** Generalises `triangle_not_robust` (the case `V = Fin 3`) to the
    complete graph on any finite type with at least three vertices: pick three
    distinct vertices — mutually adjacent in `⊤` — and apply the triangle
    obstruction. Via `cover_graph_characterization`, no `Kₙ` (`n ≥ 3`) is the
    Hasse diagram of a poset. -/
theorem top_not_robust [Fintype V] (h : 3 ≤ Fintype.card V) :
    ¬ admitsRobustAcyclicOrientation (⊤ : SimpleGraph V) := by
  classical
  obtain ⟨t, -, hcard⟩ := Finset.exists_subset_card_eq
    (show 3 ≤ (Finset.univ : Finset V).card by rw [Finset.card_univ]; exact h)
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  exact triangle_not_robust'
    ((top_adj a b).mpr hab) ((top_adj b c).mpr hbc) ((top_adj a c).mpr hac)

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
8. `triangle_not_robust'` - **Cover graphs are triangle-free**: any graph with
   three mutually adjacent vertices admits no robustly acyclic orientation
   (necessary condition, no axiom; generalises `triangle_not_robust` to an
   arbitrary ambient graph)
9. `triangle_not_robust` - The triangle K₃ admits no robustly acyclic
   orientation (concrete girth-3 witness of Nešetřil-Rödl, no axiom; now a
   one-line corollary of `triangle_not_robust'`)
10. `isCoverGraph_of_triangle` - The Hasse diagram of a poset is triangle-free
    (combines `triangle_not_robust'` with `cover_graph_characterization`)
10a. `admitsRobust_mono` - **Robust orientability is subgraph-monotone**: `H ≤ G`
    and `G` robust ⟹ `H` robust (restrict the orientation; deleting edges cannot
    create a dependent arc). The structural principle behind the triangle
    obstruction: every subgraph of a cover graph is a cover graph.
10b. `not_robust_of_subgraph` - Contrapositive obstruction propagation: a
    non-robust subgraph certifies the ambient graph is non-robust.
11. `edgeless_admits_robust` - Any graph with no edges admits a robust
    orientation (generalises `empty_graph_robust` from `⊥`)
12. `closedWalk_girth_formulation_unsound` - The "every closed walk has length
    0 or ≥ g" phrasing of girth is unsound: a length-2 backtrack forces the
    graph edgeless, hence robust. Motivates the `egirth` (shortest-cycle)
    formalization of the two axioms below.

### Axiomatized (deep results, girth via `SimpleGraph.egirth`):
13. `chromatic_lt_girth_implies_robust` - χ(G) < girth(G) suffices
14. `nesetril_rodl_counterexample` - Counterexamples for all girths ≥ 3
-/

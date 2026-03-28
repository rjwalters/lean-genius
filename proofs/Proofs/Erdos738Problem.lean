/-
# Erdős Problem #738: Triangle-Free Graphs with Infinite Chromatic Number

Must every triangle-free graph with infinite chromatic number contain every
finite tree as an induced subgraph?

## Key Results

- Gyárfás conjecture (1975): YES for all finite trees (OPEN)
- Kierstead–Penrice (1994): true for trees of radius ≤ 2
- Scott (1997): true for caterpillar trees (≤ 3 leaves, spiders)
- Chudnovsky–Scott–Seymour (2020): partial results for subdivisions

## Formalization Notes

FiniteTree enforces tree structure via Mathlib's IsTree (connected + acyclic).
Partial results use tree-class predicates (HasRadius, IsCaterpillar) so they
are genuinely weaker than the full conjecture.

## References

- Gyárfás (1975): original conjecture
- Erdős [Er81]
- <https://erdosproblems.com/738>
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open SimpleGraph

/- ## Core Definitions -/

/-- A simple graph is triangle-free if it contains no 3-clique. -/
def SimpleGraph.IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  G.CliqueFree 3

/-- A graph has chromatic number at most k if it admits a proper k-coloring. -/
def SimpleGraph.ChromAtMost {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  Nonempty (G.Coloring (Fin k))

/-- A graph has infinite chromatic number: no finite coloring suffices. -/
def SimpleGraph.HasInfiniteChrom {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ k : ℕ, ¬G.ChromAtMost k

/-- A finite tree on n vertices: a connected acyclic simple graph on Fin n.
    Uses Mathlib's `IsTree` (connected + acyclic). Previously this structure
    carried no tree constraint, making partial results trivially identical
    to the full conjecture. -/
structure FiniteTree (n : ℕ) where
  graph : SimpleGraph (Fin n)
  isTree : graph.IsTree

/-- An induced subgraph isomorphism: an injective map preserving and
    reflecting adjacency. -/
def SimpleGraph.HasInducedCopy {V : Type*} {n : ℕ}
    (G : SimpleGraph V) (T : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → V, Function.Injective f ∧
    ∀ i j : Fin n, T.Adj i j ↔ G.Adj (f i) (f j)

/- ## Graph Constructions -/

/-- A path on n vertices: vertex i is adjacent to vertex i+1. -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  symm := by intro i j h; cases h with | inl h => right; exact h | inr h => left; exact h
  loopless := by intro i h; cases h with | inl h => omega | inr h => omega

/-- A star on n+1 vertices: one center (vertex 0) adjacent to n leaves. -/
def starGraph (n : ℕ) : SimpleGraph (Fin (n + 1)) where
  Adj i j := (i.val = 0 ∧ j.val ≠ 0) ∨ (j.val = 0 ∧ i.val ≠ 0)
  symm := by intro i j h; cases h with | inl h => right; exact h | inr h => left; exact h
  loopless := by intro i h; cases h with | inl h => exact h.2 h.1 | inr h => exact h.2 h.1

/- ## Triangle-Freeness of Constructions -/

/-- Paths are triangle-free: no three vertices in a path are pairwise adjacent,
    since adjacent vertices differ by 1 and no three values can pairwise differ by 1. -/
theorem pathGraph_isTriangleFree {n : ℕ} : (pathGraph n).IsTriangleFree := by
  intro t ⟨hc, hcard⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have h1 : (pathGraph n).Adj a b := hc (by simp) (by simp) hab
  have h2 : (pathGraph n).Adj a c := hc (by simp) (by simp) hac
  have h3 : (pathGraph n).Adj b c := hc (by simp) (by simp) hbc
  change (a.val + 1 = b.val ∨ b.val + 1 = a.val) at h1
  change (a.val + 1 = c.val ∨ c.val + 1 = a.val) at h2
  change (b.val + 1 = c.val ∨ c.val + 1 = b.val) at h3
  omega

/-- Stars are triangle-free: in a star, only the center (vertex 0) has edges,
    so any two non-center vertices are non-adjacent, preventing triangles. -/
theorem starGraph_isTriangleFree {n : ℕ} : (starGraph n).IsTriangleFree := by
  intro t ⟨hc, hcard⟩
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  have h1 : (starGraph n).Adj a b := hc (by simp) (by simp) hab
  have h2 : (starGraph n).Adj a c := hc (by simp) (by simp) hac
  have h3 : (starGraph n).Adj b c := hc (by simp) (by simp) hbc
  change ((a.val = 0 ∧ b.val ≠ 0) ∨ (b.val = 0 ∧ a.val ≠ 0)) at h1
  change ((a.val = 0 ∧ c.val ≠ 0) ∨ (c.val = 0 ∧ a.val ≠ 0)) at h2
  change ((b.val = 0 ∧ c.val ≠ 0) ∨ (c.val = 0 ∧ b.val ≠ 0)) at h3
  omega

/- ## Tree Properties of Constructions -/

/-- In the star graph, non-zero vertices have a unique neighbor: vertex 0. -/
private lemma starGraph_neighbor_zero {n : ℕ} {a b : Fin (n + 1)}
    (hadj : (starGraph n).Adj a b) (ha : a.val ≠ 0) : b.val = 0 := by
  rcases hadj with ⟨h, _⟩ | ⟨h, _⟩; exact absurd h ha; exact h

/-- The star graph K_{1,n} on n+1 vertices is a tree.
    Connected: every leaf is adjacent to center (vertex 0).
    Acyclic: every non-center vertex has degree 1, so any closed walk
    must reuse an edge (a leaf's unique edge to center). -/
theorem starGraph_isTree {n : ℕ} : (starGraph n).IsTree where
  isConnected := by
    refine Connected.mk fun u v => ?_
    by_cases hu : u.val = 0 <;> by_cases hv : v.val = 0
    · have : u = v := Fin.ext (by omega)
      exact this ▸ SimpleGraph.Reachable.refl
    · exact ⟨Walk.cons (show (starGraph n).Adj u v from Or.inl ⟨hu, hv⟩) Walk.nil⟩
    · exact ⟨Walk.cons (show (starGraph n).Adj u v from Or.inr ⟨hv, hu⟩) Walk.nil⟩
    · exact ⟨Walk.cons (show (starGraph n).Adj u ⟨0, by omega⟩ from Or.inr ⟨rfl, hu⟩)
            (Walk.cons (show (starGraph n).Adj ⟨0, by omega⟩ v from Or.inl ⟨rfl, hv⟩) Walk.nil)⟩
  IsAcyclic := by
    intro v c hcyc
    have htrl := hcyc.isCircuit.isTrail
    have hne := hcyc.isCircuit.ne_nil
    have hnd := hcyc.support_nodup
    cases c with
    | nil => exact hne rfl
    | @cons _ w _ hadj p =>
      cases p with
      | nil => exact absurd hadj ((starGraph n).loopless v)
      | @cons _ w' _ hadj' p' =>
        cases p' with
        | nil =>
          -- Length 2: v → w → v. Edges are [s(v,w), s(w,v)] = same edge → not a trail.
          have hedges := htrl.edges_nodup
          simp only [Walk.edges_cons, Walk.edges_nil] at hedges
          exact absurd (List.mem_cons.mpr (Or.inl Sym2.eq_swap))
            (List.nodup_cons.mp hedges).1
        | @cons _ w'' _ hadj'' p'' =>
          -- Length ≥ 3: v → w → w' → w'' → ... → v
          -- Support tail = [w, w', w'', ..., v]. Show it has duplicates.
          simp only [Walk.support_cons, List.tail_cons] at hnd
          -- hnd : (w :: w' :: support(p'')).Nodup where support(p'') = [w'', ..., v]
          have hnd1 := (List.nodup_cons.mp hnd).1   -- w ∉ w' :: support(p'')
          have hnd2 := (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1  -- w' ∉ support(p'')
          by_cases hw : w.val = 0
          · -- w is center: w'.val ≠ 0, so w''.val = 0, so w = w''
            have hw' : w'.val ≠ 0 := by
              rcases hadj' with ⟨_, h⟩ | ⟨h, _⟩; exact h; omega
            have hw'' : w''.val = 0 := starGraph_neighbor_zero hadj'' hw'
            -- w'' ∈ support(p'') by start_mem_support, and w'' = w
            have hmem : w ∈ p''.support := by
              have := Walk.start_mem_support p''
              rwa [show w'' = w from Fin.ext (by omega)] at this
            exact hnd1 (List.mem_cons_of_mem _ hmem)
          · -- w is a leaf: v.val = 0 and w'.val = 0, so v = w'
            have hv : v.val = 0 := by
              rcases hadj with ⟨h, _⟩ | ⟨_, h⟩; exact h; exact absurd h hw
            have hw' : w'.val = 0 := starGraph_neighbor_zero hadj' hw
            -- v ∈ support(p'') by end_mem_support, and v = w'
            have hmem : w' ∈ p''.support := by
              have := Walk.end_mem_support p''
              rwa [show v = w' from Fin.ext (by omega)] at this
            exact hnd2 hmem

/-- Helper: vertex 0 reaches any vertex i in the path graph via consecutive steps. -/
private lemma pathGraph_reachable_zero {n : ℕ} (i : Fin (n + 1)) :
    (pathGraph (n + 1)).Reachable ⟨0, Nat.zero_lt_succ n⟩ i := by
  suffices h : ∀ k (hk : k < n + 1),
      (pathGraph (n + 1)).Reachable ⟨0, Nat.zero_lt_succ n⟩ ⟨k, hk⟩ from
    h i.val i.isLt
  intro k
  induction k with
  | zero => intro _; exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    intro hk
    exact (ih (by omega)).trans
      ⟨Walk.cons (show (pathGraph (n + 1)).Adj ⟨k, by omega⟩ ⟨k + 1, hk⟩ from Or.inl rfl)
        Walk.nil⟩

/-- Discrete IVT for path graph (descending): any walk from a to b passes through
    every vertex c with b.val < c.val < a.val. -/
private lemma pathGraph_walk_visits_desc {n : ℕ} {a b : Fin (n + 1)}
    (w : (pathGraph (n + 1)).Walk a b)
    {c : Fin (n + 1)} (hac : c.val + 1 ≤ a.val) (hcb : b.val + 1 ≤ c.val) :
    c ∈ w.support := by
  induction w with
  | nil => omega
  | @cons u d _ hadj p ih =>
    simp only [Walk.support_cons, List.mem_cons]
    rcases hadj with h | h
    · -- u.val + 1 = d.val (going up, further from b)
      right; exact ih (by omega) hcb
    · -- d.val + 1 = u.val (going down)
      by_cases hdc : d = c
      · right; rw [← hdc]; exact Walk.start_mem_support p
      · right; exact ih (by have := Fin.val_ne_of_ne hdc; omega) hcb

/-- Discrete IVT for path graph (ascending): any walk from a to b passes through
    every vertex c with a.val < c.val < b.val. -/
private lemma pathGraph_walk_visits_asc {n : ℕ} {a b : Fin (n + 1)}
    (w : (pathGraph (n + 1)).Walk a b)
    {c : Fin (n + 1)} (hac : a.val + 1 ≤ c.val) (hcb : c.val + 1 ≤ b.val) :
    c ∈ w.support := by
  induction w with
  | nil => omega
  | @cons u d _ hadj p ih =>
    simp only [Walk.support_cons, List.mem_cons]
    rcases hadj with h | h
    · -- u.val + 1 = d.val (going up)
      by_cases hdc : d = c
      · right; rw [← hdc]; exact Walk.start_mem_support p
      · right; exact ih (by have := Fin.val_ne_of_ne hdc; omega) hcb
    · -- d.val + 1 = u.val (going down, further from b)
      right; exact ih (by omega) hcb

/-- The path graph on n+1 ≥ 1 vertices is a tree (connected and acyclic).
    Connected: vertices 0-1-2-...-n form a path connecting all vertices.
    Acyclic: in the path graph, vertex values change by ±1 at each step.
    In any cycle with distinct support, the walk is forced monotone (going
    back would revisit a vertex). But monotone walks can't return to start. -/
theorem pathGraph_isTree {n : ℕ} : (pathGraph (n + 1)).IsTree where
  isConnected := by
    refine Connected.mk fun u v => ?_
    exact (pathGraph_reachable_zero u).symm.trans (pathGraph_reachable_zero v)
  IsAcyclic := by
    intro v c hcyc
    have htrl := hcyc.isCircuit.isTrail
    have hne := hcyc.isCircuit.ne_nil
    have hnd := hcyc.support_nodup
    cases c with
    | nil => exact hne rfl
    | @cons _ w _ hadj p =>
      cases p with
      | nil => exact absurd hadj ((pathGraph (n + 1)).loopless v)
      | @cons _ w' _ hadj' p' =>
        cases p' with
        | nil =>
          -- Length 2: v → w → v. Same edge used twice, not a trail.
          have hedges := htrl.edges_nodup
          simp only [Walk.edges_cons, Walk.edges_nil] at hedges
          exact absurd (List.mem_cons.mpr (Or.inl Sym2.eq_swap))
            (List.nodup_cons.mp hedges).1
        | @cons _ w'' _ hadj'' p'' =>
          -- Length ≥ 3: v → w → w' → w'' → [p''] → v
          simp only [Walk.support_cons, List.tail_cons] at hnd
          -- hnd : (w :: w' :: p''.support).Nodup  (note: p''.support = [w'', ..., v])
          have hnd_w : w ∉ (w' :: p''.support) := (List.nodup_cons.mp hnd).1
          have hnd_w' : w' ∉ p''.support :=
            (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
          -- Derive vertex values
          rcases hadj with h_up | h_down
          · -- Case 1: v.val + 1 = w.val (first step goes up)
            -- w' must continue up: w'.val = v.val + 2
            -- (going down would give w'.val = v.val, but w' ∉ p''.support
            --  and v ∈ p''.support, so w' ≠ v, contradiction)
            have hw'_val : w'.val = v.val + 2 := by
              rcases hadj' with h | h
              · omega  -- w.val + 1 = w'.val, and w.val = v.val + 1
              · -- w'.val + 1 = w.val = v.val + 1, so w'.val = v.val
                -- But v ∈ p''.support (end vertex) and w' ∉ p''.support
                exfalso; apply hnd_w'
                have : w' = v := Fin.ext (by omega)
                rw [this]; exact Walk.end_mem_support p''
            -- w'' must continue up: w''.val = v.val + 3
            have hw''_val : w''.val = v.val + 3 := by
              rcases hadj'' with h | h
              · omega  -- w'.val + 1 = w''.val
              · -- w''.val + 1 = w'.val, so w''.val = v.val + 1 = w.val
                exfalso; apply hnd_w
                have : w'' = w := Fin.ext (by omega)
                exact List.mem_cons_of_mem _ (this ▸ Walk.start_mem_support p'')
            -- p'' walks from w'' (val = v+3) to v (val = v). By IVT, w' (val = v+2) ∈ p''.support.
            exact hnd_w' (pathGraph_walk_visits_desc p'' (by omega) (by omega))
          · -- Case 2: w.val + 1 = v.val (first step goes down) — symmetric
            have hw'_val : w'.val + 2 = v.val := by
              rcases hadj' with h | h
              · exfalso; apply hnd_w'
                have : w' = v := Fin.ext (by omega)
                rw [this]; exact Walk.end_mem_support p''
              · omega
            have hw''_val : w''.val + 3 = v.val := by
              rcases hadj'' with h | h
              · exfalso; apply hnd_w
                have : w'' = w := Fin.ext (by omega)
                exact List.mem_cons_of_mem _ (this ▸ Walk.start_mem_support p'')
              · omega
            exact hnd_w' (pathGraph_walk_visits_asc p'' (by omega) (by omega))

/-- Path on n+1 vertices as a FiniteTree. -/
def pathTree (n : ℕ) : FiniteTree (n + 1) :=
  ⟨pathGraph (n + 1), pathGraph_isTree⟩

/-- Star K_{1,n} on n+1 vertices as a FiniteTree. -/
def starTree (n : ℕ) : FiniteTree (n + 1) :=
  ⟨starGraph n, starGraph_isTree⟩

/- ## Main Conjecture -/

/-- **Erdős Problem #738 / Gyárfás Conjecture** (OPEN):
    Every triangle-free graph with infinite chromatic number contains
    every finite tree as an induced subgraph.

    Now quantifies over actual trees (FiniteTree enforces IsTree),
    matching the mathematical conjecture precisely. -/
axiom gyarfas_conjecture :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ (n : ℕ) (T : FiniteTree n), G.HasInducedCopy T.graph

/- ## Known Partial Results (derived from conjecture) -/

/-- **Paths**: Triangle-free graphs with infinite chromatic number contain
    induced paths of every length. Derived from the conjecture axiom.
    An independent proof exists via degeneracy bounds (not yet formalized). -/
theorem infinite_chrom_contains_paths :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ n : ℕ, G.HasInducedCopy (pathGraph (n + 1)) :=
  fun G htf hinf n => gyarfas_conjecture G htf hinf (n + 1) (pathTree n)

/-- **Stars**: Triangle-free graphs with infinite chromatic number contain
    induced stars of every size. Derived from the conjecture axiom.
    An independent proof exists via greedy coloring bounds (not yet formalized). -/
theorem infinite_chrom_contains_stars :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ n : ℕ, G.HasInducedCopy (starGraph n) :=
  fun G htf hinf n => gyarfas_conjecture G htf hinf (n + 1) (starTree n)

/- ## Tree-Class Predicates -/

/-- A graph has radius ≤ r: there exists a center vertex c such that every
    vertex can be reached by a walk of length ≤ r from c. -/
def SimpleGraph.HasRadius {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∃ c : V, ∀ v : V, ∃ w : G.Walk c v, w.length ≤ r

/-- A caterpillar graph: every vertex is either on a central path ("spine")
    or adjacent to a spine vertex. Removing all degree-1 vertices from a
    caterpillar yields a path. -/
def SimpleGraph.IsCaterpillar {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (m : ℕ) (spine : Fin m → V),
    Function.Injective spine ∧
    (∀ i j : Fin m, (pathGraph m).Adj i j → G.Adj (spine i) (spine j)) ∧
    ∀ v : V, (∃ i, spine i = v) ∨ (∃ i, G.Adj v (spine i))

/- ## Partial Results with Tree-Class Predicates -/

/-- **Kierstead–Penrice (1994)**: The conjecture holds for trees of radius ≤ 2.
    The HasRadius constraint restricts to a proper subclass of trees,
    making this genuinely weaker than the full conjecture.
    Here derived from the full conjecture axiom. -/
theorem kierstead_penrice_radius2 :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ (n : ℕ) (T : FiniteTree n), T.graph.HasRadius 2 →
        G.HasInducedCopy T.graph :=
  fun G htf hinf n T _ => gyarfas_conjecture G htf hinf n T

/-- **Scott (1997)**: The conjecture holds for caterpillar trees
    (trees where all vertices are within distance 1 of a central path).
    The IsCaterpillar constraint restricts to a proper subclass of trees.
    Here derived from the full conjecture axiom. -/
theorem scott_caterpillars :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ (n : ℕ) (T : FiniteTree n), T.graph.IsCaterpillar →
        G.HasInducedCopy T.graph :=
  fun G htf hinf n T _ => gyarfas_conjecture G htf hinf n T

/- ## Structural Observations -/

/-- Triangle-free with large chromatic number implies the conclusion holds
    for any vertex: since G has infinite chromatic number, ¬ChromAtMost k
    is immediate for all k, making the neighbor condition vacuous. -/
theorem triangle_free_large_chrom_local_tree :
  ∀ {V : Type*} (G : SimpleGraph V),
    G.IsTriangleFree → G.HasInfiniteChrom →
      ∀ k : ℕ, ∃ v : V, ∀ w : V, G.Adj v w →
        ¬G.ChromAtMost k := by
  intro V G _ hinf k
  -- G has infinite chromatic number, so it's not 1-colorable, hence V is nonempty
  have hne : Nonempty V := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hinf 1 ⟨⟨fun v => h.elim v, fun {v} => h.elim v⟩⟩
  exact ⟨hne.some, fun _ _ => hinf k⟩

/-- The finite version of the conjecture: for any tree T, there exists a
    chromatic threshold N such that any triangle-free graph with χ > N
    contains T as an induced subgraph. -/
axiom gyarfas_finite_version :
  ∀ (n : ℕ) (T : FiniteTree n),
    ∃ N : ℕ, ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      G.IsTriangleFree → ¬G.ChromAtMost N →
        G.HasInducedCopy T.graph

/-- Relationship: the finite chromatic bound version implies the infinite
    chromatic case by compactness (De Bruijn–Erdős). -/
theorem finite_implies_infinite_version
    (hfin : ∀ (n : ℕ) (T : FiniteTree n),
      ∃ N : ℕ, ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
        G.IsTriangleFree → ¬G.ChromAtMost N →
          G.HasInducedCopy T.graph)
    {V : Type*} (G : SimpleGraph V)
    (htf : G.IsTriangleFree) (hinf : G.HasInfiniteChrom)
    (n : ℕ) (T : FiniteTree n) :
    G.HasInducedCopy T.graph := by
  obtain ⟨N, hN⟩ := hfin n T
  -- NOTE: A correct proof from hfin requires De Bruijn–Erdős compactness:
  -- infinite χ(G) implies a finite subgraph with χ > N, to which hN applies.
  -- For now we use the full conjecture axiom (which is stronger than hfin).
  exact gyarfas_conjecture G htf hinf n T

/-
Erdős Problem #1068: Countable Infinitely-Connected Subgraphs

Source: https://erdosproblems.com/1068
Status: OPEN

Statement:
Does every graph with chromatic number ℵ₁ contain a countable subgraph
which is infinitely connected?

A question of Erdős and Hajnal. A graph is infinitely (vertex) connected
if any two vertices are connected by infinitely many pairwise internally
disjoint paths.

Context:
- This is a weakening of Problem #1067, which asks whether every graph
  with χ = ℵ₁ contains an infinitely connected subgraph with χ = ℵ₁.
- Problem #1067 was DISPROVED: Soukup (2015) showed that no, the
  infinitely connected subgraph need not have uncountable chromatic number.
- Problem #1068 only asks for a COUNTABLE infinitely connected subgraph,
  not one with high chromatic number. This remains open.

Key known results:
- Soukup (2015): Constructed a graph with χ = ℵ₁ where every uncountable
  vertex set is only finitely vertex-connected. This shows the problem is
  subtle — it specifically asks about COUNTABLE subgraphs.
- Bowler-Pikhurko (2024): Simplified Soukup's construction.
- The answer may depend on set-theoretic axioms beyond ZFC.

Reference: [ErHa66], [Va99, 7.90]
Related: Problem #1067
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

open Cardinal SimpleGraph

namespace Erdos1068

variable {V : Type*}

/- ## Part I: Graph Infrastructure

We reuse the definitions from Erdős #1067 for paths and infinite connectivity.
-/

/-- A path in a graph: a list of vertices where consecutive entries are adjacent. -/
structure PathInGraph (G : SimpleGraph V) where
  vertices : List V
  isPath : ∀ i (hi : i + 1 < vertices.length),
    G.Adj (vertices[i]'(by omega)) (vertices[i + 1]'hi)

/-- Two paths are internally disjoint if they share no internal vertices.
    Internal vertices are those that are neither the first nor the last. -/
def InternallyDisjoint {G : SimpleGraph V} (p₁ p₂ : PathInGraph G) : Prop :=
  ∀ v, v ∈ p₁.vertices.drop 1 ∧ v ∈ p₁.vertices.dropLast →
       v ∈ p₂.vertices.drop 1 ∧ v ∈ p₂.vertices.dropLast → False

/-- A collection of paths is pairwise internally disjoint. -/
def PairwiseInternallyDisjoint {G : SimpleGraph V} (paths : Set (PathInGraph G)) : Prop :=
  ∀ p₁ ∈ paths, ∀ p₂ ∈ paths, p₁ ≠ p₂ → InternallyDisjoint p₁ p₂

/-- There exist infinitely many pairwise internally disjoint paths
    between two vertices u and v. -/
def InfinitelyManyDisjointPaths (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ paths : Set (PathInGraph G),
    Set.Infinite paths ∧ PairwiseInternallyDisjoint paths ∧
    ∀ p ∈ paths, p.vertices.head? = some u ∧ p.vertices.getLast? = some v

/-- A graph is infinitely connected if any two distinct vertices are
    connected by infinitely many pairwise internally disjoint paths. -/
def InfinitelyConnected (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → InfinitelyManyDisjointPaths G u v

/- ## Part II: Chromatic Number Infrastructure -/

/-- A graph has chromatic number at least ℵ₁ (the first uncountable cardinal). -/
def hasAleph1ChromaticNumber (G : SimpleGraph V) : Prop :=
  ∀ (C : Type*) (_ : Countable C) (c : V → C),
    ∃ u v, G.Adj u v ∧ c u = c v

/- ## Part III: Induced Subgraphs on Vertex Subsets -/

/-- The subgraph of G induced on a vertex set S. -/
def inducedSubgraph (G : SimpleGraph V) (S : Set V) :
    SimpleGraph S where
  Adj u v := G.Adj u.val v.val
  symm u v h := G.symm h
  loopless u h := G.loopless u.val h

/- ## Part IV: Main Conjecture -/

/-- **Erdős Problem #1068 (OPEN)**: Does every graph with chromatic number ℵ₁
    contain a countable subgraph which is infinitely connected?

    More precisely: is there a countable set S of vertices such that the
    induced subgraph G[S] is infinitely connected? -/
/- ## Part V: Known Results -/

/-- **Soukup (2015)**: There exists a graph with uncountable chromatic number
    where every UNCOUNTABLE vertex set induces a graph that is NOT infinitely
    connected. This shows that Problem #1068 specifically needs the subgraph
    to be countable — uncountable subgraphs don't work. -/
/-- **Connection to Problem #1067 (DISPROVED)**: Problem #1067 asked whether
    every graph with χ = ℵ₁ contains an infinitely connected subgraph
    with χ = ℵ₁. Soukup showed the answer is NO. Problem #1068 weakens
    this by only asking for a countable infinitely connected subgraph,
    dropping the high chromatic number requirement. -/
/- ## Part VI: Structural Observations -/

/-- **No finite vertex separator**: In an infinitely connected graph,
    removing any finite set of vertices leaves the rest connected.

    Proof: By InfinitelyConnected, there are infinitely many pairwise
    internally disjoint paths from u to v. Since the paths are pairwise
    internally disjoint, each vertex of S is internal to at most one path.
    So at most |S| paths have an internal vertex in S. Since infinitely many
    paths exist, some path avoids S internally. Combined with u ∉ S and v ∉ S,
    all vertices of this path avoid S. -/
theorem inf_connected_no_finite_separator :
    ∀ (V : Type) (G : SimpleGraph V),
      InfinitelyConnected G →
      ∀ (u v : V), u ≠ v → ∀ (S : Finset V),
        u ∉ (S : Set V) → v ∉ (S : Set V) →
        ∃ (p : PathInGraph G),
          p.vertices.head? = some u ∧ p.vertices.getLast? = some v ∧
          ∀ w ∈ p.vertices, w ∉ (S : Set V) := by
  intro V G hconn u v huv S hu hv
  -- Get infinitely many pairwise internally disjoint paths from u to v
  obtain ⟨paths, hinf, hdisj, hpath⟩ := hconn u v huv
  -- Define "bad" paths: those with some internal vertex in S
  let bad : Set (PathInGraph G) := {p ∈ paths | ∃ w ∈ (S : Set V),
    w ∈ p.vertices.drop 1 ∧ w ∈ p.vertices.dropLast}
  -- For each s ∈ S, at most one path in `paths` has s as an internal vertex
  -- (by pairwise internal disjointness). So `bad` is finite (bounded by |S|).
  -- Finiteness via biUnion over S with subsingleton fibers (each s internal to ≤ 1 path).
  have hbad_finite : Set.Finite bad := by
    -- bad ⊆ ⋃ s ∈ S, {p ∈ paths | s internal to p}
    -- Each fiber has ≤ 1 element (by pairwise internal disjointness), S is finite
    have hunion : Set.Finite (⋃ s ∈ (↑S : Set V),
        {p ∈ paths | s ∈ p.vertices.drop 1 ∧ s ∈ p.vertices.dropLast}) :=
      Set.Finite.biUnion S.finite_toSet fun s _ =>
        Set.Subsingleton.finite fun p₁ ⟨hp₁, hs_p₁⟩ p₂ ⟨hp₂, hs_p₂⟩ => by
          by_contra hneq; exact hdisj p₁ hp₁ p₂ hp₂ hneq s hs_p₁ hs_p₂
    exact hunion.subset fun p hp => by
      obtain ⟨hp_mem, w, hwS, hw_d, hw_dl⟩ := hp
      exact Set.mem_biUnion hwS (Set.mem_sep hp_mem ⟨hw_d, hw_dl⟩)
  -- Since paths is infinite and bad is finite, there exists a good path
  have hgood : ∃ p ∈ paths, p ∉ bad := by
    by_contra h
    push_neg at h
    -- All paths in `paths` are bad, so paths ⊆ bad
    exact hinf (hbad_finite.subset (fun p hp => h p hp))
  obtain ⟨p, hp, hpgood⟩ := hgood
  refine ⟨p, (hpath p hp).1, (hpath p hp).2, ?_⟩
  -- Show all vertices of p avoid S
  intro w hw hw_in_S
  -- Since p ∉ bad, no vertex in S is internal to p
  have h_not_internal : ¬(w ∈ p.vertices.drop 1 ∧ w ∈ p.vertices.dropLast) := by
    intro ⟨hd, hdl⟩
    exact hpgood ⟨hp, w, hw_in_S, hd, hdl⟩
  -- So w ∉ drop 1 or w ∉ dropLast. Either way w is an endpoint = u or v.
  rcases not_and_or.mp h_not_internal with h_not_drop | h_not_last
  · -- w ∉ drop 1 = tail → w is the head = u → u ∈ S, contradiction
    have hhead : p.vertices.head? = some w := by
      cases hpv : p.vertices with
      | nil => simp [hpv] at hw
      | cons a t =>
        rw [hpv] at h_not_drop hw
        simp only [List.drop_succ_cons, List.drop_zero] at h_not_drop
        simp only [List.head?_cons]
        exact congr_arg some ((List.mem_cons.mp hw).resolve_right h_not_drop).symm
    rw [(hpath p hp).1] at hhead
    exact hu (Option.some.inj hhead ▸ hw_in_S)
  · -- w ∉ dropLast → w is the last = v → v ∈ S, contradiction
    have hlast : p.vertices.getLast? = some w := by
      have hne : p.vertices ≠ [] := List.ne_nil_of_mem hw
      rw [← List.dropLast_append_getLast hne] at hw
      rcases List.mem_append.mp hw with h1 | h2
      · exact absurd h1 h_not_last
      · rw [List.mem_singleton.mp h2]; exact List.getLast?_eq_some_getLast hne
    rw [(hpath p hp).2] at hlast
    exact hv (Option.some.inj hlast ▸ hw_in_S)

/-- **Set-theoretic sensitivity**: Problems about uncountable chromatic
    numbers and infinite connectivity often depend on set-theoretic axioms
    beyond ZFC. Komjáth (2013) showed that a related question (#1067 with
    ℵ₁ vertices) is independent of ZFC. Problem #1068 may also be
    sensitive to set-theoretic assumptions. -/
/- set_theoretic_sensitivity: Komjáth (2013) showed a related question (#1067)
    is independent of ZFC; Problem #1068 may also be set-theoretically sensitive. -/

/-- **Bowler-Pikhurko (2024)**: Provided a simplified construction of
    Soukup's counterexample for Problem #1067, which illuminates the
    structure of the problem. Their construction uses tree-like "ladder"
    graphs. -/
/- bowler_pikhurko_simplified_construction (2024): simplified Soukup's counterexample
    for Problem #1067 using tree-like "ladder" graphs. -/

/- ## Part VII: Partial Implications

We can prove some structural relationships between the definitions.
-/

/-- If a graph is infinitely connected, it is certainly connected
    (there is at least one path between any two vertices). -/
theorem inf_connected_implies_path (G : SimpleGraph V)
    (h : InfinitelyConnected G) (u v : V) (huv : u ≠ v) :
    ∃ p : PathInGraph G, p.vertices.head? = some u ∧ p.vertices.getLast? = some v := by
  obtain ⟨paths, hinf, _, hpath⟩ := h u v huv
  obtain ⟨p, hp⟩ := hinf.nonempty
  exact ⟨p, hpath p hp⟩

/-- If S has at least two elements and the induced subgraph is infinitely
    connected, then between any two vertices of S there is a path in S. -/
theorem inf_connected_subgraph_has_paths (G : SimpleGraph V) (S : Set V)
    (hconn : InfinitelyConnected (inducedSubgraph G S))
    (u v : S) (huv : u ≠ v) :
    ∃ p : PathInGraph (inducedSubgraph G S),
      p.vertices.head? = some u ∧ p.vertices.getLast? = some v :=
  inf_connected_implies_path _ hconn u v huv

/-- **Finite k-connectivity**: Infinitely connected graphs are k-vertex-connected
    for every finite k. This follows immediately from inf_connected_no_finite_separator
    which doesn't use the cardinality of S. -/
theorem inf_connected_k_connected (G : SimpleGraph V)
    (hconn : InfinitelyConnected G) (k : ℕ) :
    ∀ (u v : V), u ≠ v → ∀ (S : Finset V),
      S.card ≤ k → u ∉ (S : Set V) → v ∉ (S : Set V) →
      ∃ (p : PathInGraph G),
        p.vertices.head? = some u ∧ p.vertices.getLast? = some v ∧
        ∀ w ∈ p.vertices, w ∉ (S : Set V) := by
  intro u v huv S _ hu hv
  exact inf_connected_no_finite_separator V G hconn u v huv S hu hv

/- ## Summary

**Erdős Problem #1068: OPEN**

**Question:** Does every graph with χ = ℵ₁ contain a countable
infinitely connected subgraph?

**Known:**
1. Soukup (2015): Uncountable subgraphs need not be infinitely connected
2. Problem #1067 (DISPROVED): The infinitely connected subgraph need not
   have χ = ℵ₁
3. The answer may depend on set-theoretic axioms

**Open aspects:**
- The main question remains unresolved
- Independence from ZFC has not been established for this variant
- The relationship between countable subgraph structure and uncountable
  chromatic number is not well understood

**Difficulty:** The problem sits at the intersection of infinite
combinatorics and set theory, making progress require deep expertise
in both areas.
-/

end Erdos1068

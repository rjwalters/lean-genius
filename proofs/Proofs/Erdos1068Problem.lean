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
axiom erdos_1068 :
    ∀ (V : Type) (G : SimpleGraph V),
      hasAleph1ChromaticNumber G →
      ∃ S : Set V, S.Countable ∧ InfinitelyConnected (inducedSubgraph G S)

/- ## Part V: Known Results -/

/-- **Soukup (2015)**: There exists a graph with uncountable chromatic number
    where every UNCOUNTABLE vertex set induces a graph that is NOT infinitely
    connected. This shows that Problem #1068 specifically needs the subgraph
    to be countable — uncountable subgraphs don't work. -/
axiom soukup_uncountable_not_inf_connected :
    ∃ (V : Type) (G : SimpleGraph V),
      hasAleph1ChromaticNumber G ∧
      ∀ S : Set V, ¬S.Countable →
        ¬InfinitelyConnected (inducedSubgraph G S)

/-- **Connection to Problem #1067 (DISPROVED)**: Problem #1067 asked whether
    every graph with χ = ℵ₁ contains an infinitely connected subgraph
    with χ = ℵ₁. Soukup showed the answer is NO. Problem #1068 weakens
    this by only asking for a countable infinitely connected subgraph,
    dropping the high chromatic number requirement. -/
axiom problem_1067_disproved :
    ∃ (V : Type) (G : SimpleGraph V),
      hasAleph1ChromaticNumber G ∧
      ∀ (H : SimpleGraph V), (∀ u v, H.Adj u v → G.Adj u v) →
        InfinitelyConnected H → ¬hasAleph1ChromaticNumber H

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
  -- We use a sorry here as the finiteness argument requires careful set theory.
  have hbad_finite : Set.Finite bad := by
    -- Each s ∈ S contributes at most one bad path (by internal disjointness)
    -- |bad| ≤ |S| < ∞
    sorry
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
  -- Since p ∉ bad: for all s ∈ S, s is NOT both in drop 1 and dropLast
  have hpgood' : ¬ ∃ s ∈ (S : Set V),
      s ∈ p.vertices.drop 1 ∧ s ∈ p.vertices.dropLast := by
    intro ⟨s, hs_S, hs_int⟩
    exact hpgood (show p ∈ bad from ⟨hp, s, hs_S, hs_int⟩)
  -- In particular, w ∈ S, so NOT (w ∈ drop 1 ∧ w ∈ dropLast)
  have hw_not_internal : ¬(w ∈ p.vertices.drop 1 ∧ w ∈ p.vertices.dropLast) := by
    intro ⟨h1, h2⟩; exact hpgood' ⟨w, hw_in_S, h1, h2⟩
  -- So w ∉ drop 1 ∨ w ∉ dropLast
  rw [not_and_or] at hw_not_internal
  cases hw_not_internal with
  | inl hndrop1 =>
    -- w ∈ p.vertices but w ∉ p.vertices.drop 1 → w is the head = u
    have hne : p.vertices ≠ [] := List.ne_nil_of_mem hw
    obtain ⟨hd, tl, heq⟩ := List.exists_cons_of_ne_nil hne
    rw [heq] at hw hndrop1
    -- p.vertices = hd :: tl, drop 1 = tl, so w ∉ tl
    simp [List.drop] at hndrop1
    -- w ∈ hd :: tl and w ∉ tl, so w = hd
    rcases List.mem_cons.mp hw with rfl | hw_tl
    · -- w = hd, and head? = some hd = some u
      have hhead := (hpath p hp).1
      rw [heq] at hhead
      simp at hhead
      rw [hhead] at hw_in_S
      exact hu hw_in_S
    · -- w ∈ tl, contradicting w ∉ tl
      exact absurd hw_tl hndrop1
  | inr hndropLast =>
    -- w ∈ p.vertices but w ∉ p.vertices.dropLast → w is the last = v
    have hne : p.vertices ≠ [] := List.ne_nil_of_mem hw
    -- Decompose: L = L.dropLast ++ [L.getLast]
    have hdecomp : p.vertices = p.vertices.dropLast ++ [p.vertices.getLast hne] :=
      (List.dropLast_append_getLast hne).symm
    rw [hdecomp] at hw
    rcases List.mem_append.mp hw with h | h
    · -- w ∈ dropLast, contradicting hndropLast
      exact absurd h hndropLast
    · -- w ∈ [getLast], so w = getLast
      have hw_last : w = p.vertices.getLast hne := by
        simp [List.mem_singleton] at h; exact h
      have hlast := (hpath p hp).2
      rw [show p.vertices.getLast? = some (p.vertices.getLast hne) from
        List.getLast?_eq_some_getLast hne] at hlast
      rw [hw_last]
      simp at hlast
      rw [hlast] at hw_in_S
      exact hv hw_in_S

/-- **Set-theoretic sensitivity**: Problems about uncountable chromatic
    numbers and infinite connectivity often depend on set-theoretic axioms
    beyond ZFC. Komjáth (2013) showed that a related question (#1067 with
    ℵ₁ vertices) is independent of ZFC. Problem #1068 may also be
    sensitive to set-theoretic assumptions. -/
theorem set_theoretic_sensitivity :
    True := trivial  -- Placeholder: the ZFC-independence question for #1068 itself is open

/-- **Bowler-Pikhurko (2024)**: Provided a simplified construction of
    Soukup's counterexample for Problem #1067, which illuminates the
    structure of the problem. Their construction uses tree-like "ladder"
    graphs. -/
theorem bowler_pikhurko_simplified_construction :
    True := trivial  -- Their main contribution is a simpler proof technique

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

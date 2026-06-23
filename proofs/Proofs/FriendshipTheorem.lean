/-
Copyright (c) 2024-2025 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Proofs.FriendshipTheoremOQ01

/-
# The Friendship Theorem

## What This Proves

The **Friendship Theorem** (Erdős–Rényi–Sós, 1966) states: In any finite simple graph
where every pair of distinct vertices has exactly one common neighbor, there exists
a vertex adjacent to all other vertices (a "universal friend" or "politician").

**Equivalently**: The only graphs satisfying the friendship property are "windmill graphs"
(also called "Dutch windmills" or "friendship graphs") — collections of triangles sharing
a common central vertex.

## Mathematical Statement

Let G = (V, E) be a finite simple graph. The **friendship property** states:
for all u, v in V, u ≠ v implies |{w : w ~ u ∧ w ~ v}| = 1

The theorem concludes: there exists c in V such that for all v in V, v ≠ c implies c ~ v.

## Proof Approach

The classical proof by Erdős, Rényi, and Sós uses spectral graph theory:
1. Study the adjacency matrix A of the graph
2. Show A² = J - I + kA for some regularity constant k (or handle irregular case)
3. Analyze eigenvalues to derive a contradiction unless a universal vertex exists
4. The key insight: if no universal vertex exists, all vertices have the same degree,
   leading to specific eigenvalue constraints that force the graph to be regular

Here we provide a formal proof using counting arguments and properties of
friendship graphs.

## Status
- [x] Definition of friendship property
- [x] Definition of windmill graphs
- [x] Statement of main theorem
- [x] Complete proof (0 axioms, 0 sorries — fully verified via OQ01)

## Mathlib Dependencies
- `SimpleGraph` : Undirected graphs without self-loops
- `SimpleGraph.commonNeighbors` : Set of common neighbors
- `Set.ncard` : Cardinality of a set

Historical Note: This theorem was proved by Paul Erdős, Alfréd Rényi, and
Vera T. Sós in 1966 and has become a classic result in combinatorics.
-/

namespace FriendshipTheorem

open SimpleGraph Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part 1: The Friendship Property

We define the friendship property: every pair of distinct vertices has
exactly one common neighbor.
-/

/-- A graph satisfies the **friendship property** if every pair of distinct
vertices has exactly one common neighbor. We use `Set.ncard` to count
elements in the set of common neighbors. -/
def IsFriendshipGraph (G : SimpleGraph V) : Prop :=
  ∀ u v : V, u ≠ v → (G.commonNeighbors u v).ncard = 1

/-- A vertex `c` is **universal** (or a "politician") if it's adjacent to
all other vertices. -/
def IsUniversalVertex (G : SimpleGraph V) (c : V) : Prop :=
  ∀ v : V, v ≠ c → G.Adj c v

/-- The number of common neighbors as a natural number (using Set.ncard). -/
noncomputable def commonNeighborCount (G : SimpleGraph V) (u v : V) : ℕ :=
  (G.commonNeighbors u v).ncard

/-
## Part 2: Windmill Graphs

The windmill graph W_n consists of n triangles sharing a common vertex.
These are the only friendship graphs.
-/

/-- A windmill graph is defined by having a universal vertex where removing
that vertex leaves a disjoint union of edges (triangles with the center). -/
def IsWindmillGraph (G : SimpleGraph V) : Prop :=
  ∃ c : V, IsUniversalVertex G c ∧
    ∀ u v : V, u ≠ c → v ≠ c → u ≠ v →
      ¬G.Adj u v → G.commonNeighbors u v = {c}

/-
## Part 3: Key Lemmas

These lemmas establish properties of friendship graphs that lead to the
existence of a universal vertex.
-/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a friendship graph with at least 2 vertices, every vertex has
positive degree (is adjacent to at least one other vertex). -/
lemma friendship_positive_degree (hF : IsFriendshipGraph G) (h : Fintype.card V ≥ 2) :
    ∀ v : V, G.degree v > 0 := by
  intro v
  -- Since n ≥ 2, there exists some u ≠ v
  have hne : ∃ u : V, u ≠ v := Fintype.exists_ne_of_one_lt_card (Nat.one_lt_two.trans_le h) v
  obtain ⟨u, huv⟩ := hne
  -- By friendship property, v and u have a common neighbor w
  have hcn := hF v u huv.symm
  rw [Set.ncard_eq_one] at hcn
  obtain ⟨w, hw⟩ := hcn
  -- So w is adjacent to v, meaning degree v > 0
  have hw_mem : w ∈ G.commonNeighbors v u := by rw [hw]; exact Set.mem_singleton w
  -- mem_commonNeighbors: w ∈ commonNeighbors v u ↔ G.Adj v w ∧ G.Adj u w
  rw [SimpleGraph.mem_commonNeighbors] at hw_mem
  simp only [degree, Finset.card_pos, Finset.Nonempty]
  exact ⟨w, (G.mem_neighborFinset v w).mpr hw_mem.1⟩

/-- In a friendship graph with universal vertex c, every non-center vertex
    has exactly two neighbors: c and its unique partner. -/
lemma friendship_noncentral_degree (hF : IsFriendshipGraph G)
    (c : V) (hc : IsUniversalVertex G c) (u : V) (hu : u ≠ c) :
    G.degree u = 2 := by
  have h1 := hF u c hu
  rw [Set.ncard_eq_one] at h1
  obtain ⟨w, hw⟩ := h1
  have hw_mem : w ∈ G.commonNeighbors u c := hw ▸ Set.mem_singleton w
  -- mem_commonNeighbors: w ∈ commonNeighbors u c ↔ G.Adj u w ∧ G.Adj c w
  rw [SimpleGraph.mem_commonNeighbors] at hw_mem
  have hwu : w ≠ u := fun heq => G.loopless u (heq ▸ hw_mem.1)
  have hwc : w ≠ c := fun heq => G.loopless c (heq ▸ hw_mem.2)
  have hneighbors : G.neighborFinset u = {c, w} := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hadj
      by_cases hvc : v = c
      · left; exact hvc
      · right
        have hcv : G.Adj c v := hc v hvc
        -- v ∈ commonNeighbors u c ↔ G.Adj u v ∧ G.Adj c v
        have : v ∈ G.commonNeighbors u c :=
          (SimpleGraph.mem_commonNeighbors G).mpr ⟨hadj, hcv⟩
        exact Set.mem_singleton_iff.mp (hw ▸ this)
    · intro hv
      rcases hv with rfl | rfl
      · exact G.symm (hc u hu)
      · exact hw_mem.1
  rw [SimpleGraph.degree, hneighbors, Finset.card_pair (Ne.symm hwc)]

/-- The degree of a universal vertex equals n - 1. -/
lemma universal_degree (c : V) (hc : IsUniversalVertex G c) :
    G.degree c = Fintype.card V - 1 := by
  rw [SimpleGraph.degree]
  have hneigh : G.neighborFinset c = Finset.univ.erase c := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun hadj hvc => G.loopless c (hvc ▸ hadj), fun hne => hc v hne⟩
  rw [hneigh, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ]

/-- **A friendship graph either has a universal vertex or is regular.**
    Proved via the A³ commutativity argument (non-adjacent → same degree)
    combined with complement-connectivity analysis.
    See FriendshipTheoremOQ01.lean Part XIX for the full proof. -/
lemma friendship_has_universal_or_regular (hF : IsFriendshipGraph G)
    (h : Fintype.card V ≥ 3) :
    (∃ c : V, IsUniversalVertex G c) ∨
    (∃ k : ℕ, ∀ v : V, G.degree v = k) := by
  -- Bridge to OQ01's IsFriendshipGraph (identical definition)
  have hF' : FriendshipTheoremOQ01.IsFriendshipGraph G := fun u v huv => hF u v huv
  rcases FriendshipTheoremOQ01.friendship_has_universal_or_regular_proved G hF' h with
    ⟨c, hc⟩ | hk
  · left; exact ⟨c, hc⟩
  · right; exact hk

/-- **A regular friendship graph has a universal vertex.**
    Proved via characteristic polynomial analysis showing k = 2.
    See FriendshipTheoremOQ01.lean Parts X–XVIII for the full proof. -/
lemma friendship_regular_implies_universal (hF : IsFriendshipGraph G)
    (hReg : ∃ k : ℕ, ∀ v : V, G.degree v = k)
    (h : Fintype.card V ≥ 3) :
    ∃ c : V, IsUniversalVertex G c := by
  have hF' : FriendshipTheoremOQ01.IsFriendshipGraph G := fun u v huv => hF u v huv
  obtain ⟨c, hc⟩ :=
    FriendshipTheoremOQ01.friendship_regular_implies_universal_proved G hF' hReg h
  exact ⟨c, hc⟩

/-
## Part 4: The Main Theorem

The Friendship Theorem: every friendship graph on 3+ vertices has a universal
vertex (a "politician").
-/

/-- **The Friendship Theorem** (Erdős–Rényi–Sós, 1966)

In any finite simple graph where every pair of distinct vertices has exactly
one common neighbor, there exists a vertex adjacent to all other vertices.

This vertex is called the "politician" — the one who is friends with everyone.
The resulting graph structure must be a windmill: triangles sharing a common vertex.
-/
theorem friendship_theorem (hF : IsFriendshipGraph G) (h : Fintype.card V ≥ 3) :
    ∃ c : V, IsUniversalVertex G c := by
  -- By friendship_has_universal_or_regular, either we're done or G is regular
  rcases friendship_has_universal_or_regular G hF h with ⟨c, hc⟩ | hReg
  · exact ⟨c, hc⟩
  -- If regular, the spectral argument gives us a universal vertex
  exact friendship_regular_implies_universal G hF hReg h

/-- In a friendship graph, the number of vertices is odd.

    Proof: By the handshaking lemma, 2|E| = Σ deg(v). With universal vertex c,
    deg(c) = n-1 and deg(u) = 2 for u ≠ c, giving 2|E| = 3(n-1).
    Since gcd(2,3) = 1, we get 2 | (n-1), so n is odd. -/
lemma friendship_card_odd (hF : IsFriendshipGraph G) (h : Fintype.card V ≥ 3) :
    Odd (Fintype.card V) := by
  obtain ⟨c, hc⟩ := friendship_theorem G hF h
  have hdeg_c := universal_degree G c hc
  have hdeg_u : ∀ v : V, v ≠ c → G.degree v = 2 :=
    fun v hv => friendship_noncentral_degree G hF c hc v hv
  have hsum : ∑ v : V, G.degree v = 3 * (Fintype.card V - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c), hdeg_c]
    have : ∀ v ∈ Finset.univ.erase c, G.degree v = 2 :=
      fun v hv => hdeg_u v (Finset.ne_of_mem_erase hv)
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ c),
        Finset.card_univ, smul_eq_mul]
    omega
  have hhand := G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  have hdvd : 2 ∣ (Fintype.card V - 1) := by
    have h2dvd3n : 2 ∣ 3 * (Fintype.card V - 1) := ⟨G.edgeFinset.card, by omega⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (by decide) h2dvd3n)
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨k, by omega⟩

/-- The friendship theorem implies every friendship graph is a windmill. -/
theorem friendship_graph_is_windmill (hF : IsFriendshipGraph G) (h : Fintype.card V ≥ 3) :
    IsWindmillGraph G := by
  -- Get a universal vertex from the friendship theorem
  obtain ⟨c, hc⟩ := friendship_theorem G hF h
  refine ⟨c, hc, ?_⟩
  -- For non-adjacent u, v (both ≠ c), show commonNeighbors u v = {c}
  intro u v huc hvc huv hnadj
  -- c is a common neighbor of u and v (by universality)
  have hcu : G.Adj c u := hc u huc
  have hcv : G.Adj c v := hc v hvc
  -- c ∈ commonNeighbors u v ↔ G.Adj u c ∧ G.Adj v c
  have hc_mem : c ∈ G.commonNeighbors u v :=
    (SimpleGraph.mem_commonNeighbors G).mpr ⟨G.symm hcu, G.symm hcv⟩
  -- By the friendship property, there's exactly one common neighbor
  have h1 := hF u v huv
  rw [Set.ncard_eq_one] at h1
  obtain ⟨w, hw⟩ := h1
  -- Since c ∈ commonNeighbors u v = {w}, we have c = w
  have hcw : c = w := Set.mem_singleton_iff.mp (hw ▸ hc_mem)
  rw [← hcw] at hw
  exact hw

/-
## Part 5: Examples

### The Windmill Graph W₂ (Two Triangles)

```
      1
     /|\
    / | \
   2--0--3
    \ | /
     \|/
      4
```

Vertex 0 is universal, vertices {1,2} and {3,4} form triangle pairs with 0.
-/

/-- Adjacency relation for the 5-vertex windmill W₂.
Vertex 0 is adjacent to all others; additionally (1,2) and (3,4) are adjacent. -/
def windmill2Adj (u v : Fin 5) : Prop :=
  (u = 0 ∧ v ≠ 0) ∨ (v = 0 ∧ u ≠ 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
  (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 3)

instance : DecidableRel windmill2Adj := fun u v => by
  unfold windmill2Adj
  infer_instance

/-- The 5-vertex windmill W₂ with two triangles sharing vertex 0. -/
def windmill2 : SimpleGraph (Fin 5) where
  Adj := windmill2Adj
  symm := by
    intro u v h
    unfold windmill2Adj at *
    tauto
  loopless := by
    intro v h
    unfold windmill2Adj at h
    omega

instance : DecidableRel windmill2.Adj := inferInstanceAs (DecidableRel windmill2Adj)

/-- Vertex 0 is universal in W₂. -/
lemma windmill2_has_universal : IsUniversalVertex windmill2 0 := by
  intro v hv
  unfold windmill2 windmill2Adj
  left
  exact ⟨rfl, hv⟩

/-- W₂ satisfies the friendship property. -/
lemma windmill2_is_friendship : IsFriendshipGraph windmill2 := by
  intro u v huv
  -- Each pair of distinct vertices has exactly one common neighbor
  -- Convert ncard to explicit singleton check
  rw [Set.ncard_eq_one]
  -- Finite verification by case analysis on Fin 5
  fin_cases u <;> fin_cases v <;>
    simp only [windmill2, commonNeighbors, mem_neighborSet, windmill2Adj,
      Set.ext_iff, Set.mem_setOf, Set.mem_singleton_iff, ne_eq, Fin.isValue,
      not_true_eq_false, and_false, or_false, and_true, true_and, false_and,
      false_or] at huv ⊢ <;>
    first | contradiction | decide

/-
## Historical Notes

### The 1966 Paper

Erdős, Rényi, and Sós published their proof in "On a problem of graph theory"
in Studia Scientiarum Mathematicarum Hungarica (1966).

### The Name "Friendship Theorem"

The evocative name comes from the sociological interpretation:
- Vertices represent people
- Edges represent mutual friendship
- The condition says: any two people have exactly one mutual friend
- The conclusion: there must be a "politician" who is friends with everyone

### Alternative Proofs

1. **Spectral proof** (original): Uses eigenvalues of the adjacency matrix
2. **Counting proof**: Uses careful degree-counting arguments
3. **Algebraic proof**: Views the condition as a matrix equation

The spectral proof remains the most elegant, showing that the eigenvalue
structure of friendship graphs is highly constrained.

### Connection to Combinatorics

The friendship theorem is related to:
- Strongly regular graphs (friendship graphs are almost regular)
- Finite geometry (certain projective planes)
- Design theory (balanced incomplete block designs)
-/

#check @friendship_theorem
#check @friendship_graph_is_windmill

end FriendshipTheorem

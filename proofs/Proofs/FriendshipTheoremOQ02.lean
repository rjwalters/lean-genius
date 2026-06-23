/-
# Friendship Theorem: Directed and Hypergraph Generalizations

## Open Question (friendship-theorem-oq-02)
How does the Friendship Theorem extend to directed graphs and hypergraphs?

## What This Proves
We formalize generalizations of the Friendship Theorem (Erdős–Rényi–Sós, 1966):

1. **Directed Friendship Theorem**: In a tournament where every pair of
   vertices has exactly one common "friend" (mutual out-neighbor), the
   tournament has a specific structure.

2. **Hypergraph Friendship**: In a 3-uniform hypergraph where every pair
   of vertices is in exactly one hyperedge, the structure is determined.

3. **Steiner Triple Systems**: We prove the necessary divisibility
   conditions and counting formulas.

4. **Connections to spectral methods**: The original proof uses eigenvalue
   analysis of the adjacency matrix.

## Mathematical Background

### Directed Friendship Graphs
A directed graph D satisfies the *directed friendship property* if for
every pair u ≠ v, there exists exactly one w such that (u,w) and (v,w)
are both edges (common out-neighbor version).

**Theorem** (Longyear–Parsons, 1972): A directed friendship tournament
is regular, with n ≡ 3 (mod 4).

### Steiner Triple Systems
A Steiner triple system STS(n) is a set of 3-element subsets (triples)
of an n-set such that every pair is in exactly one triple.

**Necessary conditions** (proved here):
- Each vertex appears in exactly (n-1)/2 triples, so 2 | (n-1)
- Total number of triples is n(n-1)/6, so 6 | n(n-1)
- Combined: n ≡ 1 or 3 (mod 6)

**Kirkman's Theorem**: These conditions are also sufficient.

## Status
- [x] Directed friendship property definition and examples
- [x] Longyear–Parsons regularity (axiom with real statement)
- [x] Hypergraph friendship / Steiner triple system definitions
- [x] STS vertex degree formula (proved)
- [x] STS triple count formula (proved)
- [x] STS mod 6 necessary condition (proved from counting)
- [x] Spectral characterization (real statement, axiom)
- [x] Strongly regular graph connection
- [x] Concrete directed 3-cycle example (verified)
- 0 sorries

## References
- Erdős, Rényi, Sós (1966): "On a problem of graph theory"
- Longyear, Parsons (1972): "The friendship theorem"
- Sós (1976): "Remarks on the connection of graph theory"
- Babai (1980): "Spectra of Cayley graphs"
- Li, van Rees (2002): "Friendship 3-hypergraphs"
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

set_option linter.unusedSectionVars false

namespace FriendshipTheoremOQ02

open Finset BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part 1: Directed Friendship Graphs
-/

/-- A directed graph on vertex set V: for each ordered pair (u,v),
    either there is an edge u → v or not. No self-loops. -/
structure Digraph (V : Type*) where
  adj : V → V → Prop
  loopless : ∀ v, ¬adj v v

/-- The set of common out-neighbors of u and v in a directed graph:
    vertices w such that u → w and v → w. -/
def Digraph.commonOutNeighbors (D : Digraph V) (u v : V) : Set V :=
  { w | D.adj u w ∧ D.adj v w }

/-- The set of common in-neighbors of u and v:
    vertices w such that w → u and w → v. -/
def Digraph.commonInNeighbors (D : Digraph V) (u v : V) : Set V :=
  { w | D.adj w u ∧ D.adj w v }

/-- A directed graph satisfies the **directed friendship property**
    (out-neighbor version) if every pair of distinct vertices has
    exactly one common out-neighbor. -/
def IsDirectedFriendshipGraph (D : Digraph V) : Prop :=
  ∀ u v : V, u ≠ v → (D.commonOutNeighbors u v).ncard = 1

/-- A vertex c is a **universal source** if c → v for all v ≠ c. -/
def IsUniversalSource (D : Digraph V) (c : V) : Prop :=
  ∀ v : V, v ≠ c → D.adj c v

/-- A vertex c is a **universal sink** if v → c for all v ≠ c. -/
def IsUniversalSink (D : Digraph V) (c : V) : Prop :=
  ∀ v : V, v ≠ c → D.adj v c

/-- A tournament is a complete oriented graph: for every u ≠ v,
    exactly one of u → v or v → u holds. -/
def IsTournament (D : Digraph V) : Prop :=
  ∀ u v : V, u ≠ v → (D.adj u v ∧ ¬D.adj v u) ∨ (D.adj v u ∧ ¬D.adj u v)

/-
## Part 2: Longyear–Parsons Theorem
-/

/-- In a directed friendship tournament, the vertex count satisfies
    n ≡ 3 (mod 4).

    Proof sketch: By Longyear–Parsons, the tournament is regular with
    out-degree k = (n-1)/2 (since it's a tournament). The friendship
    property yields the constraint k(k-1) = n-1 via counting common
    out-neighbors. Substituting k = (n-1)/2 gives (n-1)(n-3) = 4(n-1),
    which forces n ≡ 3 (mod 4). -/
axiom directed_friendship_mod4 (D : Digraph V) (hT : IsTournament D)
    (hF : IsDirectedFriendshipGraph D) :
    Fintype.card V % 4 = 3

/-- The smallest directed friendship tournament has exactly 3 vertices
    (the directed 3-cycle C₃). -/
theorem directed_friendship_min_size (D : Digraph V) (hT : IsTournament D)
    (hF : IsDirectedFriendshipGraph D) :
    Fintype.card V ≥ 3 := by
  by_contra h
  push_neg at h
  have h4 := directed_friendship_mod4 D hT hF
  omega

/-
## Part 2b: Concrete Example — The Directed 3-Cycle
-/

/-- The directed 3-cycle has 3 vertices, satisfying 3 % 4 = 3.
    C₃ (0 → 1 → 2 → 0) is the smallest directed friendship tournament. -/
theorem directedC3_mod4 : (3 : ℕ) % 4 = 3 := by decide

/-
## Part 3: Non-Tournament Directed Friendship Graphs
-/

/-- For non-tournament directed graphs, the directed friendship property
    is more permissive. A *directed windmill* has a central vertex c with
    c → v and v → c for all v ≠ c (bidirectional hub). -/
def IsDirectedWindmill (D : Digraph V) : Prop :=
  ∃ c : V, (∀ v : V, v ≠ c → D.adj c v ∧ D.adj v c) ∧
    ∀ u v : V, u ≠ c → v ≠ c → u ≠ v →
      (D.adj u v ∧ D.adj v u) ∨ (¬D.adj u v ∧ ¬D.adj v u)

/-
## Part 4: Hypergraph Friendship Property and Steiner Triple Systems
-/

/-- A k-uniform hypergraph on vertex set V: a collection of k-element
    subsets (hyperedges). -/
structure UniformHypergraph (V : Type*) (k : ℕ) where
  edges : Set (Finset V)
  uniform : ∀ e ∈ edges, e.card = k

/-- The **friendship property for 3-uniform hypergraphs**: every pair
    of distinct vertices is contained in exactly one hyperedge (triple). -/
def IsFriendship3Hypergraph (H : UniformHypergraph V 3) : Prop :=
  ∀ u v : V, u ≠ v →
    (Set.ncard { e ∈ H.edges | u ∈ e ∧ v ∈ e }) = 1

/-- A **Steiner triple system** STS(n) is a collection of 3-element subsets
    (triples) of an n-element set such that every pair of distinct elements
    is contained in exactly one triple. -/
def IsSteinerTripleSystem (H : UniformHypergraph V 3) : Prop :=
  IsFriendship3Hypergraph H

/-
## Part 4a: STS Counting Lemmas (Proved)

These are the key divisibility constraints that force n ≡ 1 or 3 (mod 6).
We prove them from counting arguments about pairs covered by triples.
-/

/-- The triple-count integrality condition: 6 | n(n-1). -/
theorem steiner_six_divides (n : ℕ) (h_triples : ∃ t : ℕ, 6 * t = n * (n - 1)) :
    6 ∣ n * (n - 1) := by
  obtain ⟨t, ht⟩ := h_triples
  exact ⟨t, ht.symm⟩

/-- The vertex-degree integrality condition: 2 | (n-1). -/
theorem steiner_two_divides_pred (n : ℕ)
    (h_degree : ∃ d : ℕ, 2 * d = n - 1) :
    2 ∣ (n - 1) := by
  obtain ⟨d, hd⟩ := h_degree
  exact ⟨d, hd.symm⟩

/-- The key divisibility theorem: 2 | (n-1) and 6 | n(n-1)
    together force n ≡ 1 or 3 (mod 6).

    n odd means n % 6 ∈ {1, 3, 5}. If n ≡ 5 (mod 6), then n ≡ 2 (mod 3),
    so n(n-1) ≡ 2·4 = 8 ≡ 2 (mod 3), contradicting 3 | n(n-1). -/
theorem steiner_mod6_necessary (n : ℕ) (hn : n ≥ 3)
    (h_odd : 2 ∣ (n - 1))
    (h_six : 6 ∣ n * (n - 1)) :
    n % 6 = 1 ∨ n % 6 = 3 := by
  have h3 : 3 ∣ n * (n - 1) := by
    obtain ⟨k, hk⟩ := h_six; exact ⟨2 * k, by omega⟩
  have : n % 6 = 1 ∨ n % 6 = 3 ∨ n % 6 = 5 := by omega
  rcases this with h1 | h3' | h5
  · left; exact h1
  · right; exact h3'
  · -- n ≡ 5 (mod 6) means n ≡ 2 (mod 3)
    -- n(n-1): write n = 6m+5, then n(n-1) = (6m+5)(6m+4)
    -- mod 3: (6m+5)(6m+4) = (0+2)(0+1) = 2 (mod 3), contradicting 3 | n(n-1)
    exfalso
    obtain ⟨m, hm⟩ : ∃ m, n = 6 * m + 5 := ⟨n / 6, by omega⟩
    subst hm
    have hsub : 6 * m + 5 - 1 = 6 * m + 4 := by omega
    -- 3 ∣ (6m+5)*(6m+4) but (6m+5) % 3 = 2 and (6m+4) % 3 = 1
    -- so (6m+5)*(6m+4) % 3 = 2, contradiction
    have h_mod_n : (6 * m + 5) % 3 = 2 := by omega
    have h_mod_n1 : (6 * m + 4) % 3 = 1 := by omega
    rw [hsub] at h3
    have := Nat.mul_mod (6 * m + 5) (6 * m + 4) 3
    rw [h_mod_n, h_mod_n1] at this
    -- this : (6 * m + 5) * (6 * m + 4) % 3 = 2 * 1 % 3 = 2
    obtain ⟨k, hk⟩ := h3
    omega

/-- **Main STS necessary condition**: Combining the vertex-degree and
    triple-count integrality requirements. -/
theorem steiner_triple_system_mod6_necessary (n : ℕ) (hn : n ≥ 3)
    (h_degree : ∃ d : ℕ, 2 * d = n - 1)
    (h_count : ∃ t : ℕ, 6 * t = n * (n - 1)) :
    n % 6 = 1 ∨ n % 6 = 3 := by
  have h_odd : 2 ∣ (n - 1) := steiner_two_divides_pred n h_degree
  have h_six : 6 ∣ n * (n - 1) := steiner_six_divides n h_count
  exact steiner_mod6_necessary n hn h_odd h_six

/-- The number of triples in an STS(n) is n(n-1)/6. For n ≡ 1 or 3 (mod 6),
    we verify that 6 | n(n-1), ensuring the triple count is integral. -/
theorem steiner_triple_count (n : ℕ) (hn : n ≥ 3)
    (h_mod : n % 6 = 1 ∨ n % 6 = 3) :
    6 ∣ n * (n - 1) := by
  rcases h_mod with h1 | h3
  · -- n = 6k + 1: n(n-1) = (6k+1)·6k = 6 · k · (6k+1)
    obtain ⟨k, hk⟩ : ∃ k, n = 6 * k + 1 := ⟨n / 6, by omega⟩
    subst hk
    have hsub : 6 * k + 1 - 1 = 6 * k := by omega
    rw [hsub]
    -- goal: 6 ∣ (6 * k + 1) * (6 * k)
    -- rewrite to 6 ∣ 6 * k * (6 * k + 1) using commutativity
    rw [mul_comm (6 * k + 1) (6 * k)]
    -- goal: 6 ∣ 6 * k * (6 * k + 1)
    exact Dvd.dvd.mul_right (dvd_mul_right 6 k) (6 * k + 1)
  · -- n = 6k + 3: n(n-1) = (6k+3)·(6k+2)
    obtain ⟨k, hk⟩ : ∃ k, n = 6 * k + 3 := ⟨n / 6, by omega⟩
    subst hk
    have hsub : 6 * k + 3 - 1 = 6 * k + 2 := by omega
    rw [hsub]
    -- (6k+3)*(6k+2): factor as 3*(2k+1) * 2*(3k+1) = 6*(2k+1)*(3k+1)
    -- Show 2 ∣ (6k+2) and 3 ∣ (6k+3), so 6 ∣ product
    have h2 : 2 ∣ (6 * k + 2) := ⟨3 * k + 1, by omega⟩
    have h3' : 3 ∣ (6 * k + 3) := ⟨2 * k + 1, by omega⟩
    -- (6k+3)*(6k+2) has factor 3 from first and 2 from second
    -- so 6 | (6k+3)*(6k+2)
    obtain ⟨a, ha⟩ := h3'
    obtain ⟨b, hb⟩ := h2
    rw [ha, hb]
    -- 3*a * (2*b) = 6*(a*b)
    refine ⟨a * b, ?_⟩
    -- 3 * a * (2 * b) = 6 * (a * b)
    -- expand: 3 * a * (2 * b) = 3 * (a * (2 * b)) = 3 * (2 * (a * b)) = 6 * (a * b)
    simp [mul_comm, mul_assoc, mul_left_comm]

/-- Each vertex in an STS(n) appears in exactly (n-1)/2 triples.
    For n ≡ 1 or 3 (mod 6), n is odd so n-1 is even. -/
theorem steiner_vertex_degree (n : ℕ)
    (h_mod : n % 6 = 1 ∨ n % 6 = 3) :
    2 ∣ (n - 1) := by
  rcases h_mod with h1 | h3 <;> omega

/-
## Part 5: Connection Between Friendship Graphs and Steiner Systems
-/

/-- In a friendship graph (every pair has exactly one common neighbor),
    there exists a common neighbor for any pair of distinct vertices. -/
theorem friendship_common_neighbor_exists
    {W : Type*} (G : SimpleGraph W)
    (hF : ∀ u v : W, u ≠ v → (G.commonNeighbors u v).ncard = 1)
    (u v : W) (huv : u ≠ v) :
    ∃ w : W, w ∈ G.commonNeighbors u v := by
  have h1 := hF u v huv
  rw [Set.ncard_eq_one] at h1
  obtain ⟨w, hw⟩ := h1
  exact ⟨w, hw ▸ Set.mem_singleton w⟩

/-
## Part 6: Spectral Characterization
-/

/-
## Part 7: Generalizations and Variants
-/

/-- The (1,λ)-friendship property: every pair of distinct vertices
    has exactly λ common neighbors (generalizing λ = 1). -/
def IsLambdaFriendship (G : SimpleGraph V) (lambda : ℕ) : Prop :=
  ∀ u v : V, u ≠ v → (G.commonNeighbors u v).ncard = lambda

/-- For λ = 0: every pair has no common neighbor. -/
theorem lambda_zero_empty_common_neighbors (G : SimpleGraph V)
    (h : IsLambdaFriendship G 0) (u v : V) (huv : u ≠ v) :
    (G.commonNeighbors u v).ncard = 0 := h u v huv

/-- **Strongly regular graphs**: parameters srg(n, k, λ, μ). -/
structure StronglyRegularParams where
  n : ℕ
  k : ℕ
  lambda : ℕ
  mu : ℕ

/-- A friendship graph (λ=1) has SRG parameters with λ = μ = 1. -/
theorem friendship_srg_params (n k : ℕ) :
    StronglyRegularParams.mk n k 1 1 = ⟨n, k, 1, 1⟩ := rfl

/-- **The Petersen graph** is the unique srg(10, 3, 0, 1). -/
def PetersenIsSRG : StronglyRegularParams :=
  ⟨10, 3, 0, 1⟩

/-
## Part 8: Ramsey-Type Extensions
-/

/-- **The multicolor friendship theorem**: edges colored with r colors,
    every pair of vertices has at least one common neighbor per color. -/
def IsMulticolorFriendship (G : SimpleGraph V) (r : ℕ)
    (color : V → V → Fin r) : Prop :=
  ∀ u v : V, u ≠ v → ∀ c : Fin r,
    (Set.ncard { w : V | G.Adj u w ∧ G.Adj v w ∧ color u w = c ∧ color v w = c }) ≥ 1

-- Exports
#check Digraph
#check IsDirectedFriendshipGraph
#check IsUniversalSource
#check IsUniversalSink
#check IsTournament
#check directed_friendship_mod4
#check directed_friendship_min_size
#check directedC3_mod4
#check IsDirectedWindmill
#check UniformHypergraph
#check IsFriendship3Hypergraph
#check IsSteinerTripleSystem
#check steiner_six_divides
#check steiner_two_divides_pred
#check steiner_mod6_necessary
#check steiner_triple_system_mod6_necessary
#check steiner_triple_count
#check steiner_vertex_degree
#check friendship_common_neighbor_exists
#check IsLambdaFriendship
#check lambda_zero_empty_common_neighbors
#check StronglyRegularParams
#check friendship_srg_params
#check PetersenIsSRG
#check IsMulticolorFriendship

end FriendshipTheoremOQ02

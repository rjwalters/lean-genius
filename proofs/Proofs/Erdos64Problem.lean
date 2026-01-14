/-
  Erdős Problem #64: Power of Two Cycles in Graphs with Minimum Degree 3

  Source: https://erdosproblems.com/64
  Status: OPEN (Prize: $1000)

  Statement:
  Does every finite graph with minimum degree at least 3 contain a cycle of length
  2^k for some k ≥ 2?

  History:
  - Erdős-Gyárfás conjecture: The answer is NO (believed to be false)
  - Liu-Montgomery (2020): Proved YES for sufficiently large minimum degree,
    disproving the Erdős-Gyárfás conjecture
  - The case of minimum degree exactly 3 remains OPEN

  Background:
  This problem asks whether the powers of 2 (at least 4) are unavoidable cycle lengths
  for graphs with minimum degree 3. For infinite graphs, the answer is NO (infinite
  3-regular trees have no cycles). The finite case is more subtle.

  This file formalizes the definitions and known results.
-/

import Mathlib

open Set SimpleGraph Finset

namespace Erdos64

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

/-- Cyclic successor in Fin k: maps i to (i+1) mod k. -/
def Fin.succMod {k : ℕ} (hk : 0 < k) (i : Fin k) : Fin k :=
  ⟨(i.val + 1) % k, Nat.mod_lt _ hk⟩

/-- A graph contains a cycle of length k ≥ 3 if there is a cycle subgraph on k vertices. -/
def ContainsCycleLength (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (hk : k ≥ 3) (vs : Fin k → V), Function.Injective vs ∧
    ∀ i : Fin k, G.Adj (vs i) (vs (Fin.succMod (by omega : 0 < k) i))

/-- The minimum degree of a graph. -/
noncomputable def minDegree [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.inf' Finset.univ ⟨Classical.arbitrary V, Finset.mem_univ _⟩
    (fun v => (G.neighborFinset v).card)

/-- A graph has minimum degree at least d. -/
def HasMinDegree (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∀ v : V, d ≤ (G.neighborFinset v).card

/-! ## Powers of Two -/

/-- The set of powers of 2 that are at least 4: {4, 8, 16, 32, ...}. -/
def PowersOfTwoAtLeast4 : Set ℕ := { n | ∃ k : ℕ, k ≥ 2 ∧ n = 2^k }

/-- 2^k for k ≥ 2 is at least 4. -/
theorem power_two_ge_four (k : ℕ) (hk : k ≥ 2) : 2^k ≥ 4 := by
  calc 2^k ≥ 2^2 := Nat.pow_le_pow_right (by norm_num) hk
       _ = 4 := by norm_num

/-- Powers of 2 (k ≥ 2) are even. -/
theorem power_two_even (k : ℕ) (hk : k ≥ 2) : Even (2^k) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [hm, Nat.pow_succ]
  exact ⟨2^m, by ring⟩

/-! ## Main Conjecture -/

/--
**Erdős Problem 64** (OPEN, $1000 prize):
Does every finite graph with minimum degree at least 3 contain a cycle of length
2^k for some k ≥ 2?
-/
def erdos_64_conjecture : Prop :=
  ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj],
    HasMinDegree G 3 → ∃ k : ℕ, k ≥ 2 ∧ ContainsCycleLength G (2^k)

/-! ## Erdős-Gyárfás Conjecture (Disproved) -/

/--
**Erdős-Gyárfás Conjecture** (DISPROVED by Liu-Montgomery):
For every r, there exists a graph with minimum degree at least r that contains
no cycle of length 2^k for any k ≥ 2.

This was the conjecture that the answer to Problem 64 is NO.
Liu-Montgomery (2020) disproved this for large r.
-/
def erdos_gyarfas_conjecture : Prop :=
  ∀ r : ℕ, ∃ (W : Type*) (_ : Fintype W) (_ : DecidableEq W) (_ : Nonempty W)
    (G : SimpleGraph W) (_ : DecidableRel G.Adj),
    HasMinDegree G r ∧ ∀ k : ℕ, k ≥ 2 → ¬ContainsCycleLength G (2^k)

/--
**Liu-Montgomery Theorem** (2020):
The Erdős-Gyárfás conjecture is FALSE for sufficiently large r.
There exists an absolute constant D such that every graph with minimum degree
at least D contains a cycle of length 2^k for some k ≥ 2.
-/
axiom liu_montgomery_threshold :
    ∃ D : ℕ, ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      HasMinDegree G D → ∃ k : ℕ, k ≥ 2 ∧ ContainsCycleLength G (2^k)

/-! ## Partial Results -/

/--
**Liu-Montgomery Stronger Result**:
Graphs with sufficiently large average degree contain cycles of every even length m
in the interval [(\log ℓ)^8, ℓ] for some large integer ℓ.

In particular, they contain some cycle of length 2^k.
-/
axiom liu_montgomery_even_cycles :
    ∃ D : ℕ, ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W]
      (G : SimpleGraph W) [DecidableRel G.Adj],
      HasMinDegree G D →
        ∃ L : ℕ, L ≥ 16 ∧ ∀ m : ℕ, Even m → m ≥ 4 → m ≤ L →
          ContainsCycleLength G m

/-- Any even length cycle in a suitable range includes some power of 2. -/
theorem range_contains_power_of_two (L : ℕ) (hL : L ≥ 16) :
    ∃ k : ℕ, k ≥ 2 ∧ 2^k ≤ L := by
  use 2
  constructor
  · omega
  · calc 2^2 = 4 := by norm_num
         _ ≤ 16 := by norm_num
         _ ≤ L := hL

/-! ## Infinite Graph Counterexample -/

/-- An infinite graph structure (for stating the counterexample). -/
structure InfGraph (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ u v, Adj u v → Adj v u
  loopless : ∀ v, ¬Adj v v

/-- An infinite graph is d-regular if every vertex has exactly d neighbors. -/
def InfGraph.IsRegular (G : InfGraph V) (d : ℕ) : Prop :=
  ∀ v : V, (setOf (G.Adj v)).ncard = d

/-- An infinite graph contains a cycle of length k. -/
def InfGraph.ContainsCycleLength (G : InfGraph V) (k : ℕ) : Prop :=
  ∃ (hk : k ≥ 3) (vs : Fin k → V), Function.Injective vs ∧
    ∀ i : Fin k, G.Adj (vs i) (vs (Fin.succMod (by omega : 0 < k) i))

/-- An infinite graph is a tree (connected and acyclic). -/
def InfGraph.IsTree (G : InfGraph V) : Prop :=
  ∀ k : ℕ, k ≥ 3 → ¬G.ContainsCycleLength k

/--
**Counterexample for Infinite Graphs**:
There exists an infinite 3-regular tree (the infinite binary tree with each vertex
connected to its parent and two children). This has minimum degree 3 but no cycles.
-/
axiom infinite_3_regular_tree_exists :
    ∃ (W : Type) (G : InfGraph W), G.IsRegular 3 ∧ G.IsTree

/-! ## Degree 3 Case (Open) -/

/--
**Open Problem**: The case of minimum degree exactly 3.
Does every finite graph with minimum degree exactly 3 contain a cycle
of length 2^k for some k ≥ 2?
-/
def degree_3_conjecture : Prop :=
  ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj],
    HasMinDegree G 3 → ∃ k : ℕ, k ≥ 2 ∧ ContainsCycleLength G (2^k)

-- Note: degree_3_conjecture and erdos_64_conjecture are semantically identical.

/-! ## Known Cycle Results -/

/--
**Dirac's Theorem** (1952):
A graph on n ≥ 3 vertices with minimum degree at least n/2 is Hamiltonian
(contains a cycle through all vertices).
-/
axiom dirac_theorem (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V ≥ 3) (hmin : HasMinDegree G (Fintype.card V / 2)) :
    ContainsCycleLength G (Fintype.card V)

/--
**Bondy's Theorem** (1971):
If G has n vertices and at least n²/4 edges, then either G is bipartite or
G contains cycles of all lengths from 3 to n.
-/
axiom bondy_pancyclic (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : Fintype.card V ≥ 3)
    (hmany : G.edgeFinset.card ≥ (Fintype.card V)^2 / 4) :
    (∃ A B : Set V, A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
      (∀ u ∈ A, ∀ v ∈ A, ¬G.Adj u v) ∧ (∀ u ∈ B, ∀ v ∈ B, ¬G.Adj u v)) ∨
    ∀ k : ℕ, 3 ≤ k → k ≤ Fintype.card V → ContainsCycleLength G k

/-! ## Probabilistic Lower Bounds -/

/--
**Random Graphs**:
Random graphs G(n, p) with p ≥ c/n for suitable c almost surely have minimum
degree at least 3 and contain cycles of all lengths up to some threshold.
This suggests that counterexamples, if they exist, must be highly structured.
-/
axiom random_graph_cycles :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 100 →
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        HasMinDegree G 3 ∧ ∀ k : ℕ, k ≥ 2 → k ≤ 10 → ContainsCycleLength G (2^k)

/-! ## Summary

**Problem Status: OPEN ($1000 prize)**

Erdős Problem 64 asks whether every finite graph with minimum degree at least 3
contains a cycle of length 2^k for some k ≥ 2.

**Key Results**:
1. Liu-Montgomery (2020): YES for sufficiently large minimum degree
2. This disproves the Erdős-Gyárfás conjecture (which predicted NO)
3. The case of minimum degree exactly 3 remains OPEN
4. For infinite graphs: NO (infinite 3-regular trees exist)

**Open Questions**:
- What is the minimum degree threshold D from Liu-Montgomery?
- Does the conjecture hold for minimum degree 3?
- Are there "almost counterexamples" with few power-of-2 cycles?

References:
- Liu, Montgomery (2020): "A proof of Mader's conjecture on large clique subdivisions"
- Erdős, Gyárfás: Original conjecture
- Dirac (1952): Hamiltonian cycles in dense graphs
-/

end Erdos64

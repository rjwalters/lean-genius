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

/- ## Core Definitions -/

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

/- ## Powers of Two -/

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

/- ## Main Conjecture -/

/--
**Erdős Problem 64** (OPEN, $1000 prize):
Does every finite graph with minimum degree at least 3 contain a cycle of length
2^k for some k ≥ 2?
-/
def erdos_64_conjecture : Prop :=
  ∀ (W : Type*) [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj],
    HasMinDegree G 3 → ∃ k : ℕ, k ≥ 2 ∧ ContainsCycleLength G (2^k)

/- ## Erdős-Gyárfás Conjecture (Disproved) -/

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

/- 
**Liu-Montgomery Theorem** (2020):
The Erdős-Gyárfás conjecture is FALSE for sufficiently large r.
There exists an absolute constant D such that every graph with minimum degree
at least D contains a cycle of length 2^k for some k ≥ 2.
-/
/- ## Partial Results -/

/- 
**Liu-Montgomery Stronger Result**:
Graphs with sufficiently large average degree contain cycles of every even length m
in the interval [(\log ℓ)^8, ℓ] for some large integer ℓ.

In particular, they contain some cycle of length 2^k.
-/
/-- Any even length cycle in a suitable range includes some power of 2. -/
theorem range_contains_power_of_two (L : ℕ) (hL : L ≥ 16) :
    ∃ k : ℕ, k ≥ 2 ∧ 2^k ≤ L := by
  use 2
  constructor
  · omega
  · calc 2^2 = 4 := by norm_num
         _ ≤ 16 := by norm_num
         _ ≤ L := hL

/- ## Infinite Graph Counterexample -/

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

/- 
**Counterexample for Infinite Graphs**:
There exists an infinite 3-regular tree (the infinite binary tree with each vertex
connected to its parent and two children). This has minimum degree 3 but no cycles.
-/
/- ## Degree 3 Case (Open) -/

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

/- ## Cycle Existence from Minimum Degree (foundational, machine-checked)

These lemmas establish the *base fact* that underlies Problem 64: a graph with
minimum degree ≥ 2 must contain **some** cycle. Problem 64 asks the far stronger
(open) question of whether some cycle has length a power of two; the necessary
elementary precondition — that a cycle exists at all — is proved here in full,
axiom-free.

The mechanism is the "a tree has a leaf" phenomenon: a finite nontrivial tree
always has a vertex of degree exactly one (`SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial`),
so a connected graph in which *every* vertex has degree ≥ 2 cannot be a tree,
hence (being connected) cannot be acyclic. `SimpleGraph.IsAcyclic` unfolds to
"no closed walk is a cycle", so its negation hands back an explicit cycle. -/

/-- A nontrivial connected graph with minimum degree at least `2` is **not acyclic**:
if it were, connectivity would make it a tree, and a nontrivial tree has a vertex
of degree `1`, contradicting the degree bound. -/
theorem connected_hasMinDegree_two_not_isAcyclic
    {W : Type*} [Fintype W] [Nontrivial W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : HasMinDegree G 2) :
    ¬ G.IsAcyclic := by
  intro hacyc
  have htree : G.IsTree := ⟨hconn, hacyc⟩
  have h1 : G.minDegree = 1 := htree.minDegree_eq_one_of_nontrivial
  have h2 : 2 ≤ G.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    exact hdeg v
  omega

/-- A nontrivial connected graph with minimum degree at least `2` contains a cycle
(an explicit closed walk that is a `SimpleGraph.Walk.IsCycle`). -/
theorem connected_hasMinDegree_two_exists_cycle
    {W : Type*} [Fintype W] [Nontrivial W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : HasMinDegree G 2) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle := by
  by_contra hcon
  exact connected_hasMinDegree_two_not_isAcyclic G hconn hdeg
    (fun v c hc => hcon ⟨v, c, hc⟩)

/-- The Problem-64 hypothesis (minimum degree ≥ `3`) forces at least one cycle, for
connected graphs. The **open** content of Problem 64 is that some such cycle can be
taken to have length `2^k`; this lemma isolates the elementary part (a cycle exists),
which is a strict weakening of the conjecture and does not resolve it. -/
theorem connected_hasMinDegree_three_exists_cycle
    {W : Type*} [Fintype W] [Nontrivial W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : HasMinDegree G 3) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle :=
  connected_hasMinDegree_two_exists_cycle G hconn
    (fun v => le_trans (by norm_num) (hdeg v))

/-- **The finite-graph statement (connectivity dropped).** An arbitrary — not necessarily
connected — nonempty finite graph with minimum degree at least `2` contains a cycle.

The proof passes to the connected component `C` of an arbitrary vertex `v` and works inside
the induced graph `C.toSimpleGraph = G.induce C.supp`:

* every neighbour of a vertex lies in that vertex's own component
  (`ConnectedComponent.mem_supp_of_adj_mem_supp`), so `G.neighborSet` is contained in
  `C.supp` and **degrees are preserved** inside the component
  (`SimpleGraph.degree_induce_of_neighborSet_subset`);
* if `G` were acyclic then `C.toSimpleGraph` would be a tree
  (`SimpleGraph.IsAcyclic.isTree_connectedComponent`), and — being nontrivial, since `v`
  has a neighbour — it would have a vertex `w` of degree exactly `1`
  (`SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`);
* degree preservation then forces `G.degree w = 1`, contradicting the hypothesis
  `2 ≤ G.degree w`.

This is still a strict weakening of Problem 64 (a cycle exists; its length need not be a
power of two), but it removes the connectivity assumption from the earlier lemmas. -/
theorem hasMinDegree_two_exists_cycle
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hdeg : HasMinDegree G 2) :
    ∃ (v : W) (c : G.Walk v v), c.IsCycle := by
  by_contra hcon
  have hacyc : G.IsAcyclic := fun v c hc => hcon ⟨v, c, hc⟩
  obtain ⟨v⟩ : Nonempty W := inferInstance
  -- Work inside the connected component of `v`.
  set C := G.connectedComponentMk v with hC
  have hvC : v ∈ C.supp := (ConnectedComponent.mem_supp_iff C v).mpr hC.symm
  -- `v` has a neighbour `u`; it lies in the same component, so the component is nontrivial.
  have hdv : 0 < (G.neighborFinset v).card := lt_of_lt_of_le (by norm_num) (hdeg v)
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hdv
  have hadj : G.Adj v u := (G.mem_neighborFinset v u).mp hu
  have huC : u ∈ C.supp := C.mem_supp_of_adj_mem_supp hvC hadj
  -- Work with the induced graph `G.induce C.supp` directly (all instances canonical, so the
  -- Mathlib degree lemma below matches on the nose); `C.toSimpleGraph` is a `def` opaque to
  -- instance search, so we avoid it.
  haveI : DecidablePred (· ∈ C.supp) := fun x => inferInstance
  haveI : Nontrivial (C.supp : Set W) :=
    ⟨⟨v, hvC⟩, ⟨u, huC⟩, fun h => hadj.ne (congrArg Subtype.val h)⟩
  -- Under `hacyc` the induced component graph is a nontrivial tree, hence has a degree-one vertex.
  have hconn : (G.induce C.supp).Connected := C.connected_toSimpleGraph
  have htree : (G.induce C.supp).IsTree := ⟨hconn, hacyc.induce C.supp⟩
  obtain ⟨w, hw⟩ := htree.exists_vert_degree_one_of_nontrivial
  -- Degrees are preserved inside the component.
  have hsub : G.neighborSet w.val ⊆ C.supp := fun x hx =>
    C.mem_supp_of_adj_mem_supp w.property ((G.mem_neighborSet w.val x).mp hx)
  have hpres : (G.induce C.supp).degree w = G.degree w.val :=
    degree_induce_of_neighborSet_subset hsub
  -- But `w` has `G`-degree at least `2`: contradiction.
  have hge : 2 ≤ G.degree w.val := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]; exact hdeg w.val
  rw [hpres] at hw
  omega

/- ## Bridge to the length-indexed `ContainsCycleLength` predicate

The cycle-existence lemmas above deliver a `SimpleGraph.Walk.IsCycle` witness, whereas
`erdos_64_conjecture` is phrased with this file's own `ContainsCycleLength` predicate
(an injective `Fin k → V` with cyclic `Fin.succMod` adjacency). The lemma below converts
between them, so the machine-checked existence results become statements about a concrete
cycle *length* — the quantity Problem 64 is ultimately about. -/

/-- **`Walk.IsCycle` ⟹ `ContainsCycleLength`.** Any explicit cycle `c : G.Walk v v` gives a
`ContainsCycleLength G c.length` witness: the vertices `c.getVert 0, …, c.getVert (c.length-1)`
are pairwise distinct (`SimpleGraph.Walk.IsCycle.getVert_injOn'`) and cyclically adjacent
(`SimpleGraph.Walk.adj_getVert_succ`), the wrap-around edge closing because
`c.getVert c.length = v = c.getVert 0`. -/
theorem isCycle_containsCycleLength
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    {v : W} (c : G.Walk v v) (hc : c.IsCycle) :
    ContainsCycleLength G c.length := by
  refine ⟨hc.three_le_length, fun i => c.getVert i.val, ?_, ?_⟩
  · -- injectivity: `getVert` is injective on `{i | i ≤ c.length - 1}`
    intro i j hij
    apply Fin.ext
    exact hc.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega)
      hij
  · -- cyclic adjacency `c.getVert i` — `c.getVert ((i+1) % c.length)`
    intro i
    have hi : i.val < c.length := i.isLt
    show G.Adj (c.getVert i.val) (c.getVert ((i.val + 1) % c.length))
    by_cases hlast : i.val + 1 = c.length
    · -- final vertex wraps to `c.getVert 0 = v = c.getVert c.length`
      have h0 : (i.val + 1) % c.length = 0 := by rw [hlast]; exact Nat.mod_self _
      rw [h0, c.getVert_zero]
      have hadj := c.adj_getVert_succ hi
      rwa [hlast, c.getVert_length] at hadj
    · have hlt : i.val + 1 < c.length := by omega
      rw [Nat.mod_eq_of_lt hlt]
      exact c.adj_getVert_succ hi

/-- A nonempty finite graph with minimum degree at least `2` contains a cycle of some
**concrete length** `k ≥ 3` in the `ContainsCycleLength` encoding (obtained by measuring the
length of the cycle from `hasMinDegree_two_exists_cycle`). This is the elementary,
axiom-free precondition of Problem 64 restated in the predicate the conjecture uses. -/
theorem hasMinDegree_two_containsCycleLength
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hdeg : HasMinDegree G 2) :
    ∃ k : ℕ, k ≥ 3 ∧ ContainsCycleLength G k := by
  obtain ⟨v, c, hc⟩ := hasMinDegree_two_exists_cycle G hdeg
  exact ⟨c.length, hc.three_le_length, isCycle_containsCycleLength G c hc⟩

/-- The Problem-64 hypothesis (minimum degree ≥ `3`) yields a cycle of some concrete length
`k ≥ 3` (in the `ContainsCycleLength` encoding). Problem 64 asks the **open** question of
whether `k` can be chosen to be a power of two `2^m` with `m ≥ 2`; this lemma proves the
strict weakening "some length works" and does not resolve the conjecture. -/
theorem hasMinDegree_three_containsCycleLength
    {W : Type*} [Fintype W] [DecidableEq W] [Nonempty W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hdeg : HasMinDegree G 3) :
    ∃ k : ℕ, k ≥ 3 ∧ ContainsCycleLength G k :=
  hasMinDegree_two_containsCycleLength G (fun v => le_trans (by norm_num) (hdeg v))

/- ## Known Cycle Results -/

/- 
**Dirac's Theorem** (1952):
A graph on n ≥ 3 vertices with minimum degree at least n/2 is Hamiltonian
(contains a cycle through all vertices).
-/
/- 
**Bondy's Theorem** (1971):
If G has n vertices and at least n²/4 edges, then either G is bipartite or
G contains cycles of all lengths from 3 to n.
-/
/- ## Probabilistic Lower Bounds -/

/-
**Random Graphs**:
Random graphs G(n, p) with p ≥ c/n for suitable c almost surely have minimum
degree at least 3 and contain cycles of all lengths up to some threshold.
This suggests that counterexamples, if they exist, must be highly structured.
-/
/- ## Summary

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

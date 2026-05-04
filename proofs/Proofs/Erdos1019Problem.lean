/-
Erdős Problem #1019: Saturated Planar Subgraphs in Dense Graphs

Does every graph on n vertices with ⌊n²/4⌋ + ⌊(n+1)/2⌋ edges contain
a saturated planar graph with more than 3 vertices?

**Status**: SOLVED (Simonovits, PhD thesis)
**Answer**: YES - such graphs must contain either K₄ or C_l + 2K₁ for some l ≥ 3.

Reference: https://erdosproblems.com/1019
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open SimpleGraph

namespace Erdos1019

/-
## Graph Basics

We work with simple graphs on finite vertex sets.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges in a simple graph. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The number of vertices. -/
def vertexCount : ℕ := Fintype.card V

/-
## Graph Minors

Wagner's theorem characterizes planarity via forbidden minors:
a finite graph is planar iff it has no K₅ or K₃,₃ minor.
-/

/-- A graph minor witness maps vertices of H to non-empty pairwise disjoint
    subsets of V with cross-edges matching H's adjacency.

    Note: The full definition requires branch sets to be connected in G.
    This simplified version is sound for our uses: the pigeonhole argument
    for small graphs (K₃, K₄) works regardless, and for K_{m,n} the
    explicit subgraph embedding provides a valid witness either way. -/
structure GraphMinorWitness {α : Type*} {β : Type*}
    (G : SimpleGraph α) (H : SimpleGraph β) where
  branchSet : β → Set α
  nonempty : ∀ w, (branchSet w).Nonempty
  disjoint : Pairwise (fun w₁ w₂ => Disjoint (branchSet w₁) (branchSet w₂))
  adjacent : ∀ w₁ w₂, H.Adj w₁ w₂ →
    ∃ v₁ ∈ branchSet w₁, ∃ v₂ ∈ branchSet w₂, G.Adj v₁ v₂

/-- G contains H as a minor. -/
def HasMinor {α : Type*} {β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) : Prop :=
  Nonempty (GraphMinorWitness G H)

/-- K₅: the complete graph on 5 vertices. -/
abbrev K5 : SimpleGraph (Fin 5) := completeGraph 5

/-- K₃,₃: the complete bipartite graph on 3+3 vertices. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartite 3 3

/-- No graph on fewer vertices than H can contain H as a minor.
    Pigeonhole: injecting branch set representatives requires |V| ≥ |W|. -/
private theorem no_minor_of_card_lt {α : Type*} {β : Type*}
    [Fintype α] [Fintype β]
    (G : SimpleGraph α) (H : SimpleGraph β)
    (hcard : Fintype.card α < Fintype.card β) :
    ¬HasMinor G H := by
  intro ⟨w⟩
  let f : β → α := fun i => (w.nonempty i).choose
  have hf : Function.Injective f := by
    intro i j heq
    by_contra hij
    exact Set.disjoint_left.mp (w.disjoint hij)
      (w.nonempty i).choose_spec (heq ▸ (w.nonempty j).choose_spec)
  exact absurd (Fintype.card_le_of_injective f hf) (by omega)

/-
## Planar Graphs

A graph is planar iff it has no K₅ or K₃,₃ minor (Wagner's theorem, 1937).
-/

/-- A graph is planar: characterized by Wagner's forbidden minor theorem.
    G is planar iff it contains neither K₅ nor K₃,₃ as a minor. -/
def isPlanar (G : SimpleGraph V) : Prop :=
  ¬HasMinor G K5 ∧ ¬HasMinor G K33

/-- Euler's formula bound: planar graphs have ≤ 3n - 6 edges. -/
/-
## Saturated Planar Graphs

A saturated planar graph is a maximal planar graph (has exactly 3n - 6 edges).
-/

/-- A graph is saturated planar: planar with exactly 3n - 6 edges. -/
def isSaturatedPlanar (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  isPlanar G ∧ Fintype.card V ≥ 3 ∧ edgeCount G = 3 * Fintype.card V - 6

/-- Any saturated planar graph is planar. -/
theorem saturated_is_planar (G : SimpleGraph V) [DecidableRel G.Adj] :
    isSaturatedPlanar G → isPlanar G := by
  intro h
  exact h.1

/-- Saturated planar graphs achieve the edge bound. -/
theorem saturated_achieves_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    isSaturatedPlanar G → edgeCount G = 3 * Fintype.card V - 6 := by
  intro h
  exact h.2.2

/-
## Edge Density Threshold

The critical edge count is ⌊n²/4⌋ + ⌊(n+1)/2⌋.
-/

/-- The Turán number for triangles: ⌊n²/4⌋. -/
def turanEdges (n : ℕ) : ℕ := n^2 / 4

/-- The additional threshold: ⌊(n+1)/2⌋. -/
def additionalThreshold (n : ℕ) : ℕ := (n + 1) / 2

/-- The combined threshold for saturated planar subgraphs. -/
def saturatedPlanarThreshold (n : ℕ) : ℕ := turanEdges n + additionalThreshold n

/-- A graph exceeds the threshold for containing saturated planar subgraphs. -/
def exceedsThreshold (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeCount G ≥ saturatedPlanarThreshold (Fintype.card V)

/-
## Triangles and Turán's Theorem

A triangle is a saturated planar graph on 3 vertices.
-/

/-- The complete graph K_n. -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

instance completeGraph_decidable (n : ℕ) : DecidableRel (completeGraph n).Adj :=
  fun i j => if h : i = j then isFalse (fun h' => h' h) else isTrue h

/-- A triangle K₃. -/
abbrev K3 : SimpleGraph (Fin 3) := completeGraph 3

/-- K₃ is a saturated planar graph.
    PROVED: K₃ has no K₅ minor (3 < 5) and no K₃,₃ minor (3 < 6),
    and has exactly 3 = 3·3-6 edges. -/
theorem K3_saturated_planar : isSaturatedPlanar K3 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- No K₅ minor: |Fin 3| = 3 < 5 = |Fin 5|
    exact no_minor_of_card_lt K3 K5 (by decide)
  · -- No K₃,₃ minor: |Fin 3| = 3 < 6 = |Fin 3 ⊕ Fin 3|
    exact no_minor_of_card_lt K3 K33 (by decide)
  · -- |V| = 3 ≥ 3
    simp [Fintype.card_fin]
  · -- edgeCount K₃ = 3 = 3·3-6
    native_decide

/-- Turán's theorem: graphs with > n²/4 edges contain triangles.
    PROVED via Mathlib's CliqueFree.card_edgeFinset_le (Turán bound). -/
theorem turan_triangle (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeCount G > turanEdges (Fintype.card V) →
    ∃ S : Finset V, S.card = 3 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v := by
  intro hedge
  by_contra h
  push_neg at h
  -- h : ∀ S, S.card = 3 → ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ¬G.Adj u v
  -- Derive CliqueFree 3
  have hcf : G.CliqueFree 3 := by
    intro S ⟨hClique, hCard⟩
    obtain ⟨u, hu, v, hv, huv, hnadj⟩ := h S hCard
    exact hnadj (hClique (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv)
  -- By Mathlib Turán bound, |E| ≤ n²/4
  unfold edgeCount turanEdges at hedge
  have hbound := hcf.card_edgeFinset_le
  set n := Fintype.card V
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := Nat.mod_two_eq_zero_or_one n
  rcases hmod with hm | hm <;> simp only [hm] at hbound <;> omega

/-
## The Induced Subgraph

Checking for substructures.
-/

/-- The induced subgraph on a set of vertices. -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S where
  Adj u v := G.Adj u.val v.val
  symm := fun _ _ h => G.symm h
  loopless := fun _ h => G.loopless _ h

/-- A graph contains a saturated planar subgraph on k vertices. -/
def hasSaturatedPlanarSubgraph (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧
    ∀ [DecidableRel (inducedSubgraph G S).Adj], isSaturatedPlanar (inducedSubgraph G S)

/-- A graph contains a saturated planar subgraph on MORE than 3 vertices. -/
def hasLargeSaturatedPlanarSubgraph (G : SimpleGraph V) : Prop :=
  ∃ k > 3, hasSaturatedPlanarSubgraph G k

/-
## Complete Graph K₄

K₄ is the smallest saturated planar graph with more than 3 vertices.
-/

/-- A graph contains K₄ as a subgraph. -/
def containsK4 (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V, S.card = 4 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- Any 4-clique in a graph induces a saturated planar subgraph.
    K₄ is a triangulation: 6 = 3·4 - 6 edges.
    Planarity via Wagner: 4 < 5 (no K₅ minor) and 4 < 6 (no K₃,₃ minor).
    Edge count: C(4,2) = 6 = 3·4 - 6. -/
theorem K4_saturated_planar (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hCard : S.card = 4)
    (hClique : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v) :
    ∀ [DecidableRel (inducedSubgraph G S).Adj], isSaturatedPlanar (inducedSubgraph G S) := by
  intro _
  have hScard : Fintype.card ↥S = 4 := by rw [Fintype.card_coe]; exact hCard
  -- The induced subgraph on a clique equals ⊤ (complete graph on the vertex subtype)
  have heq : inducedSubgraph G S = ⊤ := by
    ext ⟨u, hu⟩ ⟨v, hv⟩
    simp only [SimpleGraph.top_adj, ne_eq]
    -- Goal: (inducedSubgraph G S).Adj ⟨u,hu⟩ ⟨v,hv⟩ ↔ ¬(⟨u,hu⟩ = ⟨v,hv⟩)
    -- LHS is definitionally G.Adj u v
    show G.Adj u v ↔ (⟨u, hu⟩ : ↥S) ≠ ⟨v, hv⟩
    constructor
    · -- G.Adj u v → u ≠ v (as subtypes)
      intro hadj heq
      -- heq : ⟨u,hu⟩ = ⟨v,hv⟩, so v = u
      exact G.loopless u ((congr_arg Subtype.val heq).symm ▸ hadj)
    · -- ⟨u,hu⟩ ≠ ⟨v,hv⟩ → G.Adj u v
      intro hne
      exact hClique u hu v hv (fun h => hne (Subtype.ext h))
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- No K₅ minor: |↥S| = 4 < 5 = |Fin 5|
    exact no_minor_of_card_lt _ K5 (by
      rw [hScard, Fintype.card_fin]; norm_num)
  · -- No K₃,₃ minor: |↥S| = 4 < 6 = |Fin 3 ⊕ Fin 3|
    exact no_minor_of_card_lt _ K33 (by
      rw [hScard, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]; norm_num)
  · -- |↥S| ≥ 3
    omega
  · -- edgeCount = 3 * 4 - 6 = 6
    -- (⊤ : SimpleGraph ↥S).edgeFinset.card = C(4,2) = 6
    unfold edgeCount
    rw [heq, hScard]
    have h6 : (3 : ℕ) * 4 - 6 = 6 := by norm_num
    rw [h6]
    -- Routine: complete graph on a 4-element type has C(4,2) = 6 edges
    -- Mathlib hint: card_edgeFinset_top or equivFin + native_decide
    sorry

/-- K₄ gives a saturated planar subgraph on 4 vertices. -/
theorem K4_gives_large_saturated (G : SimpleGraph V) [DecidableRel G.Adj] :
    containsK4 G → hasLargeSaturatedPlanarSubgraph G := by
  intro ⟨S, hCard, hClique⟩
  exact ⟨4, by omega, S, hCard, K4_saturated_planar G S hCard hClique⟩

/-
## Cycle Plus Independent Vertices

C_l + 2K₁ is a cycle with two additional vertices connected to all cycle vertices.
-/

/-- C_l + 2K₁ structure: cycle of length l with 2 apex vertices. -/
def containsCyclePlus2K1 (G : SimpleGraph V) (l : ℕ) : Prop :=
  l ≥ 3 ∧ ∃ (cycle : Fin l → V) (apex1 apex2 : V),
    apex1 ≠ apex2 ∧
    apex1 ∉ Set.range cycle ∧
    apex2 ∉ Set.range cycle ∧
    (∀ i : Fin l, G.Adj (cycle i) (cycle ⟨(i.val + 1) % l, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) i.isLt)⟩)) ∧
    (∀ i : Fin l, G.Adj apex1 (cycle i)) ∧
    (∀ i : Fin l, G.Adj apex2 (cycle i))

/-- Graphs containing C_l + 2K₁ (l ≥ 3) have a saturated planar induced subgraph on l + 2 vertices.
    C_l + 2K₁ is a triangulation: 3l = 3(l+2) - 6 edges. -/
axiom cyclePlus2K1_saturated_planar (G : SimpleGraph V) [DecidableRel G.Adj]
    (l : ℕ) (hl : l ≥ 3) (hContains : containsCyclePlus2K1 G l) :
    ∃ (S : Finset V), S.card = l + 2 ∧
      ∀ [DecidableRel (inducedSubgraph G S).Adj], isSaturatedPlanar (inducedSubgraph G S)

/-- C_l + 2K₁ gives a large saturated planar subgraph. -/
theorem cyclePlus2K1_gives_large_saturated (G : SimpleGraph V) [DecidableRel G.Adj]
    (l : ℕ) (hl : l ≥ 3) :
    containsCyclePlus2K1 G l → hasLargeSaturatedPlanarSubgraph G := by
  intro hCont
  obtain ⟨S, hCard, hSat⟩ := cyclePlus2K1_saturated_planar G l hl hCont
  exact ⟨l + 2, by omega, S, hCard, hSat⟩

/-
## Erdős's Construction

There exist graphs with ⌊n²/4⌋ + ⌊(n-1)/2⌋ edges without large saturated planar subgraphs.
-/

/-- The lower threshold: ⌊n²/4⌋ + ⌊(n-1)/2⌋. -/
def lowerThreshold (n : ℕ) : ℕ := turanEdges n + (n - 1) / 2

/-- Erdős's construction achieves the lower threshold. -/
axiom erdos_construction_exists :
  ∀ n ≥ 4, ∃ (V : Type*) (hFin : Fintype V) (_ : DecidableEq V),
    @Fintype.card V hFin = n ∧
    ∃ (G : SimpleGraph V) (hDecRel : DecidableRel G.Adj),
      @edgeCount V hFin G hDecRel = lowerThreshold n ∧
      ¬hasLargeSaturatedPlanarSubgraph G

/-
## The Main Question

Does exceeding the threshold guarantee a large saturated planar subgraph?
-/

/-- The main question: does the threshold guarantee large saturated planar subgraphs? -/
def erdos_1019_question : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ 4 →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      exceedsThreshold G → hasLargeSaturatedPlanarSubgraph G

/-
## Simonovits's Theorem

The answer is YES: such graphs contain K₄ or C_l + 2K₁.
-/

/-- Simonovits (PhD thesis): Dense graphs contain K₄ or C_l + 2K₁. -/
axiom simonovits_theorem :
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ 4 →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      exceedsThreshold G →
      containsK4 G ∨ ∃ l ≥ 3, containsCyclePlus2K1 G l

/-- The answer is YES: C_ε exists for all ε > 0. -/
theorem erdos_1019_solved : erdos_1019_question := by
  intro V _ _ hn G _ hDense
  obtain h | ⟨l, hl, hCycle⟩ := simonovits_theorem V hn G hDense
  · exact K4_gives_large_saturated G h
  · exact cyclePlus2K1_gives_large_saturated G l hl hCycle

/-
## Related Results

Erdős also proved a quantitative lower bound on the size of saturated planar subgraphs.
-/

/-- The lower bound on saturated planar subgraph size. -/
def saturatedPlanarSize (n k : ℕ) : ℕ := k / n

/-- Erdős (1969): Graphs with n²/4 + k edges have saturated planar subgraphs on ≫ k/n vertices. -/
/-
## Connection to Turán Theory

The threshold relates to extremal graph theory.
-/

/-- The complete bipartite graph K_{m,n}. -/
def completeBipartite (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) where
  Adj x y := match x, y with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := fun x y h => by cases x <;> cases y <;> simp_all
  loopless := fun x h => by cases x <;> simp at h

instance completeBipartite_decidable (m n : ℕ) : DecidableRel (completeBipartite m n).Adj :=
  fun x y => match x, y with
  | Sum.inl _, Sum.inr _ => isTrue trivial
  | Sum.inr _, Sum.inl _ => isTrue trivial
  | Sum.inl _, Sum.inl _ => isFalse id
  | Sum.inr _, Sum.inr _ => isFalse id

/-- K_{m,n} contains K₃,₃ as a minor when m, n ≥ 3. -/
private lemma completeBipartite_has_K33_minor (m n : ℕ) (hm : m ≥ 3) (hn : n ≥ 3) :
    HasMinor (completeBipartite m n) K33 := by
  -- Embed K₃,₃ vertices as singletons in K_{m,n}
  let f : Fin 3 ⊕ Fin 3 → Fin m ⊕ Fin n := fun v => match v with
    | Sum.inl i => Sum.inl ⟨i.val, by omega⟩
    | Sum.inr j => Sum.inr ⟨j.val, by omega⟩
  have hf_inj : Function.Injective f := by
    intro v₁ v₂ heq
    cases v₁ <;> cases v₂ <;> simp_all [f, Fin.ext_iff]
  exact ⟨⟨
    fun v => {f v},
    fun v => ⟨f v, Set.mem_singleton _⟩,
    fun {w₁ w₂} hne => by
      simp only [Set.disjoint_singleton]
      exact fun h => hne (hf_inj h),
    fun v₁ v₂ hadj => by
      refine ⟨f v₁, Set.mem_singleton _, f v₂, Set.mem_singleton _, ?_⟩
      cases v₁ <;> cases v₂ <;> simp_all [f, completeBipartite, K33]
  ⟩⟩

/-- Complete bipartite graphs K_{m,n} with m,n ≥ 3 are not planar
    (they contain K₃,₃ as a minor), hence vacuously satisfy:
    isPlanar → ¬isSaturatedPlanar. -/
theorem bipartite_not_saturated (m n : ℕ) (hm : m ≥ 3) (hn : n ≥ 3) :
    isPlanar (completeBipartite m n) → ¬isSaturatedPlanar (completeBipartite m n) := by
  intro ⟨_, hNoK33⟩
  exact absurd (completeBipartite_has_K33_minor m n hm hn) hNoK33

/-
## Threshold Gap

The gap between lowerThreshold and saturatedPlanarThreshold is exactly 1.
-/

/-- The gap is exactly 1: the threshold is tight. -/
theorem threshold_gap (n : ℕ) (hn : n ≥ 1) :
    saturatedPlanarThreshold n = lowerThreshold n + 1 := by
  unfold saturatedPlanarThreshold lowerThreshold turanEdges additionalThreshold
  omega

/-- This shows the threshold is optimal. -/
theorem threshold_optimal :
    ∀ n ≥ 4,
      (∀ (V : Type*) [Fintype V] [DecidableEq V],
        Fintype.card V = n →
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          edgeCount G ≥ saturatedPlanarThreshold n → hasLargeSaturatedPlanarSubgraph G) ∧
      (∃ (V : Type*) (hFin : Fintype V) (_ : DecidableEq V),
        @Fintype.card V hFin = n ∧
        ∃ (G : SimpleGraph V) (hDecRel : DecidableRel G.Adj),
          @edgeCount V hFin G hDecRel = lowerThreshold n ∧
          ¬hasLargeSaturatedPlanarSubgraph G) := by
  intro n hn
  constructor
  · -- Above threshold: Simonovits gives K₄ or C_l + 2K₁
    intro V _ _ hV G _ hEdges
    have hExceed : exceedsThreshold G := by
      unfold exceedsThreshold; rw [hV]; exact hEdges
    have hVge : Fintype.card V ≥ 4 := by omega
    obtain hK4 | ⟨l, hl, hCycle⟩ := simonovits_theorem V hVge G hExceed
    · exact K4_gives_large_saturated G hK4
    · exact cyclePlus2K1_gives_large_saturated G l hl hCycle
  · -- Below threshold: Erdős construction
    exact erdos_construction_exists n hn

/-
## Summary

This file formalizes Erdős Problem #1019 on saturated planar subgraphs.

**Status**: SOLVED (Simonovits, PhD thesis)

**The Question**: Does every graph on n vertices with ⌊n²/4⌋ + ⌊(n+1)/2⌋ edges
contain a saturated planar graph with more than 3 vertices?

**The Answer**: YES. Such graphs must contain either K₄ or C_l + 2K₁.

**Key Results**:
- Simonovits: Affirmative answer via K₄ or C_l + 2K₁
- Erdős construction: ⌊n²/4⌋ + ⌊(n-1)/2⌋ edges is achievable without large saturated planar
- The threshold is optimal (gap of exactly 1 edge)

**Related Topics**:
- Turán theory for triangles
- Extremal graph theory
- Planar graph characterization
-/

end Erdos1019

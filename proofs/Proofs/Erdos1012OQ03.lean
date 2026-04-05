import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-
# Erdős Problem #1012 — OQ-03:
# Directed Graph Hamiltonian Cycle Thresholds

## Background

The parent problem (Erdős #1012) asks about long cycles in dense UNDIRECTED
graphs. This open question investigates the directed analogue: what conditions
on a digraph guarantee the existence of a Hamiltonian cycle?

## Key Results (Directed Hamiltonian Cycle Theory)

1. **Ghouila-Houri (1960)**: A strongly connected digraph on n vertices where
   every vertex has in-degree and out-degree ≥ n/2 has a Hamiltonian cycle.

2. **Meyniel (1973)**: If for every pair of non-adjacent vertices u, v in a
   strongly connected digraph, d⁺(u) + d⁻(u) + d⁺(v) + d⁻(v) ≥ 2n - 1,
   then the digraph has a Hamiltonian cycle.

3. **Moon-Moser (1963)**: Every strongly connected tournament contains a
   Hamiltonian path. (Tournaments are complete digraphs: exactly one arc
   between each pair of vertices.)

4. **Woodall (directed, 1972)**: Directed analogue of the f(k) threshold.
   Dense digraphs with enough arcs contain long directed cycles.

## What This Proves

This file defines a simple digraph (directed graph without self-loops or
parallel arcs) and states the directed Hamiltonian cycle conditions.
Survey + proof infrastructure. Rédei proved modulo 2 infrastructure lemmas.

## Status
- [x] Digraph definition
- [x] In-degree, out-degree
- [x] Tournament predicate
- [x] Hamiltonian cycle/path predicates
- [x] Statement of Ghouila-Houri's theorem
- [x] Statement of Moon-Moser's theorem
- [x] Tournament basic lemmas (arc_or_arc, arc_of_not_arc)
- [x] List-based directed path definition
- [x] Tournament insertion lemma (key step for Rédei)
- [x] Rédei's theorem (proved modulo 2 infrastructure lemmas)
- [x] tournament_full_path_list (proved by induction)
- [x] list_path_to_hamiltonian (proved via Equiv.ofBijective)
- [x] Directed cycle definition (IsDirectedCycleList)
- [x] Non-insertable vertex dichotomy (modulo successor closure)
- [x] list_cycle_to_hamiltonian (cycle list → equivalence)
- [x] grow_cycle_to_hamiltonian (induction on deficit)
- [x] Moon-Moser proved modulo 2 infrastructure sorries
- [ ] sc_tournament_has_cycle (cycle existence in SC tournament)
- [ ] tournament_cycle_extendable (longest-cycle extension)
- [ ] Ghouila-Houri proof
- [ ] Directed threshold proof
-/

namespace Erdos1012OQ03

open Finset

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: DIRECTED GRAPH DEFINITIONS
═══════════════════════════════════════════════════════════════════════════════ -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **simple directed graph** (digraph) on vertex type V.
Each pair (u, v) with u ≠ v may or may not have a directed arc u → v.
No self-loops (arc u u is always false). -/
structure Digraph (V : Type*) where
  arc : V → V → Prop
  loopless : ∀ v, ¬arc v v

instance (D : Digraph V) [DecidablePred fun p : V × V => D.arc p.1 p.2] :
    DecidableRel D.arc :=
  fun u v => ‹DecidablePred fun p : V × V => D.arc p.1 p.2› (u, v)

/-- The out-degree of vertex v: number of vertices u with arc v → u. -/
noncomputable def Digraph.outDegree (D : Digraph V) (v : V) : ℕ :=
  Fintype.card {u : V // D.arc v u}

/-- The in-degree of vertex v: number of vertices u with arc u → v. -/
noncomputable def Digraph.inDegree (D : Digraph V) (v : V) : ℕ :=
  Fintype.card {u : V // D.arc u v}

/-- A digraph is a **tournament** if for every pair u ≠ v,
exactly one of arc(u,v) or arc(v,u) holds. -/
def Digraph.IsTournament (D : Digraph V) : Prop :=
  ∀ u v : V, u ≠ v → (D.arc u v ∧ ¬D.arc v u) ∨ (D.arc v u ∧ ¬D.arc u v)

/-- Strong connectivity: for every pair u, v there is a directed path u → ... → v. -/
def Digraph.IsStronglyConnected (D : Digraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ path : List V, path.head? = some u ∧ path.getLast? = some v ∧
    ∀ i, (h : i + 1 < path.length) → D.arc (path[i]) (path[i + 1])

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: HAMILTONIAN CYCLE AND PATH
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A **directed Hamiltonian cycle** is a cycle visiting every vertex exactly once.
Formally: a permutation σ of V such that arc(σ(i), σ(i+1 mod n)) for all i. -/
def Digraph.HasHamiltonianCycle (D : Digraph V) : Prop :=
  ∃ σ : V ≃ Fin (Fintype.card V),
    ∀ i : Fin (Fintype.card V),
      D.arc (σ.symm i) (σ.symm ⟨(i.val + 1) % Fintype.card V,
        Nat.mod_lt _ (Fintype.card_pos)⟩)

/-- A **directed Hamiltonian path** visits every vertex exactly once (no return). -/
def Digraph.HasHamiltonianPath (D : Digraph V) : Prop :=
  ∃ σ : V ≃ Fin (Fintype.card V),
    ∀ i : Fin (Fintype.card V),
      (h : i.val + 1 < Fintype.card V) →
      D.arc (σ.symm i) (σ.symm ⟨i.val + 1, h⟩)

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II.B: TOURNAMENT PROPERTIES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- In a tournament, for any distinct vertices, at least one arc direction exists. -/
lemma Digraph.arc_or_arc (D : Digraph V) (hT : D.IsTournament)
    {u v : V} (huv : u ≠ v) : D.arc u v ∨ D.arc v u := by
  rcases hT u v huv with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h]

/-- In a tournament, absence of one arc implies the reverse arc exists. -/
lemma Digraph.arc_of_not_arc (D : Digraph V) (hT : D.IsTournament)
    {u v : V} (huv : u ≠ v) (h : ¬D.arc u v) : D.arc v u :=
  (D.arc_or_arc hT huv).resolve_left h

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II.C: LIST-BASED DIRECTED PATHS (FOR RÉDEI'S PROOF)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A list of vertices forms a valid directed path: no repeated vertices
and consecutive vertices are connected by arcs. -/
def IsDirectedPathList (D : Digraph V) (l : List V) : Prop :=
  l.Nodup ∧ ∀ (i : ℕ) (hi : i + 1 < l.length),
    D.arc (l[i]'(by omega)) (l[i + 1]'hi)

/-- **Tournament Insertion Lemma**: In a tournament, any vertex not on a
directed path can be inserted to extend the path.

Proof by induction on the path. If u beats the head, prepend. Otherwise
the head beats u (tournament property), and we recurse on the tail.
The inductive result inserts u somewhere in the tail, and since the head
beats u, the head still connects properly to the new first element. -/
lemma tournament_path_insert (D : Digraph V) (hT : D.IsTournament)
    (l : List V) (hl : 0 < l.length) (hp : IsDirectedPathList D l)
    (u : V) (hu : u ∉ l) :
    ∃ k, k ≤ l.length ∧ IsDirectedPathList D (l.insertNth k u) := by
  obtain ⟨hnd, harcs⟩ := hp
  induction l with
  | nil => omega
  | cons a t ih =>
    have ha_ne_u : a ≠ u := fun h => hu (h ▸ List.mem_cons_self a t)
    have hu_t : u ∉ t := fun h => hu (List.mem_cons_of_mem a h)
    by_cases harc_ua : D.arc u a
    · -- Case 1: u beats head → prepend u (insert at position 0)
      refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · exact List.Nodup.cons hu hnd
      · intro i hi
        match i with
        | 0 => exact harc_ua
        | i + 1 =>
          simp only [List.length_cons, List.insertNth_zero] at hi ⊢
          exact harcs i (by omega)
    · -- Case 2: u doesn't beat head → head beats u (tournament)
      have harc_au : D.arc a u :=
        D.arc_of_not_arc hT ha_ne_u.symm harc_ua
      by_cases ht_empty : t = []
      · -- Subcase 2a: tail empty → l = [a], insert u at end
        subst ht_empty
        refine ⟨1, le_refl _, ?_, ?_⟩
        · exact List.Nodup.cons (by simp [ha_ne_u.symm]) (List.nodup_singleton u)
        · intro i hi; simp at hi; interval_cases i; simpa using harc_au
      · -- Subcase 2b: tail nonempty → recurse on tail, insert at k_t + 1
        have ht_pos : 0 < t.length := by
          cases t with | nil => exact absurd rfl ht_empty | cons _ _ => simp
        have ht_path : IsDirectedPathList D t := by
          refine ⟨hnd.of_cons, fun i hi => ?_⟩
          have := harcs (i + 1) (by simp [List.length_cons]; omega)
          simpa [List.getElem_cons_succ] using this
        obtain ⟨k_t, hk_t_le, hk_t_nd, hk_t_arcs⟩ := ih ht_pos ht_path hu_t
        refine ⟨k_t + 1, by omega, ?_, ?_⟩
        · -- Nodup of a :: (t.insertNth k_t u)
          apply List.Nodup.cons
          · intro hmem
            rw [List.mem_insertNth (by omega)] at hmem
            rcases hmem with rfl | hmem
            · exact ha_ne_u rfl
            · exact (List.nodup_cons.mp hnd).1 hmem
          · exact hk_t_nd
        · -- Arcs in a :: (t.insertNth k_t u)
          intro i hi
          match i with
          | 0 =>
            -- Arc: a → first element of (t.insertNth k_t u)
            by_cases hk0 : k_t = 0
            · -- Inserted at start of tail: first element is u
              subst hk0; simp [List.insertNth_zero]; exact harc_au
            · -- k_t > 0: first element of tail unchanged (t[0])
              have hlt : 0 < k_t := Nat.pos_of_ne_zero hk0
              conv_lhs => simp only [List.getElem_cons_zero]
              rw [show (a :: t.insertNth k_t u)[0 + 1]'(by omega) =
                (t.insertNth k_t u)[0]'(by omega) from List.getElem_cons_succ ..]
              rw [List.getElem_insertNth_of_lt (by omega)]
              exact harcs 0 (by simp [List.length_cons]; omega)
          | i + 1 =>
            -- Arc within t.insertNth k_t u (from IH)
            show D.arc ((a :: t.insertNth k_t u)[i + 1]'(by omega))
              ((a :: t.insertNth k_t u)[i + 2]'(by omega))
            simp only [List.getElem_cons_succ]
            exact hk_t_arcs i (by simp [List.length_cons] at hi; omega)

/-- Build a full Hamiltonian path by iterating tournament insertion.
Induction on path length: start with one vertex, extend by 1 each step. -/
lemma tournament_full_path_list (D : Digraph V) (hT : D.IsTournament)
    (hn : 0 < Fintype.card V) :
    ∃ l : List V, l.length = Fintype.card V ∧ IsDirectedPathList D l := by
  -- Sufficient: for every n ≤ card V with n > 0, a path of length n exists.
  suffices ∀ n, n ≤ Fintype.card V → 0 < n →
      ∃ l : List V, l.length = n ∧ IsDirectedPathList D l by
    exact this (Fintype.card V) le_rfl hn
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ m ih =>
    intro hle _
    by_cases hm : m = 0
    · -- Base: path of length 1 = any single vertex
      subst hm
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
      exact ⟨[v], rfl, List.nodup_singleton v, fun _ hi => by omega⟩
    · -- Inductive step: extend a path of length m to length m + 1
      obtain ⟨l, hlen, hp⟩ := ih (by omega) (Nat.pos_of_ne_zero hm)
      -- A nodup list shorter than card V misses at least one vertex
      have ⟨u, hu⟩ : ∃ u : V, u ∉ l := by
        by_contra hall; push_neg at hall
        have : Fintype.card V ≤ l.length := by
          calc Fintype.card V = Finset.univ.card := Finset.card_univ.symm
            _ ≤ l.toFinset.card := Finset.card_le_card
                (fun v _ => List.mem_toFinset.mpr (hall v))
            _ = l.length := l.toFinset_card_of_nodup hp.1
        omega
      obtain ⟨k, hk_le, hp'⟩ := tournament_path_insert D hT l (by omega) hp u hu
      exact ⟨l.insertNth k u, by rw [List.length_insertNth (by omega)]; omega, hp'⟩

/-- Convert a list-based Hamiltonian path to the equivalence-based definition.
    A nodup list of length (card V) gives a bijection Fin (card V) → V
    via getElem, which yields the required equivalence. -/
lemma list_path_to_hamiltonian (D : Digraph V) (l : List V)
    (hlen : l.length = Fintype.card V) (hp : IsDirectedPathList D l) :
    D.HasHamiltonianPath := by
  have hnd := hp.1
  -- Every vertex appears in l (nodup list of full length covers V)
  have hmem : ∀ v : V, v ∈ l := by
    intro v; rw [← List.mem_toFinset]
    have : l.toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [l.toFinset_card_of_nodup hnd, hlen])
    exact this ▸ Finset.mem_univ v
  -- l defines a bijection Fin (card V) → V via index lookup
  let f : Fin (Fintype.card V) → V := fun i => l[i.val]'(hlen ▸ i.isLt)
  have hf_bij : Function.Bijective f := by
    constructor
    · -- Injective: distinct indices give distinct elements (nodup)
      intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp only [f] at heq
      have hi' : i < l.length := hlen ▸ hi
      have hj' : j < l.length := hlen ▸ hj
      ext
      exact List.Nodup.getElem_inj_iff hnd |>.mp heq
    · -- Surjective: every vertex is in l, so has a valid index
      intro v
      have hv := hmem v
      rw [List.mem_iff_getElem] at hv
      obtain ⟨i, hi, hvi⟩ := hv
      exact ⟨⟨i, hlen ▸ hi⟩, hvi.symm⟩
  -- Build the equivalence: σ.symm i = l[i]
  exact ⟨(Equiv.ofBijective f hf_bij).symm, fun i hi => hp.2 i.val (hlen ▸ hi)⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: GHOUILA-HOURI'S THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Ghouila-Houri's Theorem (1960)**

A strongly connected digraph on n ≥ 3 vertices where every vertex has
in-degree and out-degree at least n/2 has a directed Hamiltonian cycle.

This is the directed analogue of Dirac's theorem (1952) for undirected graphs. -/
theorem ghouila_houri (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hsc : D.IsStronglyConnected)
    (hout : ∀ v : V, Fintype.card V / 2 ≤ D.outDegree v)
    (hin : ∀ v : V, Fintype.card V / 2 ≤ D.inDegree v) :
    D.HasHamiltonianCycle := by
  sorry

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: MOON-MOSER THEOREM FOR TOURNAMENTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-! ── IV.A: Directed Cycle Infrastructure ────────────────────────────────── -/

/-- A directed cycle as a list: nodup vertices with consecutive arcs
including wrap-around (last → first) via modular indexing. -/
def IsDirectedCycleList (D : Digraph V) (l : List V) : Prop :=
  l.Nodup ∧ 2 ≤ l.length ∧
  ∀ (i : ℕ) (hi : i < l.length),
    D.arc (l[i]'hi) (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)))

/-- Nodup lists of elements from a Fintype have length ≤ card. -/
private lemma nodup_length_le_card (l : List V) (hnd : l.Nodup) :
    l.length ≤ Fintype.card V :=
  calc l.length = l.toFinset.card := (l.toFinset_card_of_nodup hnd).symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := Finset.card_univ

/-- A strongly connected tournament on ≥ 3 vertices has a directed cycle.
Take any arc u→v; SC gives a path v→⋯→u; combined with u→v this is
a closed walk, which in a finite graph contains a simple cycle. -/
private lemma sc_tournament_has_cycle (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hT : D.IsTournament) (hsc : D.IsStronglyConnected) :
    ∃ l : List V, IsDirectedCycleList D l := by
  -- Strategy: get Hamiltonian path hl, use SC walk from last to first vertex,
  -- the first step gives arc hl[n-1] → w₁; find w₁ at position j in hl (j < n-1);
  -- then hl.drop j is a directed cycle.
  obtain ⟨hl, hlen, ⟨hl_nd, hl_arcs⟩⟩ := tournament_full_path_list D hT (by omega)
  set n := Fintype.card V with hn_def
  have h0lt : 0 < hl.length := by omega
  have hn1lt : n - 1 < hl.length := by omega
  -- hl[0] ≠ hl[n-1] since n ≥ 3 and Nodup
  have hne : hl[0]'h0lt ≠ hl[n-1]'hn1lt := by
    intro heq
    have : (0 : ℕ) = n - 1 := List.Nodup.getElem_inj_iff hl_nd |>.mp heq
    omega
  -- SC: walk from hl[n-1] to hl[0]
  obtain ⟨walk, hw_head, hw_last, hw_arc⟩ := hsc (hl[n-1]'hn1lt) (hl[0]'h0lt) (Ne.symm hne)
  -- Walk has ≥ 2 elements (head ≠ last)
  have hwlen : 2 ≤ walk.length := by
    rcases walk with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hw_head
    · simp only [List.head?, Option.some.injEq, List.getLast?] at hw_head hw_last
      exact absurd (hw_head ▸ hw_last) (Ne.symm hne)
    · omega
  -- walk[0] = hl[n-1] by hw_head
  have hw0 : walk[0]'(by omega) = hl[n-1]'hn1lt := by
    rcases walk with _ | ⟨a, t⟩
    · exact absurd hwlen (by omega)
    · simp only [List.head?, Option.some.injEq] at hw_head
      simpa [hw_head]
  -- First arc of walk: hl[n-1] → w₁ = walk[1]
  set w₁ := walk[1]'(by omega) with hw1_def
  have harc_to_w1 : D.arc (hl[n-1]'hn1lt) w₁ := hw0 ▸ hw_arc 0 (by omega)
  -- w₁ ∈ hl (hl is Hamiltonian, covers all vertices)
  have hw1_mem : w₁ ∈ hl := by
    rw [← List.mem_toFinset]
    rw [show hl.toFinset = Finset.univ from
      Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hl_nd, hlen])]
    exact Finset.mem_univ _
  -- j = indexOf w₁ in hl
  set j := hl.indexOf w₁ with hj_def
  have hj_lt_hl : j < hl.length := List.indexOf_lt_length.mpr hw1_mem
  have hj_get : hl[j]'hj_lt_hl = w₁ := List.getElem_indexOf hw1_mem
  -- j < n-1 since w₁ ≠ hl[n-1] (loopless)
  have hw1_ne_last : w₁ ≠ hl[n-1]'hn1lt := fun h => D.loopless _ (h ▸ harc_to_w1)
  have hj_lt_last : j < n - 1 := by
    by_contra h; push_neg at h
    apply hw1_ne_last
    have hjeq : j = n - 1 := by omega
    calc w₁ = hl[j]'hj_lt_hl := hj_get.symm
      _ = hl[n-1]'hn1lt := by congr 1; omega
  -- hl.drop j is a directed cycle of length n - j ≥ 2
  refine ⟨hl.drop j, List.Nodup.drop j hl_nd, ?_, ?_⟩
  · simp only [List.length_drop, hlen]; omega
  · intro i hi
    simp only [List.length_drop, hlen] at hi
    -- (hl.drop j)[m] = hl[j + m]
    have hget : ∀ m (hm : m < n - j),
        (hl.drop j)[m]'(by simp [List.length_drop, hlen]; omega) = hl[j + m]'(by omega) :=
      fun m _ => List.getElem_drop ..
    rw [hget i (by omega)]
    by_cases hwrap : i + 1 = n - j
    · -- Closing arc: hl[j+i] = hl[n-1] → hl[j] = w₁
      have hmod : (i + 1) % (n - j) = 0 := by
        rw [show i + 1 = n - j from hwrap, Nat.mod_self]
      rw [hget 0 (by omega), hmod, Nat.zero_add]
      -- Goal: D.arc (hl[j+i]'_) (hl[j]'_)
      have hjieq : j + i = n - 1 := by omega
      convert harc_to_w1 using 2
      · exact congrArg (hl[·]'(by omega)) hjieq
      · exact hj_get.symm
    · -- Interior arc: hl[j+i] → hl[j+i+1] from Hamiltonian path
      have hmod : (i + 1) % (n - j) = i + 1 := Nat.mod_eq_of_lt (by omega)
      rw [hget (i + 1) (by omega), hmod]
      convert hl_arcs (j + i) (by omega) using 2 <;> omega

/-! ── IV.B: Non-Insertable Vertex Dichotomy ─────────────────────────────── -/

/-- In a tournament, if vertex u cannot be inserted into directed cycle l
at any position (no i with arc(l[i],u) ∧ arc(u,l[(i+1)%k])), then either
all cycle vertices beat u, or u beats all cycle vertices.

**Proof sketch**: The set A = {i : arc(l[i], u)} is closed under cyclic
successor: arc(l[i],u) → ¬arc(u,l[(i+1)%k]) (non-insertable) →
arc(l[(i+1)%k],u) (tournament). A nonempty subset of ℤ/kℤ closed under
successor is everything. So A = ∅ (u beats all) or A = {0,…,k−1}
(all beat u). -/
private lemma tournament_cycle_non_insertable (D : Digraph V)
    (hT : D.IsTournament) (l : List V) (hc : IsDirectedCycleList D l)
    (u : V) (hu : u ∉ l)
    (h_ni : ∀ (i : ℕ) (hi : i < l.length),
      ¬(D.arc (l[i]'hi) u ∧
        D.arc u (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))))) :
    (∀ (i : ℕ) (hi : i < l.length), D.arc (l[i]'hi) u) ∨
    (∀ (i : ℕ) (hi : i < l.length), D.arc u (l[i]'hi)) := by
  obtain ⟨hnd, hlen, harcs⟩ := hc
  -- Key property: arc(l[i], u) → arc(l[(i+1)%k], u) (successor closure)
  have h_succ : ∀ i (hi : i < l.length), D.arc (l[i]'hi) u →
      D.arc (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))) u := by
    intro i hi harc_iu
    have hmem : l[(i + 1) % l.length] ∈ l := List.getElem_mem ..
    have hne : l[(i + 1) % l.length] ≠ u := fun h => hu (h ▸ hmem)
    exact D.arc_of_not_arc hT hne.symm (fun h => h_ni i hi ⟨harc_iu, h⟩)
  -- Split on whether arc(l[0], u) holds
  by_cases h0 : D.arc (l[0]'(by omega)) u
  · -- Case: l[0] beats u. Iterate successor forward to show all beat u.
    left; intro j hj
    -- By induction: for all m ≤ j, arc(l[m], u)
    suffices ∀ m, m ≤ j → D.arc (l[m]'(by omega)) u from this j le_rfl
    intro m hm; induction m with
    | zero => exact h0
    | succ m ih =>
      have := h_succ m (by omega) (ih (by omega))
      rwa [Nat.mod_eq_of_lt (by omega : m + 1 < l.length)] at this
  · -- Case: l[0] does NOT beat u. Show u beats all cycle vertices.
    right; intro j hj
    -- Contrapositive: if arc(l[j], u), iterate forward to reach index 0
    have hnu : ¬D.arc (l[j]'hj) u := by
      intro harc_j; apply h0
      -- Forward iteration: arc(l[j+d], u) for all d with j+d < l.length
      have h_fwd : ∀ d, j + d < l.length →
          D.arc (l[j + d]'(by omega)) u := by
        intro d; induction d with
        | zero => intro _; simpa
        | succ d ih =>
          intro hd
          have := h_succ (j + d) (by omega) (ih (by omega))
          rwa [Nat.mod_eq_of_lt (show j + d + 1 < l.length from by omega)] at this
      -- Get arc(l[k-1], u) from forward iteration
      have h_last := h_fwd (l.length - 1 - j) (by omega)
      have h_last' : D.arc (l[l.length - 1]'(by omega)) u := by
        convert h_last using 2; omega
      -- One more step: index k-1 → 0 (wraps around)
      have := h_succ (l.length - 1) (by omega) h_last'
      rwa [show (l.length - 1 + 1) % l.length = 0 from by
        rw [show l.length - 1 + 1 = l.length from by omega, Nat.mod_self]] at this
    -- ¬arc(l[j], u) → arc(u, l[j]) by tournament property
    have hmem : l[j] ∈ l := List.getElem_mem ..
    have hne : l[j] ≠ u := fun h => hu (h ▸ hmem)
    exact D.arc_of_not_arc hT hne hnu

/-! ── IV.C: Cycle Extension ─────────────────────────────────────────────── -/

/-- In a strongly connected tournament, any directed cycle shorter than n
can be extended. This is the key step for Moon-Moser.

**Proof sketch** (longest cycle argument):
Given cycle C of length k < n, pick any u ∉ C.
• If ∃ i with arc(C[i],u) ∧ arc(u,C[(i+1)%k]): insert u → cycle of length k+1.
• Otherwise, by `tournament_cycle_non_insertable`: either all of C beats u
  or u beats all of C.
  – Partition non-cycle vertices into S⁺ (beats all of C) and S⁻ (beaten by all).
  – S = S⁺: no arc from C to S → C can't reach S → contradicts SC.
  – S = S⁻: no arc from S to C → S can't reach C → contradicts SC.
  – Both nonempty: if ∃ a∈S⁺, b∈S⁻ with arc(b,a): form cycle
    a→w₁→⋯→wₖ→b→a of length k+2, contradicting maximality.
    Otherwise all S⁺ beat all S⁻, trapping S⁻ → contradicts SC. -/
-- Helper: getElem of insertNth decomposes as three cases
private lemma insertNth_getElem_eq {α : Type*} (l : List α) (a : α) (i : ℕ)
    (hi : i ≤ l.length) (j : ℕ) (hj : j < (l.insertNth i a).length) :
    (l.insertNth i a)[j]'hj =
      if hlt : j < i then l[j]'(by simp [List.length_insertNth hi] at hj; omega)
      else if heq : j = i then a
      else l[j - 1]'(by simp [List.length_insertNth hi] at hj; omega) := by
  induction i generalizing l j with
  | zero =>
    simp only [List.insertNth_zero, Nat.not_lt_zero, ↓reduceDite, Nat.zero_le, le_refl]
    rcases j with _ | j <;> simp
  | succ i ih =>
    rcases l with _ | ⟨a', t⟩
    · simp [List.length_nil] at hi
    · simp only [List.insertNth_succ_cons]
      rcases j with _ | j
      · simp
      · simp only [List.getElem_cons_succ]
        rw [ih t (by simpa using hi) j (by simp [List.length_insertNth (by simpa using hi)] at hj ⊢; omega)]
        by_cases hlt : j < i <;> by_cases heq : j = i <;> simp_all <;> omega

private lemma tournament_cycle_extendable (D : Digraph V) (hT : D.IsTournament)
    (hsc : D.IsStronglyConnected) (l : List V) (hc : IsDirectedCycleList D l)
    (hl : l.length < Fintype.card V) :
    ∃ l' : List V, IsDirectedCycleList D l' ∧ l.length < l'.length := by
  obtain ⟨hnd, hlen2, harcs⟩ := hc
  set k := l.length with hk_def
  -- Find u ∉ l (exists since k < n)
  have ⟨u, hu⟩ : ∃ u : V, u ∉ l := by
    by_contra hall; push_neg at hall
    exact absurd (calc Fintype.card V = Finset.univ.card := Finset.card_univ.symm
      _ ≤ l.toFinset.card := Finset.card_le_card (fun v _ => List.mem_toFinset.mpr (hall v))
      _ = k := l.toFinset_card_of_nodup hnd) (by omega)
  -- Case 1: u is insertable at some position i
  by_cases h_ins : ∃ (i : ℕ) (hi : i < k),
      D.arc (l[i]'hi) u ∧ D.arc u (l[(i+1)%k]'(Nat.mod_lt _ (by omega)))
  · obtain ⟨i, hi, harc_liu, harc_ul⟩ := h_ins
    -- l.insertNth (i+1) u is a cycle of length k+1
    use l.insertNth (i + 1) u
    have hlen_ins : (l.insertNth (i + 1) u).length = k + 1 :=
      List.length_insertNth (by omega)
    refine ⟨?_, ?_, ?_⟩
    · exact List.Nodup.insertNth hu hnd
    · simp [hlen_ins]; omega
    · -- Arc condition: split by position relative to i+1
      intro j hj
      simp only [hlen_ins] at hj
      -- Get elements via the helper lemma
      have heli : ∀ m (hm : m < k + 1),
          (l.insertNth (i + 1) u)[m]'hm =
            if m < i + 1 then l[m]'(by omega)
            else if m = i + 1 then u
            else l[m - 1]'(by omega) := by
        intro m hm; exact insertNth_getElem_eq l u (i+1) (by omega) m (by rwa [hlen_ins])
      rw [heli j hj]
      -- Determine (j+1) % (k+1) and the element there
      set jnext := (j + 1) % (k + 1) with hjnext_def
      have hjnext_lt : jnext < k + 1 := Nat.mod_lt _ (by omega)
      rw [heli jnext hjnext_lt]
      -- Now split into 5 cases based on j vs i+1
      by_cases hji : j < i
      · -- j < i: both j and jnext = j+1 are below i+1
        have hjnext : jnext = j + 1 := Nat.mod_eq_of_lt (by omega)
        simp only [show j < i + 1 from by omega, show j + 1 < i + 1 from by omega,
                   hjnext, ↓reduceIte, dite_true]
        exact harcs j (by omega)
      · by_cases hji2 : j = i
        · -- j = i: new[i] = l[i], new[i+1] = u (next is i+1)
          subst hji2
          have hjnext : jnext = i + 1 := Nat.mod_eq_of_lt (by omega)
          simp [hjnext]
          exact harc_liu
        · by_cases hji3 : j = i + 1
          · -- j = i+1: new[j] = u
            subst hji3
            have hjnext : jnext = if i + 2 < k + 1 then i + 2 else 0 := by
              simp [hjnext_def]
              split_ifs with h
              · exact Nat.mod_eq_of_lt h
              · push_neg at h
                rw [show i + 2 = k + 1 from by omega, Nat.mod_self]
            simp only [show ¬(i + 1 < i + 1) from by omega, show i + 1 = i + 1 from rfl,
                       if_false, if_true]
            split_ifs at hjnext with h
            · -- i + 2 < k + 1: new[i+2] = l[i+1]
              rw [hjnext]
              simp only [show ¬(i + 2 < i + 1) from by omega, show ¬(i + 2 = i + 1) from by omega,
                         if_false, show i + 2 - 1 = i + 1 from by omega]
              convert harc_ul using 2
              exact (Nat.mod_eq_of_lt (by omega)).symm
            · -- i + 2 = k + 1: new[0] = l[0] (wrap)
              have hik : i + 1 = k := by omega
              rw [hjnext]
              simp only [show (0 : ℕ) < i + 1 from by omega, ↓reduceIte]
              convert harc_ul using 2
              simp [hik, Nat.mod_self]
          · -- j > i + 1: new[j] = l[j-1]
            have hjgt : i + 1 < j := by omega
            by_cases hwrap : j + 1 < k + 1
            · -- No wrap: jnext = j + 1
              have hjnext : jnext = j + 1 := Nat.mod_eq_of_lt hwrap
              rw [hjnext]
              simp only [show ¬(j < i + 1) from by omega, show ¬(j = i + 1) from by omega,
                         show ¬(j + 1 < i + 1) from by omega, show ¬(j + 1 = i + 1) from by omega,
                         if_false]
              exact harcs (j - 1) (by omega)
            · -- Wrap: j = k, jnext = 0
              have hjk : j = k := by omega
              have hjnext : jnext = 0 := by simp [hjnext_def, hjk, Nat.mod_self]
              rw [hjnext, hjk]
              simp only [show ¬(k < i + 1) from by omega, show ¬(k = i + 1) from by omega,
                         show (0 : ℕ) < i + 1 from by omega, if_false, ↓reduceIte]
              have : k - 1 < k := by omega
              convert harcs (k - 1) this using 2
              · simp; omega
              · simp [show k - 1 + 1 = k from by omega, Nat.mod_self]
  · -- Case 2: u is not insertable anywhere
    push_neg at h_ins
    -- Classify non-l vertices into S⁻ (beaten by all C) and S⁺ (beats all C)
    let S_minus : V → Prop := fun v => ∀ (i : ℕ) (hi : i < k), D.arc (l[i]'hi) v
    let S_plus  : V → Prop := fun v => ∀ (i : ℕ) (hi : i < k), D.arc v (l[i]'hi)
    -- u ∈ S⁻ or u ∈ S⁺
    have h_ni : S_minus u ∨ S_plus u :=
      tournament_cycle_non_insertable D hT l hc u hu
        (fun i hi ⟨h1, h2⟩ => h_ins i hi ⟨h1, h2⟩)
    -- Sub-case 2a: some non-l vertex IS insertable → k+1 cycle (same construction as Case 1)
    by_cases h_any_ins : ∃ (v : V) (hv : v ∉ l) (i : ℕ) (hi : i < k),
        D.arc (l[i]'hi) v ∧ D.arc v (l[(i + 1) % k]'(Nat.mod_lt _ (by omega)))
    · obtain ⟨v, hv_nl, i, hi, harc_lv, harc_vl⟩ := h_any_ins
      use l.insertNth (i + 1) v
      have hlen_ins : (l.insertNth (i + 1) v).length = k + 1 :=
        List.length_insertNth (by omega)
      refine ⟨?_, ?_, ?_⟩
      · exact List.Nodup.insertNth hv_nl hnd
      · simp [hlen_ins]; omega
      · intro j hj
        simp only [hlen_ins] at hj
        have heli : ∀ m (hm : m < k + 1),
            (l.insertNth (i + 1) v)[m]'hm =
              if m < i + 1 then l[m]'(by omega)
              else if m = i + 1 then v
              else l[m - 1]'(by omega) := fun m hm =>
          insertNth_getElem_eq l v (i+1) (by omega) m (by rwa [hlen_ins])
        rw [heli j hj]
        set jnext := (j + 1) % (k + 1)
        have hjnext_lt : jnext < k + 1 := Nat.mod_lt _ (by omega)
        rw [heli jnext hjnext_lt]
        by_cases hji : j < i
        · have hjnext : jnext = j + 1 := Nat.mod_eq_of_lt (by omega)
          simp only [show j < i + 1 from by omega, show j + 1 < i + 1 from by omega,
                     hjnext, ↓reduceIte, dite_true]; exact harcs j (by omega)
        · by_cases hji2 : j = i
          · subst hji2
            have hjnext : jnext = i + 1 := Nat.mod_eq_of_lt (by omega)
            simp [hjnext]; exact harc_lv
          · by_cases hji3 : j = i + 1
            · subst hji3
              have hjnext : jnext = if i + 2 < k + 1 then i + 2 else 0 := by
                simp only [jnext]; split_ifs with h
                · exact Nat.mod_eq_of_lt h
                · push_neg at h; rw [show i + 2 = k + 1 from by omega, Nat.mod_self]
              simp only [show ¬(i + 1 < i + 1) from by omega, show i + 1 = i + 1 from rfl,
                         if_false, if_true]
              split_ifs at hjnext with h
              · rw [hjnext]
                simp only [show ¬(i + 2 < i + 1) from by omega, show ¬(i + 2 = i + 1) from by omega,
                           if_false, show i + 2 - 1 = i + 1 from by omega]
                convert harc_vl using 2; exact (Nat.mod_eq_of_lt (by omega)).symm
              · have hik : i + 1 = k := by omega
                rw [hjnext]; simp only [show (0 : ℕ) < i + 1 from by omega, ↓reduceIte]
                convert harc_vl using 2; simp [hik, Nat.mod_self]
            · have hjgt : i + 1 < j := by omega
              by_cases hwrap : j + 1 < k + 1
              · have hjnext : jnext = j + 1 := Nat.mod_eq_of_lt hwrap
                rw [hjnext]
                simp only [show ¬(j < i + 1) from by omega, show ¬(j = i + 1) from by omega,
                           show ¬(j + 1 < i + 1) from by omega, show ¬(j + 1 = i + 1) from by omega,
                           if_false]
                exact harcs (j - 1) (by omega)
              · have hjk : j = k := by omega
                have hjnext : jnext = 0 := by simp [jnext, hjk, Nat.mod_self]
                rw [hjnext, hjk]
                simp only [show ¬(k < i + 1) from by omega, show ¬(k = i + 1) from by omega,
                           show (0 : ℕ) < i + 1 from by omega, if_false, ↓reduceIte]
                convert harcs (k - 1) (by omega) using 2
                · simp; omega
                · simp [show k - 1 + 1 = k from by omega, Nat.mod_self]
    · -- Sub-case 2b: no non-l vertex is insertable → all non-l in S⁺ ∪ S⁻
      push_neg at h_any_ins
      -- Every non-l vertex is in S⁻ or S⁺ (by non-insertable dichotomy)
      have h_partition : ∀ v, v ∉ l → S_minus v ∨ S_plus v := fun v hv_nl =>
        tournament_cycle_non_insertable D hT l hc v hv_nl
          (fun i hi ⟨h1, h2⟩ => h_any_ins v hv_nl i hi ⟨h1, h2⟩)
      -- S⁺ and S⁻ vertices can't be in l (loopless: arc(l[r], l[r]) is false)
      have h_sm_not_l : ∀ v, S_minus v → v ∉ l := fun v hsm hmem => by
        obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hmem
        exact D.loopless _ (hsm r hr)
      have h_sp_not_l : ∀ v, S_plus v → v ∉ l := fun v hsp hmem => by
        obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hmem
        exact D.loopless _ (hsp r hr)
      -- KEY: find a ∈ S⁻, b ∈ S⁺ with arc(a,b), using SC
      -- Proof strategy:
      --   (1) S⁻ ≠ ∅: u ∈ S⁻ (from h_ni left) or symmetrically S⁺ ≠ ∅ (from right).
      --   (2) S⁺ ≠ ∅ (when u ∈ S⁻): if all non-l ∈ S⁻, any v ∈ S⁻ cannot arc into l
      --       (which would contradict S⁻ def), so v can't reach l via SC. SC violation.
      --   (3) SC walk from a∈S⁻ to b∈S⁺: first S⁺ vertex on walk has predecessor not in l
      --       (S⁺ beats l, so predecessor in l ⟹ tournament contradiction) and not in S⁺
      --       (minimality), hence in S⁻. That pair gives arc(a',b') with a'∈S⁻, b'∈S⁺.
      suffices h_pair : ∃ (a b : V), a ∉ l ∧ b ∉ l ∧ a ≠ b ∧ S_minus a ∧ S_plus b ∧ D.arc a b by
        obtain ⟨a, b, ha_nl, hb_nl, hab_ne, ha_sm, hb_sp, harc_ab⟩ := h_pair
        -- Build cycle l ++ [a, b] of length k+2 > k
        use l ++ [a, b]
        have hlen2 : (l ++ [a, b]).length = k + 2 := by simp [List.length_append]; omega
        refine ⟨?_, ?_, ?_⟩
        · -- Nodup: l Nodup, a ∉ l, b ∉ l, a ≠ b
          rw [List.nodup_append]
          refine ⟨hnd, by simp [hab_ne], ?_⟩
          intro v hv_l hv_ab
          simp only [List.mem_cons, List.mem_singleton] at hv_ab
          rcases hv_ab with rfl | rfl
          · exact ha_nl hv_l
          · exact hb_nl hv_l
        · simp [hlen2]
        · -- Arc condition for l ++ [a, b]
          intro i hi
          rw [hlen2] at hi
          have hget : ∀ m (hm : m < k + 2), (l ++ [a, b])[m]'hm =
              if hlt : m < k then l[m]'hlt else if m = k then a else b := by
            intro m hm
            split_ifs with hlt heq
            · exact List.getElem_append_left hlt
            · subst heq
              rw [List.getElem_append_right (le_refl k)]
              simp [Nat.sub_self]
            · have hmeq : m = k + 1 := by omega
              subst hmeq
              rw [List.getElem_append_right (by omega : k ≤ k + 1)]
              simp
          set inext := (i + 1) % (k + 2) with hinext_def
          have hinext_lt : inext < k + 2 := Nat.mod_lt _ (by omega)
          rw [hget i (by omega), hget inext hinext_lt]
          -- Four cases: i < k-1, i = k-1, i = k, i = k+1
          have hi4 : i < k - 1 ∨ i = k - 1 ∨ i = k ∨ i = k + 1 := by omega
          rcases hi4 with hilt | rfl | rfl | rfl
          · -- i < k-1: arc(l[i], l[i+1]) from interior arcs of l
            have hinext_eq : inext = i + 1 := by
              simp [hinext_def]; exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq]
            simp only [show i < k from by omega, show i + 1 < k from by omega, ↓reduceDite]
            convert harcs i (by omega) using 2
            exact (Nat.mod_eq_of_lt (show i + 1 < k from by omega)).symm
          · -- i = k-1: arc(l[k-1], a)
            have hinext_eq : inext = k := by
              simp [hinext_def, show k - 1 + 1 = k from by omega]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq]
            simp only [show k - 1 < k from by omega, ↓reduceDite,
                       show k = k from rfl, if_true]
            exact ha_sm (k - 1) (by omega)
          · -- i = k: arc(a, b)
            have hinext_eq : inext = k + 1 := by
              simp [hinext_def]; exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq]
            simp only [show ¬(k < k) from lt_irrefl k, ↓reduceDite,
                       show k = k from rfl, if_true,
                       show ¬(k + 1 < k) from by omega, show k + 1 ≠ k from by omega, if_false]
            exact harc_ab
          · -- i = k+1: arc(b, l[0])
            have hinext_eq : inext = 0 := by
              simp [hinext_def, show k + 1 + 1 = k + 2 from by omega, Nat.mod_self]
            rw [hinext_eq]
            simp only [show ¬(k + 1 < k) from by omega, show k + 1 ≠ k from by omega, if_false,
                       show (0 : ℕ) < k from by omega, ↓reduceDite]
            exact hb_sp 0 (by omega)
      -- Prove ∃ a ∈ S⁻, b ∈ S⁺ with arc(a,b) using strong connectivity
      -- (1) Tournament antisymmetry
      have h_anti : ∀ (a b : V), a ≠ b → D.arc a b → ¬D.arc b a :=
        fun a b hne hab => (hT a b hne).elim (fun ⟨_, h⟩ => h) (fun ⟨_, h⟩ => absurd hab h)
      -- (2) S⁻ vertex cannot arc to any cycle vertex
      have h_sm_nl : ∀ v i (hi : i < k), S_minus v → ¬D.arc v (l[i]'hi) :=
        fun v i hi hv harc =>
          h_anti v (l[i]'hi) (fun h => D.loopless _ (h ▸ harc)) harc (hv i hi)
      -- (3) Cycle vertex cannot arc to any S⁺ vertex
      have h_sp_nl : ∀ v i (hi : i < k), S_plus v → ¬D.arc (l[i]'hi) v :=
        fun v i hi hv harc =>
          h_anti (l[i]'hi) v (fun h => D.loopless _ (h ▸ harc)) harc (hv i hi)
      -- (4) SC helper: if X ⊆ V\l, X closed under D-arcs, X nonempty → SC fails
      have h_contra : ∀ (X : V → Prop),
          (∀ v w, X v → D.arc v w → X w) →
          (∀ v, X v → v ∉ l) → (∃ x, X x) → False := by
        intro X hcl hXl ⟨x₀, hx₀⟩
        have hk_pos : 0 < k := by omega
        obtain ⟨path, hhead, hlast, hparcs⟩ := hsc x₀ (l[0]'hk_pos)
          (fun h => hXl x₀ hx₀ (h ▸ List.getElem_mem _))
        have hpne : path ≠ [] := by rintro rfl; simp at hhead
        -- All path[i] ∈ X by induction
        have hall : ∀ i (hi : i < path.length), X (path[i]'hi) := by
          intro i; induction i with
          | zero =>
            intro hi
            cases path with
            | nil => contradiction
            | cons a t =>
              simp only [List.head?, Option.some.injEq] at hhead
              exact hhead ▸ hx₀
          | succ n ih =>
            intro hi
            exact hcl _ _ (ih (by omega)) (hparcs n (by omega))
        -- Last element is l[0] ∈ l → X (l[0]) contradicts hXl
        have hmem : l[0]'hk_pos ∈ path :=
          (Option.some.inj ((List.getLast?_eq_getLast hpne).symm.trans hlast)) ▸
            List.getLast_mem hpne
        rw [List.mem_iff_getElem] at hmem
        obtain ⟨i, hi, heq⟩ := hmem
        exact hXl _ (heq ▸ hall i hi) (List.getElem_mem _)
      -- (5) By contradiction: assume no S⁻→S⁺ arc exists
      by_contra h_no_pair
      push_neg at h_no_pair
      -- h_no_pair : ∀ a b, a ∉ l → b ∉ l → a ≠ b → S_minus a → S_plus b → ¬D.arc a b
      -- (6) S_minus is closed under D-arcs (under the no-crossing assumption)
      have h_sm_closed : ∀ v w, S_minus v → D.arc v w → S_minus w := by
        intro v w hv harc
        have hw_nl : w ∉ l := by
          intro hmem
          rw [List.mem_iff_getElem] at hmem
          obtain ⟨r, hr, heq⟩ := hmem
          exact h_anti v (l[r]'hr) (fun h => D.loopless _ (h ▸ heq.symm ▸ harc))
            (heq.symm ▸ harc) (hv r hr)
        rcases h_partition w hw_nl with hsm | hsp
        · exact hsm
        · -- arc(v,w) with v∈S⁻, w∈S⁺ contradicts no-crossing assumption
          have hane : v ≠ w :=
            fun h => h_anti (l[0]'(by omega)) v
              (fun heq => D.loopless _ (heq ▸ hv 0 (by omega)))
              (hv 0 (by omega)) (h.symm ▸ hsp 0 (by omega))
          exact absurd harc (h_no_pair v w (h_sm_not_l v hv) (h_sp_not_l w hsp) hane hv hsp)
      -- (7) Apply h_contra based on h_ni
      rcases h_ni with hsu | hsu
      · -- u ∈ S⁻: S_minus is closed, nonempty, ⊆ V\l → SC contradiction
        exact h_contra S_minus h_sm_closed h_sm_not_l ⟨u, hsu⟩
      · -- u ∈ S⁺: either S⁻ nonempty (apply h_contra) or S⁻=∅ → all non-l in S⁺
        by_cases h_sm_ne : ∃ a, S_minus a
        · exact h_contra S_minus h_sm_closed h_sm_not_l h_sm_ne
        · -- S⁻ = ∅: all non-l ∈ S⁺, so arc from l stays in l (S⁺ beats l → ¬arc(l,S⁺))
          push_neg at h_sm_ne
          have hk_pos : 0 < k := by omega
          have h_l_closed : ∀ j (hj : j < k) w, D.arc (l[j]'hj) w → w ∈ l := by
            intro j hj w harc
            by_contra hw_nl
            rcases h_partition w hw_nl with hsm | hsp
            · exact h_sm_ne w hsm
            · exact h_sp_nl w j hj hsp harc
          -- SC path from l[0] to u (u ∉ l), but all path elements must stay in l
          obtain ⟨path, hhead, hlast, hparcs⟩ := hsc (l[0]'hk_pos) u
            (fun h => hu (h ▸ List.getElem_mem _))
          have hpne : path ≠ [] := by rintro rfl; simp at hhead
          have hall_l : ∀ i (hi : i < path.length), (path[i]'hi) ∈ l := by
            intro i; induction i with
            | zero =>
              intro hi
              cases path with
              | nil => contradiction
              | cons a t =>
                simp only [List.head?, Option.some.injEq] at hhead
                exact hhead ▸ List.getElem_mem _
            | succ n ih =>
              intro hi
              have hn_mem := ih (by omega)
              rw [List.mem_iff_getElem] at hn_mem
              obtain ⟨r, hr, heq⟩ := hn_mem
              exact h_l_closed r hr _ (heq.symm ▸ hparcs n (by omega))
          -- path.last = u ∉ l → contradiction
          have hmem : u ∈ path :=
            (Option.some.inj ((List.getLast?_eq_getLast hpne).symm.trans hlast)) ▸
              List.getLast_mem hpne
          rw [List.mem_iff_getElem] at hmem
          obtain ⟨i, hi, heq⟩ := hmem
          exact hu (heq ▸ hall_l i hi)

/-! ── IV.D: List Cycle to Hamiltonian Cycle Equivalence ──────────────────── -/

/-- Convert a length-n directed cycle list to `HasHamiltonianCycle`.
Constructs the equivalence V ≃ Fin n via the list's getElem function,
analogous to `list_path_to_hamiltonian`. -/
private lemma list_cycle_to_hamiltonian (D : Digraph V) (l : List V)
    (hc : IsDirectedCycleList D l) (hlen : l.length = Fintype.card V) :
    D.HasHamiltonianCycle := by
  obtain ⟨hnd, hlen2, harcs⟩ := hc
  have hcard_pos : 0 < Fintype.card V := by omega
  -- Every vertex appears in l (nodup list of full length covers V)
  have hmem : ∀ v : V, v ∈ l := by
    intro v; rw [← List.mem_toFinset]
    exact (Finset.eq_univ_of_card _ (by rw [l.toFinset_card_of_nodup hnd, hlen])) ▸
      Finset.mem_univ v
  -- Build bijection Fin n → V via list indexing
  let f : Fin (Fintype.card V) → V := fun i =>
    l[i.val]'(Nat.lt_of_lt_of_eq i.isLt hlen.symm)
  have hf_bij : Function.Bijective f := by
    constructor
    · intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp only [f] at heq
      ext; exact List.Nodup.getElem_inj_iff hnd |>.mp heq
    · intro v
      have hv_mem := hmem v
      rw [List.mem_iff_getElem] at hv_mem
      obtain ⟨i, hi, hvi⟩ := hv_mem
      refine ⟨⟨i, Nat.lt_of_lt_of_eq hi hlen⟩, ?_⟩
      simp only [f]; exact hvi
  -- σ.symm i = f i = l[i], so the cycle arc condition matches directly
  exact ⟨(Equiv.ofBijective f hf_bij).symm, fun i => by
    -- σ.symm = (Equiv.ofBijective f _).symm.symm = Equiv.ofBijective f _ = f
    change D.arc (f i) (f ⟨(i.val + 1) % Fintype.card V, Nat.mod_lt _ hcard_pos⟩)
    simp only [f, ← hlen]
    exact harcs i.val (by omega)⟩

/-! ── IV.E: Growing Cycles to Hamiltonian ────────────────────────────────── -/

/-- Given any directed cycle in a SC tournament, repeatedly extend it
until it reaches length n (Hamiltonian). Well-founded recursion on
(n − cycle length); the cycle grows by 1 or 2 each call. -/
private noncomputable def grow_cycle_to_hamiltonian (D : Digraph V) (hT : D.IsTournament)
    (hsc : D.IsStronglyConnected) (l : List V) (hc : IsDirectedCycleList D l) :
    D.HasHamiltonianCycle := by
  by_cases hm : l.length = Fintype.card V
  · exact list_cycle_to_hamiltonian D l hc hm
  · have hle : l.length ≤ Fintype.card V := nodup_length_le_card l hc.1
    obtain ⟨l', hc', hl'⟩ := tournament_cycle_extendable D hT hsc l hc (by omega)
    have hle' : l'.length ≤ Fintype.card V := nodup_length_le_card l' hc'.1
    exact grow_cycle_to_hamiltonian D hT hsc l' hc'
termination_by Fintype.card V - l.length
decreasing_by omega

/-! ── IV.F: Moon-Moser Theorem ───────────────────────────────────────────── -/

/-- **Moon-Moser Theorem (1963)**

Every strongly connected tournament has a directed Hamiltonian cycle.

Every tournament (even non-strongly connected ones) has a Hamiltonian
path (Rédei's theorem, 1934). The Moon-Moser result adds that strong
connectivity gives a Hamiltonian CYCLE.

**Proof**: Get an initial cycle from strong connectivity, then repeatedly
extend it using the tournament insertion argument until it covers all
vertices. -/
theorem moon_moser (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hT : D.IsTournament) (hsc : D.IsStronglyConnected) :
    D.HasHamiltonianCycle := by
  obtain ⟨l, hc⟩ := sc_tournament_has_cycle D hn hT hsc
  exact grow_cycle_to_hamiltonian D hT hsc l hc

/-- **Rédei's Theorem (1934)**

Every tournament has a directed Hamiltonian PATH.
(No connectivity assumption needed.) -/
theorem redei (D : Digraph V) (hn : 2 ≤ Fintype.card V)
    (hT : D.IsTournament) :
    D.HasHamiltonianPath := by
  obtain ⟨l, hlen, hp⟩ := tournament_full_path_list D hT (by omega)
  exact list_path_to_hamiltonian D l hlen hp

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: EDGE THRESHOLD FOR DIRECTED HAMILTONICITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The number of arcs in a digraph. -/
noncomputable def Digraph.arcCount (D : Digraph V) : ℕ :=
  letI : DecidablePred (fun p : V × V => D.arc p.1 p.2) := Classical.decPred _
  Fintype.card {p : V × V // D.arc p.1 p.2}

-- Arithmetic helper: arcCount > (n-1)² implies at most n-2 arcs missing from K*_n.
private lemma missing_arcs_le (n m : ℕ) (hn : 3 ≤ n) (harc : (n - 1) ^ 2 < m) :
    n * (n - 1) - m ≤ n - 2 := by
  set k := n - 1
  have hkn : k + 1 = n := by omega
  have hnn1 : n * k = k ^ 2 + k := by rw [show n = k + 1 from hkn.symm]; ring
  rw [hnn1]; set a := k ^ 2; omega

-- Key combinatorial bound: the number of permutations σ : Perm(Fin n) such that
-- a directed arc (a → b) appears at some consecutive position in the cycle given by σ
-- is at most n * (n-2)!.
-- Proof sketch: for each position i (n choices), fixing σ(i)=a, σ((i+1)%n)=b leaves
-- (n-2)! permutations of the remaining n-2 values. Positions are disjoint (σ injective).
private lemma perm_arc_bad_card_le {n : ℕ} (hn : 3 ≤ n) {a b : Fin n} (hab : a ≠ b) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      ∃ i : Fin n, σ i = a ∧
        σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩ = b)).card ≤
    n * (n - 2).factorial := by
  have h_perm : Finset.filter (fun σ : Equiv.Perm (Fin n) => ∃ i : Fin n, σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ ⊆ Finset.biUnion Finset.univ (fun i : Fin n => Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ) := by
    aesop_cat;
  -- Each set in the union has cardinality (n-2)! because fixing two values of a permutation leaves (n-2)! choices.
  have h_card : ∀ i : Fin n, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ) ≤ (n - 2).factorial := by
    intro i
    have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ) ≤ Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) / (n - 1) := by
      have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) = Finset.card (Finset.biUnion (Finset.univ.erase a) (fun b => Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ)) := by
        congr with σ;
        simp +decide [ Finset.mem_biUnion ];
        intro hi hj; have := σ.injective ( hj.trans hi.symm ) ; simp_all +decide [ Fin.ext_iff, Nat.mod_eq_of_lt ] ;
        have := Nat.mod_add_div ( i + 1 ) n; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        nlinarith [ show ( i : ℕ ) < n from i.2, show ( i + 1 : ℕ ) / n = 0 from by nlinarith [ show ( i : ℕ ) < n from i.2 ] ];
      rw [ h_card, Finset.card_biUnion ];
      · rw [ Nat.le_div_iff_mul_le ( Nat.sub_pos_of_lt ( by linarith ) ) ];
        have h_card : ∀ u ∈ Finset.univ.erase a, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = u) Finset.univ) ≥ Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ) := by
          intros u hu;
          have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = u) Finset.univ) ≥ Finset.card (Finset.image (fun σ : Equiv.Perm (Fin n) => Equiv.swap u b * σ) (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a ∧ σ (Fin.mk ((i.val + 1) % n) (Nat.mod_lt (i.val + 1) (Nat.zero_lt_of_lt hn))) = b) Finset.univ)) := by
            refine Finset.card_le_card ?_;
            simp +decide [ Finset.subset_iff ];
            grind +splitImp;
          rwa [ Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ] at h_card;
        simpa [ mul_comm, Finset.card_erase_of_mem ( Finset.mem_univ a ) ] using Finset.sum_le_sum h_card;
      · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun σ hσx hσy => hxy <| by aesop;
    have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) = (n - 1).factorial := by
      have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) * n = Finset.card (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
        have h_card : ∀ j : Fin n, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = j) Finset.univ) = Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ) := by
          intro j
          have h_card : Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = j) Finset.univ) = Finset.card (Finset.image (fun σ : Equiv.Perm (Fin n) => Equiv.swap a j * σ) (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = a) Finset.univ)) := by
            congr with σ ; aesop;
          rw [ h_card, Finset.card_image_of_injective _ fun x y hxy => by simpa using hxy ];
        have h_card : Finset.card (Finset.univ : Finset (Equiv.Perm (Fin n))) = ∑ j : Fin n, Finset.card (Finset.filter (fun σ : Equiv.Perm (Fin n) => σ i = j) Finset.univ) := by
          simp +decide only [Finset.card_eq_sum_ones, Finset.sum_fiberwise];
        simp_all +decide [ mul_comm ];
      simp_all +decide [ Finset.card_univ, Fintype.card_perm ];
      cases n <;> simp_all +decide [ Nat.factorial_succ ];
      nlinarith;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.factorial ];
    · contradiction;
    · contradiction;
  exact le_trans ( Finset.card_le_card h_perm ) ( le_trans ( Finset.card_biUnion_le ) ( by simpa using Finset.sum_le_sum fun i ( hi : i ∈ Finset.univ ) => h_card i ) )

-- Factorial arithmetic: (n-2) * n * (n-2)! < n! for n ≥ 3.
private lemma counting_factorial_lt {n : ℕ} (hn : 3 ≤ n) :
    (n - 2) * n * (n - 2).factorial < n.factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 2 = k + 1 by omega]
  have hpos : 0 < (k + 1).factorial := Nat.factorial_pos _
  have hfact : (k + 3).factorial = (k + 3) * ((k + 2) * (k + 1).factorial) := by
    simp [Nat.factorial_succ, mul_comm, mul_assoc, mul_left_comm]
  nlinarith [hfact]

-- Helper: arc count equals filter cardinality on Fin n × Fin n via bijection φ.
-- Kept separate from hamiltonian_of_few_missing_arcs to avoid DecidableRel instance clashes
-- (arcCount's internal `letI := Classical.decPred _` must be the only DecidablePred for V × V).
-- The `[DecidableRel D.arc]` parameter allows the filter in the return type to be elaborated.
-- The body uses `classical` + `simp [Digraph.arcCount, Fintype.card_subtype]` to handle all
-- instance synthesis uniformly, reducing the letI and converting Fintype.card to filter.card.
omit [DecidableEq V] in
private lemma arcCount_eq_filter_bij {n : ℕ} (D : Digraph V) (φ : V ≃ Fin n)
    [DecidableRel D.arc] :
    (Finset.univ.filter (fun p : Fin n × Fin n => D.arc (φ.symm p.1) (φ.symm p.2))).card = D.arcCount := by
  classical
  simp only [Digraph.arcCount, Fintype.card_subtype]
  apply Finset.card_bij' (fun p _ => (φ.symm p.1, φ.symm p.2)) (fun p _ => (φ p.1, φ p.2))
  · intro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact hp
  · intro ⟨u, v⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  · intro ⟨a, b⟩ _; simp [Equiv.apply_symm_apply]
  · intro ⟨u, v⟩ _; simp [Equiv.symm_apply_apply]

-- Counting argument (probabilistic method): with ≤ n-2 arcs missing from K*_n,
-- a Hamiltonian cycle exists (no strong connectivity needed).
-- Proof: n! permutations; each missing arc (a→b) contributes ≤ n*(n-2)! "bad" ones;
-- total bad ≤ (n-2)*n*(n-2)! < n!; so ≥ 1 good permutation gives the HC.
private lemma hamiltonian_of_few_missing_arcs (D : Digraph V)
    (hn : 3 ≤ Fintype.card V)
    (hmissing : Fintype.card V * (Fintype.card V - 1) - D.arcCount ≤ Fintype.card V - 2) :
    D.HasHamiltonianCycle := by
  set n := Fintype.card V with hn_def
  have hn_pos : 0 < n := by omega
  -- Make arc decidable (needed for Finset.filter)
  haveI hdec_arc : DecidableRel D.arc := fun a b => Classical.dec _
  -- Make V nonempty (needed for Fintype.equivFin)
  haveI hnonempty : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  -- Canonical bijection φ : V ≃ Fin n
  let φ : V ≃ Fin n := Fintype.equivFin V
  -- π : Perm(Fin n) is "good" if the cycle φ.symm(π 0)→···→φ.symm(π(n-1))→φ.symm(π 0)
  -- uses only arcs that exist in D.
  let goodPerms : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter (fun π =>
      ∀ i : Fin n, D.arc (φ.symm (π i))
        (φ.symm (π ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩)))
  -- Extract HC from any good permutation.
  suffices hgood : goodPerms.Nonempty by
    obtain ⟨π, hπ⟩ := hgood
    have hπ' := (Finset.mem_filter.mp hπ).2
    refine ⟨φ.trans π.symm, fun i => ?_⟩
    simp only [Equiv.symm_trans_apply, Equiv.symm_symm]
    exact hπ' i
  -- Counting: show goodPerms is nonempty via cardinality.
  rw [← Finset.card_pos]
  -- The set of missing arcs (as Fin n pairs).
  let missingArcs : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ ¬D.arc (φ.symm p.1) (φ.symm p.2))
  -- For each missing arc, the set of permutations that "use" it somewhere in the cycle.
  let badSetFor : Fin n × Fin n → Finset (Equiv.Perm (Fin n)) := fun p =>
    Finset.univ.filter (fun π =>
      ∃ i : Fin n, π i = p.1 ∧ π ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩ = p.2)
  -- Every non-good permutation lies in badSetFor p for some missing arc p.
  have hcover : Finset.univ \ goodPerms ⊆ Finset.biUnion missingArcs badSetFor := by
    intro π hπ
    have hπ_sd := Finset.mem_sdiff.mp hπ
    have hbad : ¬∀ i : Fin n, D.arc (φ.symm (π i))
        (φ.symm (π ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩)) := fun hgood =>
      hπ_sd.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩)
    push_neg at hbad
    obtain ⟨i, hi⟩ := hbad
    rw [Finset.mem_biUnion]
    have hne' : π i ≠ π ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩ := by
      intro heq
      apply_fun π.symm at heq
      simp only [Equiv.symm_apply_apply] at heq
      have hval : i.val = (i.val + 1) % n := congr_arg Fin.val heq
      rcases Nat.lt_or_ge (i.val + 1) n with h | h
      · rw [Nat.mod_eq_of_lt h] at hval; omega
      · have heqn : i.val + 1 = n := by omega
        rw [heqn, Nat.mod_self] at hval; omega
    exact ⟨⟨π i, π ⟨(i.val + 1) % n, Nat.mod_lt _ hn_pos⟩⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne', hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, rfl, rfl⟩⟩
  -- |missingArcs| ≤ n - 2 (complement counting: n*(n-1) total non-loop pairs minus present).
  have hmissing_count : missingArcs.card ≤ n - 2 := by
    -- Present arcs: arcs of D indexed by Fin n via φ
    let presentArcs : Finset (Fin n × Fin n) :=
      Finset.univ.filter (fun p => D.arc (φ.symm p.1) (φ.symm p.2))
    -- presentArcs.card = D.arcCount (bijection via φ, using helper outside this lemma)
    have hpresent_card : presentArcs.card = D.arcCount :=
      arcCount_eq_filter_bij D φ
    -- missingArcs and presentArcs are disjoint (no arc can be both missing and present)
    have hdisj : Disjoint missingArcs presentArcs :=
      Finset.disjoint_filter.2 fun ⟨a, b⟩ _ ⟨_, hnot⟩ harc => hnot harc
    -- missingArcs ∪ presentArcs = all off-diagonal pairs of Fin n
    have hunion : (missingArcs ∪ presentArcs).card = n * (n - 1) := by
      have heq : missingArcs ∪ presentArcs = (Finset.univ : Finset (Fin n)).offDiag := by
        ext ⟨a, b⟩
        simp only [Finset.mem_union, Finset.mem_offDiag, Finset.mem_univ, true_and]
        constructor
        · rintro (hm | hp)
          · exact (Finset.mem_filter.mp hm).2.1
          · intro heq; subst heq
            exact D.loopless (φ.symm a) (Finset.mem_filter.mp hp).2
        · intro hab
          by_cases h : D.arc (φ.symm a) (φ.symm b)
          · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab, h⟩
      -- offDiag_card gives n^2 - n; mul_tsub + mul_one expands RHS n*(n-1) to n*n-n
      rw [heq, Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
      simp only [mul_tsub, mul_one]
    -- Partition: missingArcs.card + D.arcCount = n * (n - 1)
    have hpart : missingArcs.card + D.arcCount = n * (n - 1) := by
      rw [← hpresent_card, ← Finset.card_union_of_disjoint hdisj]
      exact hunion
    omega
  -- Union bound: |biUnion| ≤ Σ |badSetFor p| ≤ |missing| * n*(n-2)!
  have hbad_union_card : (Finset.biUnion missingArcs badSetFor).card ≤
      (n - 2) * n * (n - 2).factorial := by
    calc (Finset.biUnion missingArcs badSetFor).card
        ≤ missingArcs.sum (fun p => (badSetFor p).card) := Finset.card_biUnion_le
      _ ≤ missingArcs.card * (n * (n - 2).factorial) := by
          apply Finset.sum_le_card_nsmul
          intro ⟨a, b⟩ hp
          exact perm_arc_bad_card_le (by omega) (Finset.mem_filter.mp hp).2.1
      _ ≤ (n - 2) * (n * (n - 2).factorial) := Nat.mul_le_mul_right _ hmissing_count
      _ = (n - 2) * n * (n - 2).factorial := by ring
  -- Total = n!, bad < n!, so good > 0.
  have htotal : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Fintype.card_perm, Fintype.card_fin]
  have harith : (n - 2) * n * (n - 2).factorial < n.factorial :=
    counting_factorial_lt (by omega)
  have hle : (Finset.univ \ goodPerms).card ≤ (n - 2) * n * (n - 2).factorial :=
    (Finset.card_le_card hcover).trans hbad_union_card
  have hsum : (Finset.univ \ goodPerms).card + goodPerms.card = n.factorial := by
    -- Finset.card_sdiff (s t) : #(t \ s) = #t - #(s ∩ t); use s=goodPerms, t=univ
    have hsdiff := @Finset.card_sdiff _ goodPerms Finset.univ
    simp only [Finset.inter_univ] at hsdiff
    rw [Finset.card_univ, htotal] at hsdiff
    -- hsdiff : (Finset.univ \ goodPerms).card = n.factorial - goodPerms.card
    have hle : goodPerms.card ≤ n.factorial := by
      have h := Finset.card_le_card (Finset.subset_univ goodPerms)
      rw [Finset.card_univ, htotal] at h; exact h
    rw [hsdiff, Nat.sub_add_cancel hle]
  omega

/-- **Directed Hamiltonian threshold**: a digraph on n ≥ 3 vertices with more
than (n-1)² arcs is Hamiltonian, provided it is strongly connected.

This is the directed analogue of the Erdős #1012 edge threshold. -/
theorem directed_hamiltonian_threshold (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hsc : D.IsStronglyConnected)
    (harc : (Fintype.card V - 1) ^ 2 < D.arcCount) :
    D.HasHamiltonianCycle :=
  hamiltonian_of_few_missing_arcs D hn
    (missing_arcs_le (Fintype.card V) D.arcCount hn harc)

/-
## Proof Roadmap

### Directed Hamiltonian Threshold (PROVED, 2 sorries remain in helpers)
Decomposed via counting/probabilistic method:
1. `missing_arcs_le` (PROVED): arcCount > (n-1)² → at most n-2 missing arcs
2. `perm_arc_bad_card_le` (PROVED): counting lemma — ≤ n*(n-2)! perms use any given arc
3. `counting_factorial_lt` (PROVED): (n-2)*n*(n-2)! < n!
4. `hamiltonian_of_few_missing_arcs` (proved using 1-3): counting → good perm exists
5. `directed_hamiltonian_threshold` (PROVED): delegates to 1 + 4

Remaining sorries: none (directed_hamiltonian_threshold is fully proved, 0 sorries)

### Ghouila-Houri (~200 lines, still open)
The proof follows the same structure as Dirac's theorem:
1. Start with a longest directed path P in D
2. Show P must be Hamiltonian (degree conditions prevent extension if k < n)
3. Close P into a cycle using degree conditions on first/last vertices

### Rédei (DONE)
Proved by induction via tournament insertion lemma.
-/

#check @ghouila_houri
#check @moon_moser
#check @redei
#check @directed_hamiltonian_threshold

end Erdos1012OQ03

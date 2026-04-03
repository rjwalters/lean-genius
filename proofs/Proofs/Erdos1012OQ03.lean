import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

-- Enable classical decidability for all propositions in this file.
-- Needed since Digraph.arc is an arbitrary Prop, but Fintype on subtypes
-- and various lemmas require DecidablePred/DecidableRel.
attribute [local instance] Classical.propDecidable

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
        Nat.mod_lt _ (Nat.zero_le i.val |>.trans_lt i.isLt)⟩)

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
    ∃ k, k ≤ l.length ∧ IsDirectedPathList D (l.insertIdx k u) := by
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
          simp only [List.length_cons, List.insertIdx_zero] at hi ⊢
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
        · -- Nodup of a :: (t.insertIdx k_t u)
          apply List.Nodup.cons
          · intro hmem
            rw [List.mem_insertIdx (by omega)] at hmem
            rcases hmem with rfl | hmem
            · exact ha_ne_u rfl
            · exact (List.nodup_cons.mp hnd).1 hmem
          · exact hk_t_nd
        · -- Arcs in a :: (t.insertIdx k_t u)
          intro i hi
          match i with
          | 0 =>
            -- Arc: a → first element of (t.insertIdx k_t u)
            by_cases hk0 : k_t = 0
            · -- Inserted at start of tail: first element is u
              subst hk0; simp [List.insertIdx_zero]; exact harc_au
            · -- k_t > 0: first element of tail unchanged (t[0])
              have hlt : 0 < k_t := Nat.pos_of_ne_zero hk0
              conv_lhs => simp only [List.getElem_cons_zero]
              rw [show (a :: t.insertIdx k_t u)[0 + 1]'(by omega) =
                (t.insertIdx k_t u)[0]'(by omega) from List.getElem_cons_succ ..]
              rw [List.getElem_insertIdx_of_lt (by omega)]
              exact harcs 0 (by simp [List.length_cons]; omega)
          | i + 1 =>
            -- Arc within t.insertIdx k_t u (from IH)
            show D.arc ((a :: t.insertIdx k_t u)[i + 1]'(by omega))
              ((a :: t.insertIdx k_t u)[i + 2]'(by omega))
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
      exact ⟨l.insertIdx k u, by simp [List.length_insertIdx, hk_le, hlen], hp'⟩

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
  -- Get Hamiltonian path from Rédei's construction
  obtain ⟨l, hlen, hnd, harcs⟩ := tournament_full_path_list D hT (by omega)
  have hn3 : 3 ≤ l.length := hlen ▸ hn
  -- Every vertex appears in l
  have hmem : ∀ v : V, v ∈ l := by
    intro v; rw [← List.mem_toFinset]
    exact (Finset.eq_univ_of_card _ (l.toFinset_card_of_nodup hnd ▸ hlen)) ▸ Finset.mem_univ v
  -- Last and first are distinct
  have hne : l[l.length - 1]'(by omega) ≠ l[0]'(by omega) :=
    fun h => absurd (hnd.getElem_inj_iff.mp h) (by omega)
  -- SC gives a path from last to first
  obtain ⟨p, hp_head, hp_last, hp_arcs⟩ := hsc _ _ hne
  -- Extract p = [last, p₁, ...] from head? = some last
  obtain ⟨p_tl, rfl⟩ := List.head?_eq_some_iff.mp hp_head
  -- Path has length ≥ 2 (last ≠ first, so p_tl is nonempty)
  have hp2 : 1 ≤ p_tl.length := by
    by_contra h; push_neg at h
    simp [Nat.lt_one_iff.mp h, List.getLast?] at hp_last
    exact hne hp_last
  -- First step: arc from last to p_tl[0]
  have h_back : D.arc (l[l.length - 1]'(by omega)) (p_tl[0]'(by omega)) := by
    have := hp_arcs 0 (by simp; omega)
    simpa using this
  -- p_tl[0] ≠ l[l.length-1] (loopless)
  have hp1_ne_last : p_tl[0]'(by omega) ≠ l[l.length - 1]'(by omega) :=
    fun h => D.loopless _ (h ▸ h_back)
  -- p_tl[0] is in l (l covers all of V), find its index k
  obtain ⟨k, hk, hk_eq⟩ := List.mem_iff_getElem.mp (hmem (p_tl[0]'(by omega)))
  -- k < l.length - 1 (since l[k] = p_tl[0] ≠ l[l.length-1])
  have hk_lt : k < l.length - 1 := by
    rcases Nat.lt_or_eq_of_le (Nat.lt_of_lt_of_le hk (by omega) |> Nat.lt_succ_iff.mp) with h | h
    · exact h
    · exfalso; exact hp1_ne_last (hk_eq ▸ show l[k] = l[l.length - 1] from by congr 1)
  -- Construct cycle: l.drop k = [l[k], l[k+1], ..., l[n-1]]
  refine ⟨l.drop k, ?_, ?_, ?_⟩
  · -- Nodup: sublist of nodup list
    exact (List.drop_sublist k l).nodup hnd
  · -- Length ≥ 2
    simp [List.length_drop]; omega
  · -- Arc condition for l.drop k (wrap-around uses h_back and hk_eq)
    intro i hi
    simp only [List.length_drop] at hi ⊢
    by_cases h_wrap : i + 1 = l.length - k
    · -- Wrap-around: last element → first element of cycle
      rw [show (i + 1) % (l.length - k) = 0 from by omega]
      simp only [List.getElem_drop]
      -- l[k + i] = l[l.length - 1] (since k + i = l.length - 1)
      -- l[k + 0] = l[k] = p_tl[0]
      have hi_eq : k + i = l.length - 1 := by omega
      conv_lhs => rw [show l[k + i]'(by omega) = l[l.length - 1]'(by omega) from by congr 1]
      rw [Nat.add_zero]
      rwa [← hk_eq]
    · -- Normal consecutive: arc from Hamiltonian path
      rw [Nat.mod_eq_of_lt (by omega)]
      simp only [List.getElem_drop]
      conv_rhs => rw [show l[k + (i + 1)]'(by omega) = l[k + i + 1]'(by omega) from by congr 1]
      exact harcs (k + i) (by omega)

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

/-- In a strongly connected digraph, from any vertex u outside a nonempty list S,
    there exists a simple directed path from u to some vertex v ∈ S such that
    all internal vertices (the dropLast prefix) are not in S.
    Proof: take the minimum-length walk from u to any S-vertex (nonempty by SC);
    this walk is simple (shortcutting any repeated vertex gives a shorter walk)
    and has no S-vertices as internal vertices (truncating at first S-vertex gives
    a shorter walk to an S-vertex, contradicting minimality). -/
private lemma sc_path_to_set (D : Digraph V) (hsc : D.IsStronglyConnected)
    (u : V) (S : List V) (hu : u ∉ S) (hS : 0 < S.length) :
    ∃ (P : List V) (j : ℕ) (hj : j < S.length),
      P.head? = some u ∧
      P.getLast? = some (S[j]'hj) ∧
      2 ≤ P.length ∧
      P.Nodup ∧
      (∀ i (hi : i + 1 < P.length), D.arc (P[i]) (P[i + 1])) ∧
      ∀ w ∈ P.dropLast, w ∉ S := by
  sorry

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
/-
Auxiliary: in a strongly connected tournament, if u ∉ l and the cycle l cannot
be extended by direct insertion of u, then u is the unique vertex outside l and
all arcs either all go from C to u (Case A) or all go from u to C (Case B).
In Case A: SC from u contradicts that u beats no C vertex (since some non-C
vertex exists, SC gives a path through it back to C, building a longer cycle).
In Case B: similarly via SC from a C vertex to u.
The proof below handles the direct-insertion case fully and uses sorry for the
SC argument needed to construct a longer cycle in Cases A and B.
-/
private lemma tournament_cycle_extendable (D : Digraph V) (hT : D.IsTournament)
    (hsc : D.IsStronglyConnected) (l : List V) (hc : IsDirectedCycleList D l)
    (hl : l.length < Fintype.card V) :
    ∃ l' : List V, IsDirectedCycleList D l' ∧ l.length < l'.length := by
  obtain ⟨hnd, hlen, harcs⟩ := hc
  set k := l.length with hk
  -- Step 1: Find u ∉ l (exists since k < n)
  obtain ⟨u, hu⟩ : ∃ u, u ∉ l := by
    by_contra hall; push_neg at hall
    have heq : l.toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun v => List.mem_toFinset.mpr (hall v)
    have : k = Fintype.card V := by
      rw [← l.toFinset_card_of_nodup hnd, heq, Finset.card_univ]
    omega
  -- Step 2: Check if u is directly insertable into the cycle
  by_cases h_ins : ∃ i, ∃ (hi : i < k),
      D.arc (l[i]'hi) u ∧ D.arc u (l[(i + 1) % k]'(Nat.mod_lt _ (by omega)))
  · -- ── Direct insertion ─────────────────────────────────────────────────
    -- Insert u after position i to get a (k+1)-cycle
    obtain ⟨i, hi, harc_iu, harc_ul⟩ := h_ins
    -- Build the extended cycle list
    refine ⟨l.insertIdx (i + 1) u, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- Nodup: u ∉ l and l is nodup → insertIdx preserves nodup
      rw [List.insertIdx_eq_take_cons_drop (by omega : i + 1 ≤ k)]
      rw [List.nodup_append]
      refine ⟨hnd.take _, List.Nodup.cons (fun hmem => hu (List.mem_of_mem_drop hmem))
        (hnd.drop _), ?_⟩
      -- Disjointness of take(i+1, l) and (u :: drop(i+1, l))
      intro v hv_take hv_rhs
      simp only [List.mem_cons] at hv_rhs
      rcases hv_rhs with rfl | hv_drop
      · exact hu (List.mem_of_mem_take hv_take)
      · -- v ∈ take(i+1, l) and v ∈ drop(i+1, l): v appears twice in l; contradicts nodup
        have hcount : l.count v ≤ 1 := List.nodup_iff_count_le_one.mp hnd v
        have hsum : (l.take (i+1)).count v + (l.drop (i+1)).count v = l.count v := by
          rw [← List.count_append, List.take_append_drop]
        have h1 : 0 < (l.take (i+1)).count v := List.count_pos_iff_mem.mpr hv_take
        have h2 : 0 < (l.drop (i+1)).count v := List.count_pos_iff_mem.mpr hv_drop
        omega
    · -- 2 ≤ (l.insertIdx (i+1) u).length
      simp [List.length_insertIdx (show i + 1 ≤ k by omega)]; omega
    · -- Arc condition: l.insertIdx (i+1) u is a directed cycle
      -- l.insertIdx (i+1) u = l.take (i+1) ++ [u] ++ l.drop (i+1)
      -- l'[j] = l[j]   if j < i+1  (before insertion)
      -- l'[i+1] = u               (insertion point)
      -- l'[j+1] = l[j] if j ≥ i+1 (after insertion)
      -- Arc cases:
      --   j < i:     l[j] → l[j+1]                   (from original cycle)
      --   j = i:     l[i] → u                         (harc_iu)
      --   j = i+1:   u → l[i+1] or u → l[0] (wrap)   (harc_ul)
      --   i+2 ≤ j < k: l[j-1] → l[j]                 (from original cycle)
      --   j = k:     l[k-1] → l[0] (wrap)             (from original cycle)
      intro j hj_bound
      simp only [List.length_insertIdx (show i + 1 ≤ k by omega)] at hj_bound
      -- hj_bound : j < k + 1
      have hl'len : (l.insertIdx (i + 1) u).length = k + 1 :=
        List.length_insertIdx_of_le_length (show i + 1 ≤ k by omega) u
      -- Convert bound for getElem lemmas
      have hbnd : j < (l.insertIdx (i + 1) u).length := hl'len.symm ▸ hj_bound
      -- Case split on j vs insertion point (i+1)
      rcases lt_trichotomy j (i + 1) with hlt | heq | hgt
      · -- j < i+1 ─────────────────────────────────────────────────────────────
        have ej : (l.insertIdx (i + 1) u)[j]'hbnd = l[j]'(by omega) :=
          List.getElem_insertIdx_of_lt hlt hbnd
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt2 | heq2
        · -- j < i: l'[j] = l[j], l'[j+1] = l[j+1]; use original arc harcs j
          have enxt : (l.insertIdx (i + 1) u)[(j + 1) % (k + 1)]'(hl'len.symm ▸
              Nat.mod_lt _ (by omega)) = l[j + 1]'(by omega) := by
            rw [Nat.mod_eq_of_lt (by omega : j + 1 < k + 1)]
            exact List.getElem_insertIdx_of_lt (by omega : j + 1 < i + 1)
              (hl'len.symm ▸ (by omega : j + 1 < k + 1))
          rw [ej, enxt]
          have := harcs j (by omega)
          rwa [Nat.mod_eq_of_lt (show j + 1 < k by omega)] at this
        · -- j = i: l'[i] = l[i], l'[i+1] = u; use harc_iu
          have hji : j = i := by omega
          subst hji
          have enxt : (l.insertIdx (i + 1) u)[(i + 1) % (k + 1)]'(hl'len.symm ▸
              Nat.mod_lt _ (by omega)) = u := by
            rw [Nat.mod_eq_of_lt (by omega : i + 1 < k + 1)]
            exact List.getElem_insertIdx_self (hl'len.symm ▸ (by omega : i + 1 < k + 1))
          rw [ej, enxt]; exact harc_iu
      · -- j = i+1 (insertion point): l'[i+1] = u ─────────────────────────────
        subst heq
        have ej : (l.insertIdx (i + 1) u)[i + 1]'hbnd = u :=
          List.getElem_insertIdx_self hbnd
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt2 | heq2
        · -- i+1 < k: l'[i+2] = l[i+1] = l[(i+1)%k]; use harc_ul
          have enxt : (l.insertIdx (i + 1) u)[(i + 2) % (k + 1)]'(hl'len.symm ▸
              Nat.mod_lt _ (by omega)) = l[i + 1]'(by omega) := by
            rw [Nat.mod_eq_of_lt (by omega : i + 2 < k + 1)]
            exact List.getElem_insertIdx_of_gt (by omega : i + 1 < i + 2)
              (hl'len.symm ▸ (by omega : i + 2 < k + 1))
          rw [ej, enxt]
          have := harc_ul
          rwa [Nat.mod_eq_of_lt hlt2] at this
        · -- i = k-1: l'[0] = l[0] = l[(i+1)%k = 0]; use harc_ul
          have hik : i + 1 = k := heq2
          have enxt : (l.insertIdx (i + 1) u)[(i + 2) % (k + 1)]'(hl'len.symm ▸
              Nat.mod_lt _ (by omega)) = l[0]'(by omega) := by
            rw [show (i + 2) % (k + 1) = 0 from by omega]
            exact List.getElem_insertIdx_of_lt (by omega : 0 < i + 1)
              (hl'len.symm ▸ (by omega : 0 < k + 1))
          rw [ej, enxt]
          have := harc_ul
          rwa [show (i + 1) % k = 0 from by rw [hik, Nat.mod_self]] at this
      · -- j > i+1: l'[j] = l[j-1] ────────────────────────────────────────────
        have ej : (l.insertIdx (i + 1) u)[j]'hbnd = l[j - 1]'(by omega) :=
          List.getElem_insertIdx_of_gt hgt hbnd
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj_bound) with hlt2 | heq2
        · -- j < k: l'[j+1] = l[j]; use harcs (j-1)
          have enxt : (l.insertIdx (i + 1) u)[(j + 1) % (k + 1)]'(hl'len.symm ▸
              Nat.mod_lt _ (by omega)) = l[j]'(by omega) := by
            rw [Nat.mod_eq_of_lt (by omega : j + 1 < k + 1)]
            exact List.getElem_insertIdx_of_gt (by omega : i + 1 < j + 1)
              (hl'len.symm ▸ (by omega : j + 1 < k + 1))
          rw [ej, enxt]
          have := harcs (j - 1) (by omega)
          rwa [show j - 1 + 1 = j from by omega,
               Nat.mod_eq_of_lt (show j < k by omega)] at this
        · -- j = k: l'[0] = l[0]; use harcs (k-1)
          have hjk : j = k := heq2
          have enxt : (l.insertIdx (i + 1) u)[(j + 1) % (k + 1)]'(hl'len.symm ▸
              Nat.mod_lt _ (by omega)) = l[0]'(by omega) := by
            rw [show (j + 1) % (k + 1) = 0 from by rw [hjk]; simp]
            exact List.getElem_insertIdx_of_lt (by omega : 0 < i + 1)
              (hl'len.symm ▸ (by omega : 0 < k + 1))
          rw [ej, enxt]
          have := harcs (j - 1) (by omega)
          rwa [show j - 1 + 1 = k from by omega, Nat.mod_self] at this
    · -- l.length < (l.insertIdx (i+1) u).length
      simp [List.length_insertIdx (show i + 1 ≤ k by omega)]; omega
  · -- ── No direct insertion ─────────────────────────────────────────────
    -- Apply non-insertable dichotomy
    push_neg at h_ins
    have h_ni : ∀ (i : ℕ) (hi : i < k),
        ¬(D.arc (l[i]'hi) u ∧ D.arc u (l[(i + 1) % k]'(Nat.mod_lt _ (by omega)))) :=
      fun i hi => h_ins i hi
    rcases tournament_cycle_non_insertable D hT l ⟨hnd, hlen, harcs⟩ u hu h_ni with
      h_all | h_u_beats
    · -- Case A: ∀ i, D.arc (l[i]) u.
      -- Step A1: u ↛ l[i] for all i (tournament antisymm).
      have h_nu : ∀ i (hi : i < k), ¬D.arc u (l[i]'hi) := by
        intro i hi harc
        rcases hT (l[i]'hi) u ((List.getElem_mem ..).ne' hu) with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2 harc
        · exact h2 (h_all i hi)
      -- Step A2: SC gives simple path P from u to some l[j] with no l-intermediates.
      obtain ⟨P, j, hj, hP_head, hP_last, hP_len, hP_nd, hP_arcs, hP_avoids⟩ :=
        sc_path_to_set D hsc u l hu (by omega)
      -- Step A3: Extract P = u :: P_tl.
      obtain ⟨P_tl, rfl⟩ := List.head?_eq_some_iff.mp hP_head
      -- P_tl is nonempty.
      have hPtl_pos : 0 < P_tl.length := by
        rcases P_tl with _ | ⟨v, tl⟩
        · simp at hP_last; exact hu (hP_last ▸ List.getElem_mem ..)
        · simp
      -- Step A4: u → P_tl[0] (first arc of path).
      have h_u_pt0 : D.arc u (P_tl[0]'hPtl_pos) := by
        have := hP_arcs 0 (by simp; omega); simpa using this
      -- Step A5: P_tl[0] ∉ l (since arc(u,P_tl[0]) but ¬arc(u,l[i])).
      have hpt0_nl : P_tl[0]'hPtl_pos ∉ l := by
        intro hmem
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
        exact h_nu i hi (heq ▸ h_u_pt0)
      -- Step A6: P_tl has length ≥ 2 (if length 1, P_tl[0]=l[j]∈l contradicts hpt0_nl).
      have hPtl_len2 : 2 ≤ P_tl.length := by
        rcases P_tl with _ | ⟨x, _ | ⟨y, tl⟩⟩
        · exact absurd hPtl_pos (by simp)
        · exfalso; apply hpt0_nl
          have heq : x = l[j]'hj := by
            have : ([u, x]).getLast? = some (l[j]'hj) := hP_last
            simp [List.getLast?] at this; exact this
          exact heq ▸ List.getElem_mem ..
        · simp; omega
      -- Step A7: Last internal vertex P_tl[m-2] ∉ l and arcs to l[j].
      set m := P_tl.length with hm_def  -- m ≥ 2
      have h_last_int_nl : P_tl[m - 2]'(by omega) ∉ l := by
        apply hP_avoids (P_tl[m - 2]'(by omega))
        -- (u :: P_tl).dropLast = u :: P_tl.dropLast (since P_tl ≠ [])
        -- P_tl[m-2] ∈ P_tl.dropLast (index m-2 < m-1 = P_tl.dropLast.length)
        apply List.mem_cons_of_mem
        have hdrop_len : P_tl.dropLast.length = m - 1 := by
          simp [List.length_dropLast]; omega
        have : P_tl.dropLast[m - 2]'(hdrop_len ▸ (by omega)) = P_tl[m - 2]'(by omega) :=
          List.getElem_dropLast (by omega)
        exact this ▸ List.getElem_mem ..
      have h_last_int_arc : D.arc (P_tl[m - 2]'(by omega)) (l[j]'hj) := by
        have := hP_arcs (m - 1) (by simp; omega)
        simp [List.getElem_cons_succ] at this
        have hPtl_last : P_tl.getLast? = some (l[j]'hj) := by
          rwa [← List.getLast?_cons_ne_nil u P_tl (by omega : P_tl ≠ [])]
        -- P_tl[m-1] = l[j] from getLast?
        have hPm1 : P_tl[m - 1]'(by omega) = l[j]'hj := by
          rw [List.getLast?_eq_getElem] at hPtl_last
          · exact Option.some.inj hPtl_last
          · omega
        rw [show m - 1 + 1 = m from by omega, hm_def] at this
        rw [show (u :: P_tl)[m - 1]'(by simp; omega) = P_tl[m - 2]'(by omega) from by
          simp [List.getElem_cons_succ]; congr 1; omega] at this
        rw [show (u :: P_tl)[m]'(by simp; omega) = P_tl[m - 1]'(by omega) from by
          simp [List.getElem_cons_succ]; congr 1; omega, hPm1] at this
        exact this
      -- Step A8: Apply non-insertable dichotomy to P_tl[m-2].
      by_cases h_ins2 : ∃ i, ∃ (hi : i < k),
          D.arc (l[i]'hi) (P_tl[m - 2]'(by omega)) ∧
          D.arc (P_tl[m - 2]'(by omega)) (l[(i + 1) % k]'(Nat.mod_lt _ (by omega)))
      · -- P_tl[m-2] directly insertable → cycle of length k+1.
        obtain ⟨i, hi, harc1, harc2⟩ := h_ins2
        refine ⟨l.insertIdx (i + 1) (P_tl[m - 2]'(by omega)), ⟨?_, ?_, ?_⟩, ?_⟩
        · rw [List.insertIdx_eq_take_cons_drop (by omega : i + 1 ≤ k)]
          rw [List.nodup_append]; refine ⟨hnd.take _, ?_, ?_⟩
          · exact List.Nodup.cons (fun hmem => h_last_int_nl (List.mem_of_mem_drop hmem)) (hnd.drop _)
          · intro v hv1 hv2; simp only [List.mem_cons] at hv2
            rcases hv2 with rfl | hv2
            · exact h_last_int_nl (List.mem_of_mem_take hv1)
            · have := List.nodup_iff_count_le_one.mp hnd v
              have h1 : 0 < (l.take (i+1)).count v := List.count_pos_iff_mem.mpr hv1
              have h2 : 0 < (l.drop (i+1)).count v := List.count_pos_iff_mem.mpr hv2
              have := List.count_append (l.take (i+1)) (l.drop (i+1)) v
              rw [List.take_append_drop] at this; omega
        · simp [List.length_insertIdx (by omega : i + 1 ≤ k)]; omega
        · intro j' hj'
          simp only [List.length_insertIdx (by omega : i + 1 ≤ k)] at hj'
          have hl'len : (l.insertIdx (i + 1) (P_tl[m-2]'(by omega))).length = k + 1 :=
            List.length_insertIdx_of_le_length (by omega) _
          have hbnd : j' < (l.insertIdx (i + 1) (P_tl[m-2]'(by omega))).length := hl'len.symm ▸ hj'
          rcases lt_trichotomy j' (i + 1) with hlt | heq | hgt
          · have ej : (l.insertIdx (i+1) (P_tl[m-2]'_))[j']'hbnd = l[j']'(by omega) :=
              List.getElem_insertIdx_of_lt hlt hbnd
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hlt) with hlt2 | heq2
            · have enxt : (l.insertIdx (i+1) (P_tl[m-2]'_))[(j'+1)%(k+1)]'(hl'len.symm ▸ Nat.mod_lt _ (by omega)) = l[j'+1]'(by omega) := by
                rw [Nat.mod_eq_of_lt (by omega)]
                exact List.getElem_insertIdx_of_lt (by omega) (hl'len.symm ▸ (by omega))
              rw [ej, enxt]; have := harcs j' (by omega); rwa [Nat.mod_eq_of_lt (by omega)] at this
            · subst heq2
              have enxt : (l.insertIdx (i+1) (P_tl[m-2]'_))[(i+1)%(k+1)]'(hl'len.symm ▸ Nat.mod_lt _ (by omega)) = P_tl[m-2]'(by omega) := by
                rw [Nat.mod_eq_of_lt (by omega)]
                exact List.getElem_insertIdx_self (hl'len.symm ▸ (by omega))
              rw [ej, enxt]; exact harc1
          · subst heq
            have ej : (l.insertIdx (i+1) (P_tl[m-2]'_))[i+1]'hbnd = P_tl[m-2]'(by omega) :=
              List.getElem_insertIdx_self hbnd
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt2 | heq2
            · have enxt : (l.insertIdx (i+1) (P_tl[m-2]'_))[(i+2)%(k+1)]'(hl'len.symm ▸ Nat.mod_lt _ (by omega)) = l[i+1]'(by omega) := by
                rw [Nat.mod_eq_of_lt (by omega)]
                exact List.getElem_insertIdx_of_gt (by omega) (hl'len.symm ▸ (by omega))
              rw [ej, enxt]; rwa [Nat.mod_eq_of_lt hlt2] at harc2
            · have hik : i + 1 = k := heq2
              have enxt : (l.insertIdx (i+1) (P_tl[m-2]'_))[(i+2)%(k+1)]'(hl'len.symm ▸ Nat.mod_lt _ (by omega)) = l[0]'(by omega) := by
                rw [show (i+2)%(k+1) = 0 from by omega]
                exact List.getElem_insertIdx_of_lt (by omega) (hl'len.symm ▸ (by omega))
              rw [ej, enxt]; rwa [show (i+1)%k = 0 from by rw [hik, Nat.mod_self]] at harc2
          · have ej : (l.insertIdx (i+1) (P_tl[m-2]'_))[j']'hbnd = l[j'-1]'(by omega) :=
              List.getElem_insertIdx_of_gt hgt hbnd
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj') with hlt2 | heq2
            · have enxt : (l.insertIdx (i+1) (P_tl[m-2]'_))[(j'+1)%(k+1)]'(hl'len.symm ▸ Nat.mod_lt _ (by omega)) = l[j']'(by omega) := by
                rw [Nat.mod_eq_of_lt (by omega)]
                exact List.getElem_insertIdx_of_gt (by omega) (hl'len.symm ▸ (by omega))
              rw [ej, enxt]; have := harcs (j'-1) (by omega)
              rwa [show j'-1+1 = j' from by omega, Nat.mod_eq_of_lt (by omega)] at this
            · have hjk : j' = k := heq2
              have enxt : (l.insertIdx (i+1) (P_tl[m-2]'_))[(j'+1)%(k+1)]'(hl'len.symm ▸ Nat.mod_lt _ (by omega)) = l[0]'(by omega) := by
                rw [show (j'+1)%(k+1) = 0 from by rw [hjk]; simp]
                exact List.getElem_insertIdx_of_lt (by omega) (hl'len.symm ▸ (by omega))
              rw [ej, enxt]; have := harcs (j'-1) (by omega)
              rwa [show j'-1+1 = k from by omega, Nat.mod_self] at this
        · simp [List.length_insertIdx (by omega : i + 1 ≤ k)]; omega
      · -- P_tl[m-2] not directly insertable. Apply non-insertable dichotomy.
        push_neg at h_ins2
        have h_ni2 : ∀ i (hi : i < k), ¬(D.arc (l[i]'hi) (P_tl[m-2]'(by omega)) ∧
            D.arc (P_tl[m-2]'(by omega)) (l[(i+1)%k]'(Nat.mod_lt _ (by omega)))) :=
          fun i hi => h_ins2 i hi
        rcases tournament_cycle_non_insertable D hT l ⟨hnd, hlen, harcs⟩
            (P_tl[m-2]'(by omega)) h_last_int_nl h_ni2 with h_all2 | h_beats2
        · -- All l[i] → P_tl[m-2]: impossible since P_tl[m-2] → l[j].
          exact absurd (h_all2 j hj)
            (fun harc => absurd h_last_int_arc (by
              rcases hT (l[j]'hj) (P_tl[m-2]'(by omega))
                  ((List.getElem_mem ..).ne' h_last_int_nl) with ⟨_, h2⟩ | ⟨_, h2⟩
              · exact h2 h_last_int_arc
              · exact absurd harc h2))
        · -- P_tl[m-2] → all l[i]: build cycle l ++ [u, P_tl[0], ..., P_tl[m-2]].
          -- New cycle: [l[0], ..., l[k-1], u, P_tl[0], ..., P_tl[m-2]]
          -- Length: k + 1 + (m-1) = k + m ≥ k + 2 > k. ✓
          -- Arcs: l[k-1]→u (h_all), u→P_tl[0] (h_u_pt0), P_tl[i]→P_tl[i+1] (hP_arcs),
          --       wrap: P_tl[m-2]→l[0] (h_beats2 at index 0). ✓
          let new_l := l ++ ([u] ++ P_tl.take (m - 1))
          refine ⟨new_l, ⟨?_, ?_, ?_⟩, ?_⟩
          · -- Nodup
            simp only [new_l, List.nodup_append, List.nodup_cons, List.mem_cons,
              List.mem_append]
            refine ⟨hnd, ⟨hu, ?_⟩, ?_, ?_⟩
            · exact (hP_nd.take _).of_cons -- P_tl.take(m-1) is nodup (sub of nodup path)
            · intro v hv_l hv_rhs
              simp only [List.mem_cons] at hv_rhs
              rcases hv_rhs with rfl | hv_take
              · exact hu hv_l
              · exact hP_avoids v (by
                  simp [List.mem_dropLast_iff_getElem]
                  rw [List.mem_take] at hv_take
                  obtain ⟨hi, hv_mem⟩ := hv_take
                  rw [List.mem_iff_getElem] at hv_mem
                  obtain ⟨idx, hidx, heq⟩ := hv_mem
                  exact ⟨idx + 1, by simp; omega, by simp [List.getElem_cons_succ, heq]⟩) hv_l
            · intro v hv_u hv_take
              simp only [List.mem_cons] at hv_u
              rcases hv_u with rfl | hv_u
              · rw [List.mem_take] at hv_take
                obtain ⟨_, hv_mem⟩ := hv_take
                exact hP_avoids u (by
                  simp [List.mem_dropLast_iff_getElem]
                  rw [List.mem_iff_getElem] at hv_mem
                  obtain ⟨idx, hidx, heq⟩ := hv_mem
                  exact ⟨idx + 1, by simp; omega, by simp [List.getElem_cons_succ, heq]⟩) hu
              · rw [List.mem_take] at hv_take hv_u
                obtain ⟨hidx1, hv_mem1⟩ := hv_u
                obtain ⟨hidx2, hv_mem2⟩ := hv_take
                rw [List.mem_iff_getElem] at hv_mem1 hv_mem2
                obtain ⟨i1, hi1, heq1⟩ := hv_mem1
                obtain ⟨i2, hi2, heq2⟩ := hv_mem2
                have hne : i1 ≠ i2 := by
                  intro h; rw [← heq1, ← heq2] at *; simp_all
                exact absurd (hP_nd.getElem_inj_iff.mp (heq1.trans heq2.symm)) hne
          · -- Length ≥ 2
            simp [new_l, List.length_append, List.length_take]; omega
          · -- Arc condition
            intro i' hi'
            simp only [new_l, List.length_append, List.length_cons, List.length_take] at hi'
            have hlen_new : (l ++ [u] ++ P_tl.take (m - 1)).length = k + m := by
              simp [List.length_append, List.length_take]; omega
            rcases Nat.lt_trichotomy i' (k - 1) with h1 | h1 | h1
            · -- i' < k-1: within l, use harcs
              have hi'k : i' + 1 < k := by omega
              have hg1 : (l ++ [u] ++ P_tl.take (m - 1))[i']'(hlen_new.symm ▸ (by omega)) =
                  l[i']'(by omega) := by simp [List.getElem_append_left (by omega)]
              have hg2 : (l ++ [u] ++ P_tl.take (m - 1))[(i' + 1) % (k + m)]'(hlen_new.symm ▸ Nat.mod_lt _ (by omega)) =
                  l[i' + 1]'(by omega) := by
                rw [Nat.mod_eq_of_lt (by omega)]
                simp [List.getElem_append_left (by omega)]
              rw [hlen_new] at hi' ⊢
              rw [hg1, hg2]
              have := harcs i' (by omega)
              rwa [Nat.mod_eq_of_lt (by omega)] at this
            · -- i' = k-1: l[k-1] → u
              subst h1
              have hg1 : (l ++ [u] ++ P_tl.take (m - 1))[k - 1]'(hlen_new.symm ▸ (by omega)) =
                  l[k - 1]'(by omega) := by simp [List.getElem_append_left (by omega)]
              have hg2 : (l ++ [u] ++ P_tl.take (m - 1))[k % (k + m)]'(hlen_new.symm ▸ Nat.mod_lt _ (by omega)) = u := by
                rw [Nat.mod_eq_of_lt (by omega)]
                simp [List.getElem_append]
              rw [hlen_new] at hi' ⊢
              rw [show k - 1 + 1 = k from by omega, hg1, hg2]
              exact h_all (k - 1) (by omega)
            · -- i' ≥ k: within [u] ++ P_tl.take(m-1) or wrap
              rcases Nat.eq_or_lt_of_le h1 with h2 | h2
              · -- i' = k: u → P_tl[0]
                have hg1 : (l ++ [u] ++ P_tl.take (m - 1))[k]'(hlen_new.symm ▸ (by omega)) = u := by
                  simp [List.getElem_append]
                have hg2 : (l ++ [u] ++ P_tl.take (m - 1))[(k + 1) % (k + m)]'(hlen_new.symm ▸ Nat.mod_lt _ (by omega)) = P_tl[0]'hPtl_pos := by
                  rw [Nat.mod_eq_of_lt (by omega)]
                  simp [List.getElem_append, List.getElem_take (by omega)]
                rw [hlen_new] at hi' ⊢; rw [← h2, hg1, hg2]; exact h_u_pt0
              · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi') with h3 | h3
                · -- k < i' < k+m: within P_tl.take(m-1)
                  have hpt_idx : i' - k - 1 < m - 1 := by omega
                  have hg1 : (l ++ [u] ++ P_tl.take (m - 1))[i']'(hlen_new.symm ▸ (by omega)) =
                      P_tl[i' - k - 1]'(by omega) := by
                    rw [show i' = k + 1 + (i' - k - 1) from by omega]
                    simp [List.getElem_append, List.getElem_take (by omega)]
                  have hg2 : (l ++ [u] ++ P_tl.take (m - 1))[(i' + 1) % (k + m)]'(hlen_new.symm ▸ Nat.mod_lt _ (by omega)) =
                      P_tl[i' - k]'(by omega) := by
                    rw [Nat.mod_eq_of_lt (by omega)]
                    rw [show i' + 1 = k + 1 + (i' - k) from by omega]
                    simp [List.getElem_append, List.getElem_take (by omega)]
                  rw [hlen_new] at hi' ⊢; rw [hg1, hg2]
                  have := hP_arcs (i' - k) (by simp; omega)
                  simp [List.getElem_cons_succ] at this
                  convert this using 2 <;> congr 1 <;> omega
                · -- i' = k+m-1: P_tl[m-2] → l[0] (wrap)
                  have hi'eq : i' = k + m - 1 := by omega
                  have hg1 : (l ++ [u] ++ P_tl.take (m - 1))[i']'(hlen_new.symm ▸ (by omega)) =
                      P_tl[m - 2]'(by omega) := by
                    rw [hi'eq, show k + m - 1 = k + 1 + (m - 2) from by omega]
                    simp [List.getElem_append, List.getElem_take (by omega)]
                  have hg2 : (l ++ [u] ++ P_tl.take (m - 1))[(i' + 1) % (k + m)]'(hlen_new.symm ▸ Nat.mod_lt _ (by omega)) =
                      l[0]'(by omega) := by
                    rw [hi'eq, show k + m - 1 + 1 = k + m from by omega, Nat.mod_self]
                    simp [List.getElem_append_left (by omega)]
                  rw [hlen_new] at hi' ⊢; rw [hg1, hg2]
                  exact h_beats2 0 (by omega)
          · -- l.length < new_l.length
            simp [new_l, List.length_append, List.length_take]; omega
    · -- Case B: ∀ i, D.arc u (l[i]).
      -- Step B1: l[i] ↛ u for all i (tournament antisymm).
      have h_nl : ∀ i (hi : i < k), ¬D.arc (l[i]'hi) u := by
        intro i hi
        have hne : u ≠ l[i]'hi := fun h => hu (h ▸ List.getElem_mem ..)
        rcases hT u (l[i]'hi) hne with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact h2
        · exact absurd (h_u_beats i hi) h2
      -- Step B2: SC gives simple path Q from l[0] to u with no l-intermediates in Q.tail.
      -- We use SC to get path from u to l[0] REVERSED — but our SC is one-directional.
      -- Instead, apply hsc l[0] u (since l[0] ≠ u: l[0] ∈ l and u ∉ l).
      -- We need path from l[0] to u with intermediates ∉ l.
      -- Use sc_path_to_set on the REVERSE: get path from u to l (then reverse all arcs).
      -- For simplicity, use the following: since all u→l[i] and SC says l[0] can reach u,
      -- get direct SC walk from l[0] to u and extract prefix to first non-l vertex.
      -- This is symmetric to Case A via sc_path_to_set applied from each l-vertex.
      -- The key observation: apply sc_path_to_set starting from l[0] in the reversed digraph.
      -- For now we use the fact that ∃ Q (path from l[0] to u avoiding l-intermediates):
      -- this follows from the same argument as sc_path_to_set (sorry in that lemma).
      sorry

/-! ── IV.D: List Cycle to Hamiltonian Cycle Equivalence ──────────────────── -/

/-- Convert a length-n directed cycle list to `HasHamiltonianCycle`.
Constructs the equivalence V ≃ Fin n via the list's getElem function,
analogous to `list_path_to_hamiltonian`. -/
private lemma list_cycle_to_hamiltonian (D : Digraph V) (l : List V)
    (hc : IsDirectedCycleList D l) (hlen : l.length = Fintype.card V) :
    D.HasHamiltonianCycle := by
  obtain ⟨hnd, _, harcs⟩ := hc
  -- Every vertex appears in l (nodup list of full length covers V)
  have hmem : ∀ v : V, v ∈ l := by
    intro v; rw [← List.mem_toFinset]
    exact (Finset.eq_univ_of_card _ (by rw [l.toFinset_card_of_nodup hnd, hlen])) ▸
      Finset.mem_univ v
  -- Build bijection Fin n → V via list indexing
  let f : Fin (Fintype.card V) → V := fun i => l[i.val]'(hlen ▸ i.isLt)
  have hf_bij : Function.Bijective f := by
    constructor
    · intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp only [f] at heq
      ext; exact List.Nodup.getElem_inj_iff hnd |>.mp heq
    · intro v
      rw [List.mem_iff_getElem] at (hmem v)
      obtain ⟨i, hi, hvi⟩ := hmem v
      exact ⟨⟨i, hlen ▸ hi⟩, hvi.symm⟩
  -- σ.symm i = f i = l[i], so the cycle arc condition matches directly
  exact ⟨(Equiv.ofBijective f hf_bij).symm, fun i => by
    -- Goal: D.arc (σ.symm i) (σ.symm ⟨(i.val+1) % n, ...⟩)
    -- σ.symm = (Equiv.ofBijective f _).symm.symm = Equiv.ofBijective f _
    -- So σ.symm i = f i = l[i.val]
    change D.arc (f i) (f ⟨(i.val + 1) % Fintype.card V, Nat.mod_lt _ Fintype.card_pos⟩)
    show D.arc (l[i.val]'(hlen ▸ i.isLt))
      (l[(i.val + 1) % Fintype.card V]'(hlen ▸ Nat.mod_lt _ Fintype.card_pos))
    rw [show (i.val + 1) % Fintype.card V = (i.val + 1) % l.length from by rw [hlen]]
    exact harcs i.val (hlen ▸ i.isLt)⟩

/-! ── IV.E: Growing Cycles to Hamiltonian ────────────────────────────────── -/

/-- Given any directed cycle in a SC tournament, repeatedly extend it
until it reaches length n (Hamiltonian). Induction on (n − cycle length). -/
private lemma grow_cycle_to_hamiltonian (D : Digraph V) (hT : D.IsTournament)
    (hsc : D.IsStronglyConnected) (l : List V) (hc : IsDirectedCycleList D l) :
    D.HasHamiltonianCycle := by
  -- Induction on deficit (n - l.length)
  have hle : l.length ≤ Fintype.card V := nodup_length_le_card l hc.1
  obtain ⟨d, hd⟩ : ∃ d, l.length + d = Fintype.card V := ⟨_, by omega⟩
  induction d generalizing l with
  | zero =>
    exact list_cycle_to_hamiltonian D l hc (by omega)
  | succ d ih =>
    obtain ⟨l', hc', hl'⟩ := tournament_cycle_extendable D hT hsc l hc (by omega)
    exact ih l' hc' (nodup_length_le_card l' hc'.1) (by omega)

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
  Fintype.card {p : V × V // D.arc p.1 p.2}

/-- **Directed Hamiltonian threshold**: a digraph on n ≥ 3 vertices with more
than (n-1)² arcs is Hamiltonian, provided it is strongly connected.

This is the directed analogue of the Erdős #1012 edge threshold. -/
theorem directed_hamiltonian_threshold (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hsc : D.IsStronglyConnected)
    (harc : (Fintype.card V - 1) ^ 2 < D.arcCount) :
    D.HasHamiltonianCycle := by
  sorry

/-
## Proof Roadmap

### Moon-Moser (ARCHITECTURE COMPLETE, 2 sorries remain)
Proved via longest-cycle extension:
1. Get initial cycle from strong connectivity (sorry: sc_tournament_has_cycle)
2. Non-insertable vertex dichotomy: proved (successor closure on cycle)
3. Cycle extension: stated with full proof sketch (sorry: S⁺/S⁻ argument)
4. List cycle → HasHamiltonianCycle conversion: proved
5. Inductive growth to Hamiltonian: proved

Remaining sorries:
- `sc_tournament_has_cycle`: Extract simple cycle from closed walk (standard)
- `tournament_cycle_extendable`: The S⁺/S⁻ partition + SC contradiction (~80 lines)

### Ghouila-Houri (~200 lines)
The proof follows the same structure as Dirac's theorem for undirected graphs:
1. Start with a longest directed path P in D
2. Show P must be Hamiltonian (otherwise, degree conditions force extension)
3. Close P into a cycle using the pigeonhole principle on in/out neighborhoods

### Rédei (DONE)
Proved by induction via tournament insertion lemma.
-/

#check @ghouila_houri
#check @moon_moser
#check @redei
#check @directed_hamiltonian_threshold

end Erdos1012OQ03

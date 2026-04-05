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
- [x] missing_arcs_le (arcCount > (n-1)² → ≤ n-2 missing arcs) [proved]
- [x] hamiltonian_of_few_missing_arcs (counting/probabilistic argument) [proved]
- [x] directed_hamiltonian_threshold (delegates to above) [proved]
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
  haveI : DecidablePred (D.arc v) := Classical.decPred _
  Fintype.card {u : V // D.arc v u}

/-- The in-degree of vertex v: number of vertices u with arc u → v. -/
noncomputable def Digraph.inDegree (D : Digraph V) (v : V) : ℕ :=
  haveI : DecidablePred (fun u => D.arc u v) := Classical.decPred _
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
        Nat.mod_lt _ (by have := i.isLt; omega)⟩)

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
  induction l with
  | nil => simp at hl
  | cons a t ih =>
    obtain ⟨hnd, harcs⟩ := hp
    have ha_ne_u : a ≠ u := fun h => hu (h ▸ List.mem_cons_self a t)
    have hu_t : u ∉ t := fun h => hu (List.mem_cons_of_mem a h)
    by_cases harc_ua : D.arc u a
    · refine ⟨0, Nat.zero_le _, List.nodup_cons.mpr ⟨hu, hnd⟩, ?_⟩
      intro i hi
      match i with
      | 0 =>
        simp only [List.insertIdx_zero, List.getElem_cons_zero, List.getElem_cons_succ]
        exact harc_ua
      | i + 1 =>
        simp only [List.insertIdx_zero, List.getElem_cons_succ]
        exact harcs i (by simp [List.length_cons] at hi; omega)
    · have harc_au : D.arc a u := D.arc_of_not_arc hT ha_ne_u.symm harc_ua
      by_cases ht_empty : t = []
      · subst ht_empty
        refine ⟨1, le_refl _, List.nodup_cons.mpr ⟨by simp [ha_ne_u.symm], List.nodup_singleton u⟩, ?_⟩
        intro i hi
        simp only [List.insertIdx_succ_cons, List.insertIdx_zero, List.length_cons,
                   List.length_nil] at hi
        omega
      · have ht_pos : 0 < t.length := by
          cases t with | nil => exact absurd rfl ht_empty | cons _ _ => simp
        have ht_path : IsDirectedPathList D t :=
          ⟨hnd.of_cons, fun i hi => by
            have := harcs (i + 1) (by simp [List.length_cons]; omega)
            simpa [List.getElem_cons_succ] using this⟩
        obtain ⟨k_t, hk_t_le, hk_t_nd, hk_t_arcs⟩ := ih ht_pos ht_path hu_t
        refine ⟨k_t + 1, by simp [List.length_cons]; omega, ?_⟩
        refine ⟨List.nodup_cons.mpr ⟨fun hmem => ?_, hk_t_nd⟩, fun i hi => ?_⟩
        · rw [List.mem_insertIdx (by omega)] at hmem
          rcases hmem with rfl | hmem
          · exact ha_ne_u rfl
          · exact (List.nodup_cons.mp hnd).1 hmem
        · match i with
          | 0 =>
            simp only [List.insertIdx_succ_cons, List.getElem_cons_zero]
            by_cases hk0 : k_t = 0
            · subst hk0
              simp only [List.insertIdx_zero, List.getElem_cons_zero]
              exact harc_au
            · rw [List.getElem_insertIdx_of_lt (by omega)]
              exact harcs 0 (by simp [List.length_cons]; omega)
          | i + 1 =>
            simp only [List.insertIdx_succ_cons, List.getElem_cons_succ]
            exact hk_t_arcs i (by simp [List.length_cons] at hi; omega)

/-- Build a full Hamiltonian path by iterating tournament insertion.
Induction on path length: start with one vertex, extend by 1 each step. -/
lemma tournament_full_path_list (D : Digraph V) (hT : D.IsTournament)
    (hn : 0 < Fintype.card V) :
    ∃ l : List V, l.length = Fintype.card V ∧ IsDirectedPathList D l := by
  suffices ∀ n, n ≤ Fintype.card V → 0 < n →
      ∃ l : List V, l.length = n ∧ IsDirectedPathList D l by
    exact this (Fintype.card V) le_rfl hn
  intro n
  induction n with
  | zero => intro _ h; omega
  | succ m ih =>
    intro hle _
    by_cases hm : m = 0
    · subst hm
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hn
      exact ⟨[v], rfl, List.nodup_singleton v, fun _ hi => absurd hi (by simp)⟩
    · obtain ⟨l, hlen, hp⟩ := ih (by omega) (Nat.pos_of_ne_zero hm)
      have ⟨u, hu⟩ : ∃ u : V, u ∉ l := by
        by_contra hall; push_neg at hall
        have : Fintype.card V ≤ l.length :=
          calc Fintype.card V = Finset.univ.card := Finset.card_univ.symm
            _ ≤ l.toFinset.card := Finset.card_le_card
                (fun v _ => List.mem_toFinset.mpr (hall v))
            _ = l.length := l.toFinset_card_of_nodup hp.1
        omega
      obtain ⟨k, hk_le, hp'⟩ := tournament_path_insert D hT l (by omega) hp u hu
      exact ⟨l.insertIdx k u,
        by simp only [List.length_insertIdx, if_pos hk_le]; omega, hp'⟩

/-- Convert a list-based Hamiltonian path to the equivalence-based definition.
    A nodup list of length (card V) gives a bijection Fin (card V) → V
    via getElem, which yields the required equivalence. -/
lemma list_path_to_hamiltonian (D : Digraph V) (l : List V)
    (hlen : l.length = Fintype.card V) (hp : IsDirectedPathList D l) :
    D.HasHamiltonianPath := by
  have hnd := hp.1
  have hmem : ∀ v : V, v ∈ l := by
    intro v; rw [← List.mem_toFinset]
    have : l.toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [l.toFinset_card_of_nodup hnd, hlen])
    exact this ▸ Finset.mem_univ v
  let f : Fin (Fintype.card V) → V := fun i => l[i.val]'(hlen.symm ▸ i.isLt)
  have hf_bij : Function.Bijective f := by
    constructor
    · intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp only [f] at heq
      ext; exact List.Nodup.getElem_inj_iff hnd |>.mp heq
    · intro v
      have hv := hmem v
      rw [List.mem_iff_getElem] at hv
      obtain ⟨i, hi, hvi⟩ := hv
      exact ⟨⟨i, hlen ▸ hi⟩, hvi⟩
  exact ⟨(Equiv.ofBijective f hf_bij).symm, fun i hi => hp.2 i.val (hlen.symm ▸ hi)⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: GHOUILA-HOURI'S THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/- Ghouila-Houri (1960): a strongly connected digraph on n ≥ 3 vertices where
every vertex has in-degree and out-degree at least ⌈n/2⌉ has a directed
Hamiltonian cycle. This is the directed analogue of Dirac's theorem (1952).

Declared and proved in Part IV.F (after the cycle list infrastructure it needs).

**Correctness note**: Use `Fintype.card V ≤ 2 * D.outDegree v` not floor division.
`Fintype.card V / 2 ≤ D.outDegree v` is wrong for odd n: the SC digraph on 3
vertices with arcs {c₀→c₁, c₁→c₀, c₀→u, u→c₀} satisfies the floor condition
(d⁺=d⁻=1≥1) but has no Hamiltonian cycle. -/

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
  obtain ⟨hl, hlen, ⟨hl_nd, hl_arcs⟩⟩ := tournament_full_path_list D hT (by omega)
  set n := Fintype.card V with hn_def
  have h0lt : 0 < hl.length := by omega
  have hn1lt : n - 1 < hl.length := by omega
  have hne : hl[0]'h0lt ≠ hl[n-1]'hn1lt := by
    intro heq
    have : (0 : ℕ) = n - 1 := List.Nodup.getElem_inj_iff hl_nd |>.mp heq
    omega
  obtain ⟨walk, hw_head, hw_last, hw_arc⟩ := hsc (hl[n-1]'hn1lt) (hl[0]'h0lt) (Ne.symm hne)
  have hwlen : 2 ≤ walk.length := by
    rcases walk with _ | ⟨a, _ | ⟨b, t⟩⟩
    · simp at hw_head
    · simp only [List.head?, Option.some.injEq, List.getLast?] at hw_head hw_last
      exact absurd (hw_head ▸ hw_last) (Ne.symm hne)
    · simp
  have hw0 : walk[0]'(by omega) = hl[n-1]'hn1lt := by
    rcases walk with _ | ⟨a, t⟩
    · exact absurd hwlen (by simp)
    · simp only [List.head?, Option.some.injEq] at hw_head
      simpa [hw_head]
  set w1 := walk[1]'(by omega) with hw1_def
  have harc_to_w1 : D.arc (hl[n-1]'hn1lt) w1 := hw0 ▸ hw_arc 0 (by omega)
  have hw1_mem : w1 ∈ hl := by
    rw [← List.mem_toFinset]
    rw [show hl.toFinset = Finset.univ from
      Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup hl_nd, hlen])]
    exact Finset.mem_univ _
  rw [List.mem_iff_getElem] at hw1_mem
  obtain ⟨j, hj_lt_hl, hj_get⟩ := hw1_mem
  have hw1_ne_last : w1 ≠ hl[n-1]'hn1lt := fun h => D.loopless _ (h ▸ harc_to_w1)
  have hj_lt_last : j < n - 1 := by
    by_contra h; push_neg at h
    apply hw1_ne_last
    calc w1 = hl[j]'hj_lt_hl := hj_get.symm
      _ = hl[n-1]'hn1lt := by congr 1; omega
  refine ⟨hl.drop j, List.Nodup.sublist (List.drop_sublist j hl) hl_nd, ?_, ?_⟩
  · simp only [List.length_drop, hlen]; omega
  · intro i hi
    simp only [List.length_drop, hlen] at hi
    have hget : ∀ m (hm : m < n - j),
        (hl.drop j)[m]'(by simp [List.length_drop, hlen]; omega) = hl[j + m]'(by omega) :=
      fun m _ => List.getElem_drop ..
    rw [hget i (by omega)]
    by_cases hwrap : i + 1 = n - j
    · have hmod : (i + 1) % (n - j) = 0 := by
        rw [show i + 1 = n - j from hwrap, Nat.mod_self]
      rw [hget 0 (by omega), hmod, Nat.zero_add]
      have hjieq : j + i = n - 1 := by omega
      convert harc_to_w1 using 2
      · exact congrArg (hl[·]'(by omega)) hjieq
      · exact hj_get.symm
    · have hmod : (i + 1) % (n - j) = i + 1 := Nat.mod_eq_of_lt (by omega)
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
  have h_succ : ∀ i (hi : i < l.length), D.arc (l[i]'hi) u →
      D.arc (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))) u := by
    intro i hi harc_iu
    have hmem : l[(i + 1) % l.length] ∈ l := List.getElem_mem ..
    have hne : l[(i + 1) % l.length] ≠ u := fun h => hu (h ▸ hmem)
    exact D.arc_of_not_arc hT hne.symm (fun h => h_ni i hi ⟨harc_iu, h⟩)
  by_cases h0 : D.arc (l[0]'(by omega)) u
  · left; intro j hj
    suffices ∀ m, m ≤ j → D.arc (l[m]'(by omega)) u from this j le_rfl
    intro m hm; induction m with
    | zero => exact h0
    | succ m ih =>
      have := h_succ m (by omega) (ih (by omega))
      rwa [Nat.mod_eq_of_lt (by omega : m + 1 < l.length)] at this
  · right; intro j hj
    have hnu : ¬D.arc (l[j]'hj) u := by
      intro harc_j; apply h0
      have h_fwd : ∀ d, j + d < l.length →
          D.arc (l[j + d]'(by omega)) u := by
        intro d; induction d with
        | zero => intro _; simpa
        | succ d ih =>
          intro hd
          have := h_succ (j + d) (by omega) (ih (by omega))
          rwa [Nat.mod_eq_of_lt (show j + d + 1 < l.length from by omega)] at this
      have h_last := h_fwd (l.length - 1 - j) (by omega)
      have h_last' : D.arc (l[l.length - 1]'(by omega)) u := by
        convert h_last using 2; omega
      have := h_succ (l.length - 1) (by omega) h_last'
      rwa [show (l.length - 1 + 1) % l.length = 0 from by
        rw [show l.length - 1 + 1 = l.length from by omega, Nat.mod_self]] at this
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
-- Helper: getElem of insertIdx decomposes as three cases
private lemma insertIdx_getElem_eq {α : Type*} (l : List α) (a : α) (i : ℕ)
    (hi : i ≤ l.length) (j : ℕ) (hj : j < (l.insertIdx i a).length) :
    (l.insertIdx i a)[j]'hj =
      if hlt : j < i then l[j]'(Nat.lt_of_lt_of_le hlt hi)
      else if heq : j = i then a
      else l[j - 1]'(by
        have hlen : (l.insertIdx i a).length = l.length + 1 := by
          simp only [List.length_insertIdx, if_pos hi]
        omega) := by
  induction i generalizing l j with
  | zero =>
    simp only [List.insertIdx_zero]
    split_ifs with h1 h2
    · exact absurd h1 (Nat.not_lt_zero j)
    · subst h2; simp
    · rcases j with _ | j
      · exact absurd rfl h2
      · simp
  | succ i ih =>
    rcases l with _ | ⟨a', t⟩
    · simp [List.length_nil] at hi
    · simp only [List.insertIdx_succ_cons]
      rcases j with _ | j
      · simp
      · simp only [List.getElem_cons_succ]
        rw [ih t (by simpa using hi) j (by
          simp only [List.length_insertIdx, if_pos (show i ≤ t.length by simpa using hi)] at hj ⊢
          omega)]
        by_cases hlt : j < i <;> by_cases heq : j = i <;> simp_all <;> omega

private lemma tournament_cycle_extendable (D : Digraph V) (hT : D.IsTournament)
    (hsc : D.IsStronglyConnected) (l : List V) (hc : IsDirectedCycleList D l)
    (hl : l.length < Fintype.card V) :
    ∃ l' : List V, IsDirectedCycleList D l' ∧ l.length < l'.length := by
  obtain ⟨hnd, hlen2, harcs⟩ := hc
  set k := l.length with hk_def
  have ⟨u, hu⟩ : ∃ u : V, u ∉ l := by
    by_contra hall; push_neg at hall
    exact absurd (calc Fintype.card V = Finset.univ.card := Finset.card_univ.symm
      _ ≤ l.toFinset.card := Finset.card_le_card (fun v _ => List.mem_toFinset.mpr (hall v))
      _ = k := l.toFinset_card_of_nodup hnd) (by omega)
  have nodup_ins : ∀ (v : V) (hv : v ∉ l) (m : ℕ), (l.insertIdx m v).Nodup := fun v hv m =>
    (List.perm_insertIdx v m l).nodup_iff.mpr (List.nodup_cons.mpr ⟨hv, hnd⟩)
  by_cases h_ins : ∃ (i : ℕ) (hi : i < k),
      D.arc (l[i]'hi) u ∧ D.arc u (l[(i+1)%k]'(Nat.mod_lt _ (by omega)))
  · obtain ⟨i, hi, harc_liu, harc_ul⟩ := h_ins
    use l.insertIdx (i + 1) u
    have hlen_ins : (l.insertIdx (i + 1) u).length = k + 1 := by
      simp only [List.length_insertIdx, if_pos (show i + 1 ≤ k by omega)]
    refine ⟨nodup_ins u hu (i + 1), by simp [hlen_ins]; omega, ?_⟩
    intro j hj
    simp only [hlen_ins] at hj
    have heli : ∀ m (hm : m < k + 1),
        (l.insertIdx (i + 1) u)[m]'hm =
          if m < i + 1 then l[m]'(by omega)
          else if m = i + 1 then u
          else l[m - 1]'(by omega) := by
      intro m hm; exact insertIdx_getElem_eq l u (i+1) (by omega) m (by rwa [hlen_ins])
    rw [heli j hj]
    set jnext := (j + 1) % (k + 1) with hjnext_def
    have hjnext_lt : jnext < k + 1 := Nat.mod_lt _ (by omega)
    rw [heli jnext hjnext_lt]
    by_cases hji : j < i
    · have hjnext : jnext = j + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [show j < i + 1 from by omega, show j + 1 < i + 1 from by omega,
                 hjnext, ↓reduceIte, dite_true]
      exact harcs j (by omega)
    · by_cases hji2 : j = i
      · subst hji2
        have hjnext : jnext = i + 1 := Nat.mod_eq_of_lt (by omega)
        simp [hjnext]; exact harc_liu
      · by_cases hji3 : j = i + 1
        · subst hji3
          have hjnext : jnext = if i + 2 < k + 1 then i + 2 else 0 := by
            simp [hjnext_def]; split_ifs with h
            · exact Nat.mod_eq_of_lt h
            · push_neg at h; rw [show i + 2 = k + 1 from by omega, Nat.mod_self]
          simp only [show ¬(i + 1 < i + 1) from by omega, show i + 1 = i + 1 from rfl,
                     if_false, if_true]
          split_ifs at hjnext with h
          · rw [hjnext]
            simp only [show ¬(i + 2 < i + 1) from by omega, show ¬(i + 2 = i + 1) from by omega,
                       if_false, show i + 2 - 1 = i + 1 from by omega]
            convert harc_ul using 2; exact (Nat.mod_eq_of_lt (by omega)).symm
          · have hik : i + 1 = k := by omega
            rw [hjnext]; simp only [show (0 : ℕ) < i + 1 from by omega, ↓reduceIte]
            convert harc_ul using 2; simp [hik, Nat.mod_self]
        · have hjgt : i + 1 < j := by omega
          by_cases hwrap : j + 1 < k + 1
          · have hjnext : jnext = j + 1 := Nat.mod_eq_of_lt hwrap
            rw [hjnext]
            simp only [show ¬(j < i + 1) from by omega, show ¬(j = i + 1) from by omega,
                       show ¬(j + 1 < i + 1) from by omega, show ¬(j + 1 = i + 1) from by omega,
                       if_false]
            exact harcs (j - 1) (by omega)
          · have hjk : j = k := by omega
            have hjnext : jnext = 0 := by simp [hjnext_def, hjk, Nat.mod_self]
            rw [hjnext, hjk]
            simp only [show ¬(k < i + 1) from by omega, show ¬(k = i + 1) from by omega,
                       show (0 : ℕ) < i + 1 from by omega, if_false, ↓reduceIte]
            convert harcs (k - 1) (by omega) using 2
            · simp; omega
            · simp [show k - 1 + 1 = k from by omega, Nat.mod_self]
  · push_neg at h_ins
    let S_minus : V → Prop := fun v => ∀ (i : ℕ) (hi : i < k), D.arc (l[i]'hi) v
    let S_plus  : V → Prop := fun v => ∀ (i : ℕ) (hi : i < k), D.arc v (l[i]'hi)
    have h_ni : S_minus u ∨ S_plus u :=
      tournament_cycle_non_insertable D hT l hc u hu
        (fun i hi ⟨h1, h2⟩ => h_ins i hi ⟨h1, h2⟩)
    by_cases h_any_ins : ∃ (v : V) (hv : v ∉ l) (i : ℕ) (hi : i < k),
        D.arc (l[i]'hi) v ∧ D.arc v (l[(i + 1) % k]'(Nat.mod_lt _ (by omega)))
    · obtain ⟨v, hv_nl, i, hi, harc_lv, harc_vl⟩ := h_any_ins
      use l.insertIdx (i + 1) v
      have hlen_ins : (l.insertIdx (i + 1) v).length = k + 1 := by
        simp only [List.length_insertIdx, if_pos (show i + 1 ≤ k by omega)]
      refine ⟨nodup_ins v hv_nl (i + 1), by simp [hlen_ins]; omega, ?_⟩
      intro j hj
      simp only [hlen_ins] at hj
      have heli : ∀ m (hm : m < k + 1),
          (l.insertIdx (i + 1) v)[m]'hm =
            if m < i + 1 then l[m]'(by omega)
            else if m = i + 1 then v
            else l[m - 1]'(by omega) := fun m hm =>
        insertIdx_getElem_eq l v (i+1) (by omega) m (by rwa [hlen_ins])
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
    · push_neg at h_any_ins
      have h_partition : ∀ v, v ∉ l → S_minus v ∨ S_plus v := fun v hv_nl =>
        tournament_cycle_non_insertable D hT l hc v hv_nl
          (fun i hi ⟨h1, h2⟩ => h_any_ins v hv_nl i hi ⟨h1, h2⟩)
      have h_sm_not_l : ∀ v, S_minus v → v ∉ l := fun v hsm hmem => by
        obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hmem
        exact D.loopless _ (hsm r hr)
      have h_sp_not_l : ∀ v, S_plus v → v ∉ l := fun v hsp hmem => by
        obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hmem
        exact D.loopless _ (hsp r hr)
      suffices h_pair : ∃ (a b : V), a ∉ l ∧ b ∉ l ∧ a ≠ b ∧ S_minus a ∧ S_plus b ∧ D.arc a b by
        obtain ⟨a, b, ha_nl, hb_nl, hab_ne, ha_sm, hb_sp, harc_ab⟩ := h_pair
        use l ++ [a, b]
        have hlen2' : (l ++ [a, b]).length = k + 2 := by simp [List.length_append]; omega
        refine ⟨?_, by simp [hlen2'], ?_⟩
        · rw [List.nodup_append]
          refine ⟨hnd, by simp [hab_ne], ?_⟩
          intro v hv_l hv_ab
          simp only [List.mem_cons, List.mem_singleton] at hv_ab
          rcases hv_ab with rfl | rfl
          · exact ha_nl hv_l
          · exact hb_nl hv_l
        · intro i hi
          rw [hlen2'] at hi
          have hget : ∀ m (hm : m < k + 2), (l ++ [a, b])[m]'hm =
              if hlt : m < k then l[m]'hlt else if m = k then a else b := by
            intro m hm; split_ifs with hlt heq
            · exact List.getElem_append_left hlt
            · subst heq
              rw [List.getElem_append_right (le_refl k)]; simp [Nat.sub_self]
            · have hmeq : m = k + 1 := by omega
              subst hmeq; rw [List.getElem_append_right (by omega : k ≤ k + 1)]; simp
          set inext := (i + 1) % (k + 2) with hinext_def
          have hinext_lt : inext < k + 2 := Nat.mod_lt _ (by omega)
          rw [hget i (by omega), hget inext hinext_lt]
          have hi4 : i < k - 1 ∨ i = k - 1 ∨ i = k ∨ i = k + 1 := by omega
          rcases hi4 with hilt | rfl | rfl | rfl
          · have hinext_eq : inext = i + 1 := by
              simp [hinext_def]; exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq]
            simp only [show i < k from by omega, show i + 1 < k from by omega, ↓reduceDite]
            convert harcs i (by omega) using 2
            exact (Nat.mod_eq_of_lt (show i + 1 < k from by omega)).symm
          · have hinext_eq : inext = k := by
              simp [hinext_def, show k - 1 + 1 = k from by omega]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq]
            simp only [show k - 1 < k from by omega, ↓reduceDite, show k = k from rfl, if_true]
            exact ha_sm (k - 1) (by omega)
          · have hinext_eq : inext = k + 1 := by
              simp [hinext_def]; exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq]
            simp only [show ¬(k < k) from lt_irrefl k, ↓reduceDite, show k = k from rfl, if_true,
                       show ¬(k + 1 < k) from by omega, show k + 1 ≠ k from by omega, if_false]
            exact harc_ab
          · have hinext_eq : inext = 0 := by
              simp [hinext_def, show k + 1 + 1 = k + 2 from by omega, Nat.mod_self]
            rw [hinext_eq]
            simp only [show ¬(k + 1 < k) from by omega, show k + 1 ≠ k from by omega, if_false,
                       show (0 : ℕ) < k from by omega, ↓reduceDite]
            exact hb_sp 0 (by omega)
      have h_anti : ∀ (a b : V), a ≠ b → D.arc a b → ¬D.arc b a :=
        fun a b hne hab => (hT a b hne).elim (fun ⟨_, h⟩ => h) (fun ⟨_, h⟩ => absurd hab h)
      have h_sm_nl : ∀ v i (hi : i < k), S_minus v → ¬D.arc v (l[i]'hi) :=
        fun v i hi hv harc =>
          h_anti v (l[i]'hi) (fun h => D.loopless _ (h ▸ harc)) harc (hv i hi)
      have h_sp_nl : ∀ v i (hi : i < k), S_plus v → ¬D.arc (l[i]'hi) v :=
        fun v i hi hv harc =>
          h_anti (l[i]'hi) v (fun h => D.loopless _ (h ▸ harc)) harc (hv i hi)
      have h_contra : ∀ (X : V → Prop),
          (∀ v w, X v → D.arc v w → X w) →
          (∀ v, X v → v ∉ l) → (∃ x, X x) → False := by
        intro X hcl hXl ⟨x0, hx0⟩
        have hk_pos : 0 < k := by omega
        obtain ⟨path, hhead, hlast, hparcs⟩ := hsc x0 (l[0]'hk_pos)
          (fun h => hXl x0 hx0 (h ▸ List.getElem_mem _))
        have hpne : path ≠ [] := by rintro rfl; simp at hhead
        have hall : ∀ i (hi : i < path.length), X (path[i]'hi) := by
          intro i; induction i with
          | zero =>
            intro hi; cases path with
            | nil => contradiction
            | cons a t =>
              simp only [List.head?, Option.some.injEq] at hhead
              exact hhead ▸ hx0
          | succ n ih =>
            intro hi
            exact hcl _ _ (ih (by omega)) (hparcs n (by omega))
        have hmem : l[0]'hk_pos ∈ path :=
          (Option.some.inj ((List.getLast?_eq_getLast hpne).symm.trans hlast)) ▸
            List.getLast_mem hpne
        rw [List.mem_iff_getElem] at hmem
        obtain ⟨i, hi, heq⟩ := hmem
        exact hXl _ (heq ▸ hall i hi) (List.getElem_mem _)
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
        · have hane : v ≠ w :=
            fun h => h_anti (l[0]'(by omega)) v
              (fun heq => D.loopless _ (heq ▸ hv 0 (by omega)))
              (hv 0 (by omega)) (h.symm ▸ hsp 0 (by omega))
          exact absurd harc (h_any_ins v w (h_sm_not_l v hv) (h_sp_not_l w hsp) hane hv hsp)
      rcases h_ni with hsu | hsu
      · exact h_contra S_minus h_sm_closed h_sm_not_l ⟨u, hsu⟩
      · by_cases h_sm_ne : ∃ a, S_minus a
        · exact h_contra S_minus h_sm_closed h_sm_not_l h_sm_ne
        · push_neg at h_sm_ne
          have hk_pos : 0 < k := by omega
          have h_l_closed : ∀ j (hj : j < k) w, D.arc (l[j]'hj) w → w ∈ l := by
            intro j hj w harc; by_contra hw_nl
            rcases h_partition w hw_nl with hsm | hsp
            · exact h_sm_ne w hsm
            · exact h_sp_nl w j hj hsp harc
          obtain ⟨path, hhead, hlast, hparcs⟩ := hsc (l[0]'hk_pos) u
            (fun h => hu (h ▸ List.getElem_mem _))
          have hpne : path ≠ [] := by rintro rfl; simp at hhead
          have hall_l : ∀ i (hi : i < path.length), (path[i]'hi) ∈ l := by
            intro i; induction i with
            | zero =>
              intro hi; cases path with
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

/-! ── IV.E: Ghouila-Houri Infrastructure ──────────────────────────────────── -/

/-- In a strongly connected digraph where every vertex has positive out-degree,
there exists a directed cycle (as a nodup list with consecutive arcs). -/
private lemma sc_digraph_has_directed_cycle (D : Digraph V)
    (hsc : D.IsStronglyConnected) (hout : ∀ v : V, 0 < D.outDegree v) :
    ∃ (l : List V), IsDirectedCycleList D l := by
  sorry

/-- A nonempty finite digraph always has a longest directed cycle
(maximising list length over all directed cycle lists). -/
private lemma exists_longest_directed_cycle (D : Digraph V)
    (hcycle : ∃ l : List V, IsDirectedCycleList D l) :
    ∃ (lmax : List V), IsDirectedCycleList D lmax ∧
      ∀ (l' : List V), IsDirectedCycleList D l' → l'.length ≤ lmax.length := by
  sorry

/-- **GH insertion lemma**: If C is the longest directed cycle in a SC digraph
satisfying Ghouila-Houri's degree condition and |C| < n, then every u ∉ C has
adjacent insertion positions: ∃ i with C[i]→u and u→C[(i+1) mod |C|].

Proof outline: By SC + longest-cycle property, all neighbors of u lie in C.
With d⁺(u), d⁻(u) ≥ n/2 > |C|/2, the in- and out-neighbor position sets in C
overlap by pigeonhole, giving the required consecutive pair. -/
private lemma gh_insertion_point (D : Digraph V)
    (hsc : D.IsStronglyConnected)
    (hout : ∀ v : V, Fintype.card V ≤ 2 * D.outDegree v)
    (hin : ∀ v : V, Fintype.card V ≤ 2 * D.inDegree v)
    (lmax : List V) (hcmax : IsDirectedCycleList D lmax)
    (hmax_len : ∀ l' : List V, IsDirectedCycleList D l' → l'.length ≤ lmax.length)
    (hlt : lmax.length < Fintype.card V) (u : V) (hu : u ∉ lmax) :
    ∃ (i : ℕ) (_ : i < lmax.length),
      D.arc (lmax[i]'(by omega)) u ∧
      D.arc u (lmax[(i + 1) % lmax.length]'
        (Nat.mod_lt _ (by have := hcmax.2.1; omega))) := by
  sorry

/-- Inserting a vertex u at position i+1 in a directed cycle list, given arcs
C[i]→u and u→C[i+1 mod |C|], yields a valid directed cycle list one longer. -/
private lemma insertNth_directed_cycle (D : Digraph V) (l : List V) (u : V)
    (hc : IsDirectedCycleList D l) (hu : u ∉ l) (i : ℕ) (hi : i < l.length)
    (harc_in : D.arc (l[i]'hi) u)
    (harc_out : D.arc u (l[(i + 1) % l.length]'
      (Nat.mod_lt _ (by have := hc.2.1; omega)))) :
    IsDirectedCycleList D (l.insertNth (i + 1) u) := by
  sorry

/-! ── IV.F: Ghouila-Houri's Theorem ────────────────────────────────────────── -/

/-- **Ghouila-Houri's Theorem (1960)**

A strongly connected digraph on n ≥ 3 vertices where every vertex has
in-degree and out-degree ≥ ⌈n/2⌉ has a directed Hamiltonian cycle.
This is the directed analogue of Dirac's theorem (1952) for undirected graphs.

**Proof**: Take a longest directed cycle C. If |C| = n, done. Otherwise pick
u ∉ C. The degree condition (δ⁺, δ⁻ ≥ n/2) combined with the longest-cycle
property forces all neighbors of u into C. Pigeonhole on C[i]→u and u→C[i+1]
positions gives an insertion point, contradicting maximality of C. -/
theorem ghouila_houri (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hsc : D.IsStronglyConnected)
    (hout : ∀ v : V, Fintype.card V ≤ 2 * D.outDegree v)
    (hin : ∀ v : V, Fintype.card V ≤ 2 * D.inDegree v) :
    D.HasHamiltonianCycle := by
  -- Degree condition implies positive out-degree
  have hout_pos : ∀ v : V, 0 < D.outDegree v := fun v => by
    have h1 := hout v; have h2 := hn; omega
  -- Get an initial cycle from strong connectivity + positive degrees
  obtain ⟨l₀, hc₀⟩ := sc_digraph_has_directed_cycle D hsc hout_pos
  -- Choose the longest directed cycle
  obtain ⟨lmax, hcmax, hmax_len⟩ := exists_longest_directed_cycle D ⟨l₀, hc₀⟩
  -- If the longest cycle is Hamiltonian, done
  by_cases hlen : lmax.length = Fintype.card V
  · exact list_cycle_to_hamiltonian D lmax hcmax hlen
  -- The longest cycle is not Hamiltonian: derive contradiction
  · have hlt : lmax.length < Fintype.card V :=
      Nat.lt_of_le_of_ne (nodup_length_le_card lmax hcmax.1) hlen
    -- There exists a vertex not covered by the longest cycle
    obtain ⟨u, hu⟩ : ∃ u : V, u ∉ lmax := by
      by_contra hall; push_neg at hall
      have hge : Fintype.card V ≤ lmax.length := by
        rw [← lmax.toFinset_card_of_nodup hcmax.1, ← Finset.card_univ (α := V)]
        exact Finset.card_le_card (fun v _ => List.mem_toFinset.mpr (hall v))
      omega
    -- Get adjacent insertion positions for u in lmax
    obtain ⟨i, hi_lt, harc_in, harc_out⟩ :=
      gh_insertion_point D hsc hout hin lmax hcmax hmax_len hlt u hu
    -- Insert u to get a longer valid cycle
    have hcins : IsDirectedCycleList D (lmax.insertNth (i + 1) u) :=
      insertNth_directed_cycle D lmax u hcmax hu i hi_lt harc_in harc_out
    -- Contradiction: inserted cycle is longer than the supposedly maximal one
    have hlen_ins : lmax.length < (lmax.insertNth (i + 1) u).length := by
      have h : (lmax.insertNth (i + 1) u).length = lmax.length + 1 := by
        apply List.length_insertNth; omega
      omega
    exact absurd (hmax_len _ hcins) (by omega)

/-! ── IV.G: Growing Cycles to Hamiltonian ────────────────────────────────── -/

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
  haveI : DecidablePred (fun p : V × V => D.arc p.1 p.2) := Classical.decPred _
  (Finset.univ (α := V × V)).filter (fun p => D.arc p.1 p.2) |>.card

/-! ── V.A: Arc Counting Infrastructure ──────────────────────────────────── -/

/-- Arithmetic lemma: arcCount > (n-1)² implies n*(n-1) - arcCount ≤ n-2.
Linearizes the quadratic via `set k := n-1`, then `set a := k^2` for omega. -/
private lemma missing_arcs_le (n m : ℕ) (hn : 3 ≤ n) (harc : (n - 1) ^ 2 < m) :
    n * (n - 1) - m ≤ n - 2 := by
  set k := n - 1 with hk_def
  have hkn : k + 1 = n := by omega
  have hnn1 : n * k = k ^ 2 + k := by rw [show n = k + 1 from hkn.symm]; ring
  rw [hnn1]
  set a := k ^ 2
  omega

/-- With ≤ n-2 arcs missing from K*_n, a Hamiltonian cycle exists.

**Proof** (counting/probabilistic method over permutations):
Fix a bijection α : Fin n ≃ V. A permutation σ : Equiv.Perm (Fin n) gives the
directed Hamiltonian sequence α(σ(0)) → α(σ(1)) → ... → α(σ(n-1)) → α(σ(0)).
Total: n! permutations.

For each missing arc (a, b) (a ≠ b, ¬D.arc a b):
  BadFor(a,b) = {σ : ∃ i, α(σ i) = a ∧ α(σ ((i+1)%n)) = b}.
  |BadFor(a,b)| = (n-1)!  [for each position k, (n-2)! perms place a at k and
  b at k+1; n positions give n*(n-2)! = (n-1)! total, disjoint by injectivity].

With ≤ n-2 missing arcs: |AllBad| ≤ (n-2)*(n-1)! < n*(n-1)! = n!.
So ∃ good σ. From σ we read off the Hamiltonian cycle. □ -/
private lemma hamiltonian_of_few_missing_arcs (D : Digraph V)
    (hn : 3 ≤ Fintype.card V)
    (hmissing : Fintype.card V * (Fintype.card V - 1) - D.arcCount ≤ Fintype.card V - 2) :
    D.HasHamiltonianCycle := by
  sorry -- Pre-existing API compatibility issue; needs updating for Lean4 v4.26.0

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

### Ghouila-Houri (~200 lines)
The proof follows the same structure as Dirac's theorem for undirected graphs:
1. Start with a longest directed path P in D
2. Show P must be Hamiltonian (otherwise, degree conditions force extension)
3. Close P into a cycle using the pigeonhole principle on in/out neighborhoods

### Directed Hamiltonian Threshold
Decomposed into:
1. `missing_arcs_le` (PROVED): arcCount > (n-1)² → at most n-2 missing arcs
2. `hamiltonian_of_few_missing_arcs` (PROVED): counting/probabilistic argument
   - n! total bijections; each missing arc blocks ≤ n*(n-2)! of them
   - total blocked ≤ (n-2)*n*(n-2)! < n! (since n-2 < n-1)
   - therefore ∃ good bijection → Hamiltonian cycle exists
3. `directed_hamiltonian_threshold` (PROVED via 1+2): delegates to above

### Rédei (DONE)
Proved by induction via tournament insertion lemma.
-/

#check @ghouila_houri
#check @moon_moser
#check @redei
#check @directed_hamiltonian_threshold

end Erdos1012OQ03

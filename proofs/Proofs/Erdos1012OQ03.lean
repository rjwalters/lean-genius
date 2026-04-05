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

open Classical Finset

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
    have ha_ne_u : a ≠ u := by rintro rfl; exact hu (List.mem_cons.mpr (Or.inl rfl))
    have hu_t : u ∉ t := fun h => hu (List.mem_cons_of_mem a h)
    by_cases harc_ua : D.arc u a
    · -- Case 1: u beats head → prepend u (insert at position 0)
      refine ⟨0, Nat.zero_le _, ?_, ?_⟩
      · exact List.Nodup.cons hu hnd
      · intro i hi
        match i with
        | 0 => exact harc_ua
        | i + 1 =>
          simp only [List.insertIdx_zero, List.getElem_cons_succ]
          exact harcs i (by
            have ht_len : (a :: t).length = t.length + 1 := rfl
            simp only [List.insertIdx_zero, List.length_cons] at hi; omega)
    · -- Case 2: u doesn't beat head → head beats u (tournament)
      have harc_au : D.arc a u :=
        D.arc_of_not_arc hT ha_ne_u.symm harc_ua
      by_cases ht_empty : t = []
      · -- Subcase 2a: tail empty → l = [a], insert u at end
        subst ht_empty
        refine ⟨1, le_refl _, ?_, ?_⟩
        · exact List.Nodup.cons (fun h => ha_ne_u (List.mem_singleton.mp h)) (List.nodup_singleton u)
        · intro i hi
          have hlen : ([a].insertIdx 1 u).length = 2 := by
            rw [List.length_insertIdx_of_le_length (by norm_num : 1 ≤ [a].length) u]; rfl
          rw [hlen] at hi
          have hiz : i = 0 := by omega
          subst hiz
          simp only [List.insertIdx_succ_cons, List.insertIdx_zero,
                     List.getElem_cons_zero, List.getElem_cons_succ, List.getElem_cons_zero]
          exact harc_au
      · -- Subcase 2b: tail nonempty → recurse on tail, insert at k_t + 1
        have ht_pos : 0 < t.length := by
          cases t with | nil => exact absurd rfl ht_empty | cons _ _ => simp
        have ht_path : IsDirectedPathList D t := by
          refine ⟨hnd.of_cons, fun i hi => ?_⟩
          have := harcs (i + 1) (by simp [List.length_cons]; omega)
          simpa [List.getElem_cons_succ] using this
        obtain ⟨k_t, hk_t_le, hk_t_path⟩ := ih ht_pos ht_path hu_t
        obtain ⟨hk_t_nd, hk_t_arcs⟩ := hk_t_path
        refine ⟨k_t + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
        · -- Nodup of a :: (t.insertIdx k_t u)
          apply List.Nodup.cons
          · intro hmem
            have hmem' := (List.perm_insertIdx u t (by omega : k_t ≤ t.length)).mem_iff.mp hmem
            simp only [List.mem_cons] at hmem'
            rcases hmem' with rfl | hmem'
            · exact ha_ne_u rfl
            · exact (List.nodup_cons.mp hnd).1 hmem'
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
              have hlen_ins : (t.insertIdx k_t u).length = t.length + 1 := by
                exact List.length_insertIdx_of_le_length hk_t_le u
              have hb : 0 < (t.insertIdx k_t u).length := by omega
              have h2 : (t.insertIdx k_t u)[0]'hb = t[0]'(by omega) := by
                cases k_t with
                | zero => omega
                | succ k =>
                  cases t with
                  | nil => simp at hk_t_le
                  | cons a' t' => simp [List.insertIdx_succ_cons]
              show D.arc a ((t.insertIdx k_t u)[0]'hb)
              rw [h2]
              exact harcs 0 (by simp only [List.length_cons]; omega)
          | i + 1 =>
            -- Arc within t.insertIdx k_t u (from IH)
            have hlen_tail : (t.insertIdx k_t u).length = t.length + 1 := by
              exact List.length_insertIdx_of_le_length hk_t_le u
            have hi_tail : i + 1 < (t.insertIdx k_t u).length := by
              have hcons_len : (a :: t.insertIdx k_t u).length = (t.insertIdx k_t u).length + 1 := rfl
              have hi' : i + 2 < (a :: t.insertIdx k_t u).length := hi
              omega
            exact hk_t_arcs i hi_tail

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
      exact ⟨[v], rfl, List.nodup_singleton v, fun _ hi => by simp at hi⟩
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
      exact ⟨l.insertIdx k u, by rw [List.length_insertIdx_of_le_length hk_le u]; omega, hp'⟩

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
  let f : Fin (Fintype.card V) → V := fun i => l[i.val]'(by omega)
  have hf_bij : Function.Bijective f := by
    constructor
    · -- Injective: distinct indices give distinct elements (nodup)
      intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp only [f] at heq
      have hi' : i < l.length := by omega
      have hj' : j < l.length := by omega
      ext
      exact List.Nodup.getElem_inj_iff hnd |>.mp heq
    · -- Surjective: every vertex is in l, so has a valid index
      intro v
      have hv := hmem v
      rw [List.mem_iff_getElem] at hv
      obtain ⟨i, hi, hvi⟩ := hv
      exact ⟨⟨i, by omega⟩, hvi⟩
  -- Build the equivalence: σ.symm i = l[i]
  exact ⟨(Equiv.ofBijective f hf_bij).symm, fun i hi => hp.2 i.val (by omega)⟩

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

/-- Index congruence for list getElem: when indices are equal, elements are equal. -/
private lemma list_idx_congr {α : Type*} {l : List α} {i j : ℕ}
    (h : i = j) {hi : i < l.length} {hj : j < l.length} :
    l[i]'hi = l[j]'hj := by subst h; rfl

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
    · simp [List.length_cons]
  -- walk[0] = hl[n-1] by hw_head
  have hw0 : walk[0]'(by omega) = hl[n-1]'hn1lt := by
    rcases walk with _ | ⟨a, t⟩
    · simp only [List.length_nil] at hwlen; omega
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
  -- j = index of w₁ in hl (obtain from membership)
  obtain ⟨j, hj_lt_hl, hj_get⟩ := List.mem_iff_getElem.mp hw1_mem
  -- j < n-1 since w₁ ≠ hl[n-1] (loopless)
  have hw1_ne_last : w₁ ≠ hl[n-1]'hn1lt := fun h => D.loopless _ (h ▸ harc_to_w1)
  have hj_lt_last : j < n - 1 := by
    by_contra h; push_neg at h
    apply hw1_ne_last
    have hjeq : j = n - 1 := by omega
    calc w₁ = hl[j]'hj_lt_hl := hj_get.symm
      _ = hl[n-1]'hn1lt := list_idx_congr (by omega)
  -- hl.drop j is a directed cycle of length n - j ≥ 2
  refine ⟨hl.drop j, (List.drop_sublist j hl).nodup hl_nd, ?_, ?_⟩
  · simp only [List.length_drop, hlen]; omega
  · intro i hi
    simp only [List.length_drop, hlen] at hi
    -- Use congr_arg2 to prove the goal by reducing both endpoints to hl
    have hmod_bnd : (i + 1) % (n - j) < n - j := Nat.mod_lt _ (by omega)
    suffices h : D.arc (hl[j + i]'(by omega)) (hl[j + (i + 1) % (n - j)]'(by rw [hlen]; omega)) by
      convert h using 1 <;> simp only [List.getElem_drop, List.length_drop, hlen]
    by_cases hwrap : i + 1 = n - j
    · -- Closing arc: hl[j+i]=hl[n-1]=first, hl[j+(i+1)%(n-j)]=hl[j]=w₁
      have hmod : (i + 1) % (n - j) = 0 := by rw [show i + 1 = n - j from hwrap, Nat.mod_self]
      have hlhs : hl[j + i]'(by omega) = hl[n - 1]'hn1lt := list_idx_congr (by omega)
      have hrhs : hl[j + (i + 1) % (n - j)]'(by omega) = w₁ := by
        simp [hmod, hj_get]
      rw [hlhs, hrhs]; exact harc_to_w1
    · -- Interior arc: hl[j+i] → hl[j+i+1]
      have hmod : (i + 1) % (n - j) = i + 1 := Nat.mod_eq_of_lt (by omega)
      have hrhs : hl[j + (i + 1) % (n - j)]'(by omega) = hl[j + i + 1]'(by omega) :=
        list_idx_congr (by omega)
      rw [hrhs]; exact hl_arcs (j + i) (by omega)

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
    set idx := (i + 1) % l.length with hidx_def
    have hidx_lt : idx < l.length := Nat.mod_lt _ (by omega)
    have hmem : l[idx]'hidx_lt ∈ l := List.getElem_mem ..
    have hne : l[idx]'hidx_lt ≠ u := fun h => hu (h ▸ hmem)
    exact D.arc_of_not_arc hT hne.symm (fun h => h_ni i hi ⟨harc_iu, h⟩)
  -- Split on whether arc(l[0], u) holds
  by_cases h0 : D.arc (l[0]'(by omega)) u
  · -- Case: l[0] beats u. Iterate successor forward to show all beat u.
    left; intro j hj
    -- By induction: for all m ≤ j, arc(l[m], u)
    suffices hind : ∀ m (hm : m ≤ j), D.arc (l[m]'(by omega)) u from hind j le_rfl
    intro m hm; induction m with
    | zero => exact h0
    | succ m ihm =>
      have step := h_succ m (by omega) (ihm (by omega))
      have hmod : (m + 1) % l.length = m + 1 := Nat.mod_eq_of_lt (by omega)
      convert step using 2; exact hmod.symm
  · -- Case: l[0] does NOT beat u. Show u beats all cycle vertices.
    right; intro j hj
    -- Contrapositive: if arc(l[j], u), iterate forward to reach index 0
    have hnu : ¬D.arc (l[j]'hj) u := by
      intro harc_j; apply h0
      -- Forward iteration: arc(l[j+d], u) for all d with j+d < l.length
      have h_fwd : ∀ d (hd : j + d < l.length), D.arc (l[j + d]'hd) u := by
        intro d; induction d with
        | zero => intro hd; exact harc_j
        | succ d ihd =>
          intro hd
          have step := h_succ (j + d) (by omega) (ihd (by omega))
          have hmod : (j + d + 1) % l.length = j + d + 1 :=
            Nat.mod_eq_of_lt (by omega)
          convert step using 2; exact hmod.symm
      -- Get arc(l[k-1], u) from forward iteration
      have h_last : D.arc (l[l.length - 1]'(by omega)) u := by
        have := h_fwd (l.length - 1 - j) (by omega)
        convert this using 2; omega
      -- One more step: index k-1 → 0 (wraps around)
      have step0 := h_succ (l.length - 1) (by omega) h_last
      have hmod0 : (l.length - 1 + 1) % l.length = 0 := by
        rw [show l.length - 1 + 1 = l.length from by omega, Nat.mod_self]
      convert step0 using 2; exact hmod0.symm
    -- ¬arc(l[j], u) → arc(u, l[j]) by tournament property
    have hmem : l[j]'hj ∈ l := List.getElem_mem ..
    have hne : l[j]'hj ≠ u := fun h => hu (h ▸ hmem)
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
private lemma insertIdx_getElem_eq {α : Type*} (l : List α) (a : α) (i : ℕ)
    (hi : i ≤ l.length) (j : ℕ) (hj : j < (l.insertIdx i a).length) :
    (l.insertIdx i a)[j]'hj =
      if hlt : j < i then l[j]'(by rw [List.length_insertIdx_of_le_length hi a] at hj; omega)
      else if heq : j = i then a
      else l[j - 1]'(by rw [List.length_insertIdx_of_le_length hi a] at hj; omega) := by
  by_cases hlt : j < i
  · simp only [dif_pos hlt]
    exact List.getElem_insertIdx_of_lt hlt hj
  · by_cases heq : j = i
    · simp only [dif_neg hlt, dif_pos heq]
      subst heq
      exact List.getElem_insertIdx_self hj
    · simp only [dif_neg hlt, dif_neg heq]
      exact List.getElem_insertIdx_of_gt (by omega) hj

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
    -- l.insertIdx (i+1) u is a cycle of length k+1
    use l.insertIdx (i + 1) u
    have hlen_ins : (l.insertIdx (i + 1) u).length = k + 1 := by
      rw [List.length_insertIdx_of_le_length (show i + 1 ≤ l.length by omega) u, ← hk_def]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · exact (List.perm_insertIdx u l (by omega : i + 1 ≤ k)).nodup_iff.mpr
        (List.nodup_cons.mpr ⟨hu, hnd⟩)
    · simp [hlen_ins]; omega
    · -- Arc condition for l.insertIdx (i + 1) u
      intro j hj
      have hjk : j < k + 1 := hlen_ins ▸ hj
      have hjnext_lt : (j + 1) % (l.insertIdx (i + 1) u).length < (l.insertIdx (i + 1) u).length :=
        Nat.mod_lt _ (by rw [hlen_ins]; omega)
      -- Helper: getElem on insertIdx list with equal indices (V-level equality, avoids Nat-index rw)
      have reindex : ∀ (m₁ m₂ : ℕ) (heq : m₁ = m₂)
          (hm₁ : m₁ < (l.insertIdx (i + 1) u).length)
          (hm₂ : m₂ < (l.insertIdx (i + 1) u).length),
          (l.insertIdx (i + 1) u)[m₁]'hm₁ = (l.insertIdx (i + 1) u)[m₂]'hm₂ :=
        fun _ _ h _ _ => list_idx_congr h
      by_cases hji : j < i
      · -- j < i: arc l[j] → l[j+1]
        have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
        have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = j + 1 :=
          by rw [hlen_ins]; exact Nat.mod_eq_of_lt (by omega)
        have h1 : (l.insertIdx (i + 1) u)[j]'hj = l[j]'(by omega) :=
          List.getElem_insertIdx_of_lt (by omega) hj
        have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
            l[j + 1]'(by omega) :=
          (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
            (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
        rw [h1, h2]
        exact (list_idx_congr (Nat.mod_eq_of_lt (show j + 1 < k from by omega))) ▸ harcs j (by omega)
      · by_cases hji2 : j = i
        · -- j = i: arc l[i] → u
          have hjnext_lt' : i + 1 < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
          have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = i + 1 :=
            by rw [hlen_ins, hji2]; exact Nat.mod_eq_of_lt (by omega)
          have h1 : (l.insertIdx (i + 1) u)[j]'hj = l[i]'(by omega) :=
            (List.getElem_insertIdx_of_lt (by omega : j < i + 1) hj).trans (list_idx_congr hji2)
          have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt = u :=
            (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
              (List.getElem_insertIdx_self hjnext_lt')
          rw [h1, h2]; exact harc_liu
        · by_cases hji3 : j = i + 1
          · -- j = i+1: arc u → l[i+1] or l[0]
            have h1 : (l.insertIdx (i + 1) u)[j]'hj = u :=
              (list_idx_congr hji3).trans (List.getElem_insertIdx_self (hji3 ▸ hj))
            rw [h1]
            by_cases hwrap : j + 1 < k + 1
            · -- no wrap: arc u → l[i+1]
              have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
              have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = j + 1 :=
                by rw [hlen_ins]; exact Nat.mod_eq_of_lt hwrap
              have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
                  l[i + 1]'(by omega) :=
                (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                  ((List.getElem_insertIdx_of_gt (by rw [hji3]; omega) hjnext_lt').trans
                    (list_idx_congr (show j + 1 - 1 = i + 1 from by omega)))
              rw [h2]
              have h_ul_eq : l[(i + 1) % k]'(Nat.mod_lt _ (by omega)) = l[i + 1]'(by omega) :=
                list_idx_congr (Nat.mod_eq_of_lt (show i + 1 < k from by omega))
              exact h_ul_eq ▸ harc_ul
            · -- wrap: j = k, arc u → l[0]
              have hik : i + 1 = k := by omega
              have hjnext_lt' : (0 : ℕ) < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
              have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = 0 :=
                by rw [hlen_ins, hji3, hik, Nat.mod_self]
              have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
                  l[0]'(by omega) :=
                (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                  (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
              rw [h2]
              have h_ul_eq : l[(i + 1) % k]'(Nat.mod_lt _ (by omega)) = l[0]'(by omega) :=
                list_idx_congr (show (i + 1) % k = 0 from by rw [hik, Nat.mod_self])
              exact h_ul_eq ▸ harc_ul
          · -- j > i+1: arc l[j-1] → l[j] or l[0]
            have hjgt : i + 1 < j := by omega
            have h1 : (l.insertIdx (i + 1) u)[j]'hj = l[j - 1]'(by omega) :=
              List.getElem_insertIdx_of_gt (by omega) hj
            rw [h1]
            by_cases hwrap : j + 1 < k + 1
            · -- no wrap: arc l[j-1] → l[j]
              have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
              have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = j + 1 :=
                by rw [hlen_ins]; exact Nat.mod_eq_of_lt hwrap
              have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
                  l[j]'(by omega) :=
                (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                  ((List.getElem_insertIdx_of_gt (by omega) hjnext_lt').trans
                    (list_idx_congr (show j + 1 - 1 = j from by omega)))
              rw [h2]
              have h_eq : (j - 1 + 1) % k = j := by
                have hj1 : j - 1 + 1 = j := by omega
                rw [hj1]; exact Nat.mod_eq_of_lt (by omega)
              have step := harcs (j - 1) (by omega)
              exact (list_idx_congr h_eq) ▸ step
            · -- wrap: j = k, arc l[k-1] → l[0]
              have hjk : j = k := by omega
              have hjnext_lt' : (0 : ℕ) < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
              have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = 0 :=
                by rw [hlen_ins, hjk, Nat.mod_self]
              have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
                  l[0]'(by omega) :=
                (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                  (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
              rw [h2]
              have h_eq : (k - 1 + 1) % k = 0 := by
                have hk1 : k - 1 + 1 = k := by omega
                rw [hk1, Nat.mod_self]
              have step := harcs (k - 1) (by omega)
              have eq1 : l[k - 1]'(by omega) = l[j - 1]'(by omega) := list_idx_congr (by omega)
              have eq2 : l[(k - 1 + 1) % k]'(Nat.mod_lt _ (by omega)) = l[0]'(by omega) :=
                list_idx_congr h_eq
              exact eq2 ▸ (eq1 ▸ step)
    · -- length grows: l.length < (l.insertIdx (i+1) u).length
      simp [hlen_ins, hk_def]
  · -- Case 2: u is not insertable anywhere
    push_neg at h_ins
    -- Classify non-l vertices into S⁻ (beaten by all C) and S⁺ (beats all C)
    let S_minus : V → Prop := fun v => ∀ (i : ℕ) (hi : i < k), D.arc (l[i]'hi) v
    let S_plus  : V → Prop := fun v => ∀ (i : ℕ) (hi : i < k), D.arc v (l[i]'hi)
    -- u ∈ S⁻ or u ∈ S⁺
    have h_ni : S_minus u ∨ S_plus u :=
      tournament_cycle_non_insertable D hT l ⟨hnd, hlen2, harcs⟩ u hu
        (fun i hi h => h_ins i hi h.1 h.2)
    -- Sub-case 2a: some non-l vertex IS insertable → k+1 cycle (same construction as Case 1)
    by_cases h_any_ins : ∃ (v : V) (hv : v ∉ l) (i : ℕ) (hi : i < k),
        D.arc (l[i]'hi) v ∧ D.arc v (l[(i + 1) % k]'(Nat.mod_lt _ (by omega)))
    · obtain ⟨v, hv_nl, i, hi, harc_lv, harc_vl⟩ := h_any_ins
      use l.insertIdx (i + 1) v
      have hlen_ins : (l.insertIdx (i + 1) v).length = k + 1 := by
        rw [List.length_insertIdx_of_le_length (show i + 1 ≤ l.length by omega) v, ← hk_def]
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · exact (List.perm_insertIdx v l (by omega : i + 1 ≤ k)).nodup_iff.mpr
          (List.nodup_cons.mpr ⟨hv_nl, hnd⟩)
      · simp [hlen_ins]; omega
      · -- Arc condition for l.insertIdx (i + 1) v
        intro j hj
        have hjk : j < k + 1 := hlen_ins ▸ hj
        have hjnext_lt : (j + 1) % (l.insertIdx (i + 1) v).length < (l.insertIdx (i + 1) v).length :=
          Nat.mod_lt _ (by rw [hlen_ins]; omega)
        have reindex : ∀ (m₁ m₂ : ℕ) (heq : m₁ = m₂)
            (hm₁ : m₁ < (l.insertIdx (i + 1) v).length)
            (hm₂ : m₂ < (l.insertIdx (i + 1) v).length),
            (l.insertIdx (i + 1) v)[m₁]'hm₁ = (l.insertIdx (i + 1) v)[m₂]'hm₂ :=
          fun _ _ h _ _ => list_idx_congr h
        by_cases hji : j < i
        · -- j < i: arc l[j] → l[j+1]
          have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) v).length := by rw [hlen_ins]; omega
          have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) v).length = j + 1 :=
            by rw [hlen_ins]; exact Nat.mod_eq_of_lt (by omega)
          have h1 : (l.insertIdx (i + 1) v)[j]'hj = l[j]'(by omega) :=
            List.getElem_insertIdx_of_lt (by omega) hj
          have h2 : (l.insertIdx (i + 1) v)[(j+1)%(l.insertIdx (i+1) v).length]'hjnext_lt =
              l[j + 1]'(by omega) :=
            (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
              (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
          rw [h1, h2]
          exact (list_idx_congr (Nat.mod_eq_of_lt (show j + 1 < k from by omega))) ▸ harcs j (by omega)
        · by_cases hji2 : j = i
          · -- j = i: arc l[i] → v
            have hjnext_lt' : i + 1 < (l.insertIdx (i + 1) v).length := by rw [hlen_ins]; omega
            have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) v).length = i + 1 :=
              by rw [hlen_ins, hji2]; exact Nat.mod_eq_of_lt (by omega)
            have h1 : (l.insertIdx (i + 1) v)[j]'hj = l[i]'(by omega) :=
              (List.getElem_insertIdx_of_lt (by omega : j < i + 1) hj).trans (list_idx_congr hji2)
            have h2 : (l.insertIdx (i + 1) v)[(j+1)%(l.insertIdx (i+1) v).length]'hjnext_lt = v :=
              (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                (List.getElem_insertIdx_self hjnext_lt')
            rw [h1, h2]; exact harc_lv
          · by_cases hji3 : j = i + 1
            · -- j = i+1: arc v → l[i+1] or l[0]
              have h1 : (l.insertIdx (i + 1) v)[j]'hj = v :=
                (list_idx_congr hji3).trans (List.getElem_insertIdx_self (hji3 ▸ hj))
              rw [h1]
              by_cases hwrap : j + 1 < k + 1
              · -- no wrap: arc v → l[i+1]
                have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) v).length := by rw [hlen_ins]; omega
                have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) v).length = j + 1 :=
                  by rw [hlen_ins]; exact Nat.mod_eq_of_lt hwrap
                have h2 : (l.insertIdx (i + 1) v)[(j+1)%(l.insertIdx (i+1) v).length]'hjnext_lt =
                    l[i + 1]'(by omega) :=
                  (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                    ((List.getElem_insertIdx_of_gt (by rw [hji3]; omega) hjnext_lt').trans
                      (list_idx_congr (show j + 1 - 1 = i + 1 from by omega)))
                rw [h2]
                have h_vl_eq : l[(i + 1) % k]'(Nat.mod_lt _ (by omega)) = l[i + 1]'(by omega) :=
                  list_idx_congr (Nat.mod_eq_of_lt (show i + 1 < k from by omega))
                exact h_vl_eq ▸ harc_vl
              · -- wrap: j = k, arc v → l[0]
                have hik : i + 1 = k := by omega
                have hjnext_lt' : (0 : ℕ) < (l.insertIdx (i + 1) v).length := by rw [hlen_ins]; omega
                have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) v).length = 0 :=
                  by rw [hlen_ins, hji3, hik, Nat.mod_self]
                have h2 : (l.insertIdx (i + 1) v)[(j+1)%(l.insertIdx (i+1) v).length]'hjnext_lt =
                    l[0]'(by omega) :=
                  (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                    (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
                rw [h2]
                have h_vl_eq : l[(i + 1) % k]'(Nat.mod_lt _ (by omega)) = l[0]'(by omega) :=
                  list_idx_congr (show (i + 1) % k = 0 from by rw [hik, Nat.mod_self])
                exact h_vl_eq ▸ harc_vl
            · -- j > i+1: arc l[j-1] → l[j] or l[0]
              have hjgt : i + 1 < j := by omega
              have h1 : (l.insertIdx (i + 1) v)[j]'hj = l[j - 1]'(by omega) :=
                List.getElem_insertIdx_of_gt (by omega) hj
              rw [h1]
              by_cases hwrap : j + 1 < k + 1
              · -- no wrap: arc l[j-1] → l[j]
                have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) v).length := by rw [hlen_ins]; omega
                have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) v).length = j + 1 :=
                  by rw [hlen_ins]; exact Nat.mod_eq_of_lt hwrap
                have h2 : (l.insertIdx (i + 1) v)[(j+1)%(l.insertIdx (i+1) v).length]'hjnext_lt =
                    l[j]'(by omega) :=
                  (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                    ((List.getElem_insertIdx_of_gt (by omega) hjnext_lt').trans
                      (list_idx_congr (show j + 1 - 1 = j from by omega)))
                rw [h2]
                have h_eq : (j - 1 + 1) % k = j := by
                  have hj1 : j - 1 + 1 = j := by omega
                  rw [hj1]; exact Nat.mod_eq_of_lt (by omega)
                have step := harcs (j - 1) (by omega)
                exact (list_idx_congr h_eq) ▸ step
              · -- wrap: j = k, arc l[k-1] → l[0]
                have hjk : j = k := by omega
                have hjnext_lt' : (0 : ℕ) < (l.insertIdx (i + 1) v).length := by rw [hlen_ins]; omega
                have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) v).length = 0 :=
                  by rw [hlen_ins, hjk, Nat.mod_self]
                have h2 : (l.insertIdx (i + 1) v)[(j+1)%(l.insertIdx (i+1) v).length]'hjnext_lt =
                    l[0]'(by omega) :=
                  (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
                    (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
                rw [h2]
                have h_eq : (k - 1 + 1) % k = 0 := by
                  have hk1 : k - 1 + 1 = k := by omega
                  rw [hk1, Nat.mod_self]
                have step := harcs (k - 1) (by omega)
                have eq1 : l[k - 1]'(by omega) = l[j - 1]'(by omega) := list_idx_congr (by omega)
                have eq2 : l[(k - 1 + 1) % k]'(Nat.mod_lt _ (by omega)) = l[0]'(by omega) :=
                  list_idx_congr h_eq
                exact eq2 ▸ (eq1 ▸ step)
      · -- length grows: l.length < (l.insertIdx (i+1) v).length
        simp [hlen_ins, hk_def]
    · -- Sub-case 2b: no non-l vertex is insertable → all non-l in S⁺ ∪ S⁻
      push_neg at h_any_ins
      -- Every non-l vertex is in S⁻ or S⁺ (by non-insertable dichotomy)
      have h_partition : ∀ v, v ∉ l → S_minus v ∨ S_plus v := fun v hv_nl =>
        tournament_cycle_non_insertable D hT l ⟨hnd, hlen2, harcs⟩ v hv_nl
          (fun i hi h => h_any_ins v hv_nl i hi h.1 h.2)
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
        refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
        · -- Nodup: l Nodup, a ∉ l, b ∉ l, a ≠ b
          rw [List.nodup_append]
          refine ⟨hnd, by simp [hab_ne], ?_⟩
          intro x hx y hy
          have hy' : y = a ∨ y = b := by
            simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hy
            exact hy
          rcases hy' with rfl | rfl
          · exact fun h => ha_nl (h ▸ hx)
          · exact fun h => hb_nl (h ▸ hx)
        · simp [hlen2]
        · -- Arc condition for l ++ [a, b]
          intro i hi
          have hget : ∀ m (hm : m < (l ++ [a, b]).length), (l ++ [a, b])[m]'hm =
              if hlt : m < k then l[m]'hlt else if m = k then a else b := by
            intro m hm
            split_ifs with hlt heq
            · exact List.getElem_append_left hlt
            · subst heq
              have hk_lt : k < (l ++ [a, b]).length := hm
              have : (l ++ [a, b])[k]'hk_lt = a := by
                rw [List.getElem_append_right (le_refl k)]
                have h0 : k - k = 0 := Nat.sub_self k
                calc ([a, b] : List V)[k - k]'(by simp)
                    = ([a, b] : List V)[0]'(by simp) := getElem_congr_idx h0
                  _ = a := rfl
              exact this
            · have hmeq : m = k + 1 := by omega
              subst hmeq
              have hk1_lt : k + 1 < (l ++ [a, b]).length := hm
              have : (l ++ [a, b])[k + 1]'hk1_lt = b := by
                rw [List.getElem_append_right (by omega : k ≤ k + 1)]
                have h1 : k + 1 - k = 1 := by omega
                calc ([a, b] : List V)[k + 1 - k]'(by simp)
                    = ([a, b] : List V)[1]'(by simp) := getElem_congr_idx h1
                  _ = b := rfl
              exact this
          have hi' : i < k + 2 := hlen2 ▸ hi
          -- Use list.length for inext to match the arc condition goal
          set inext := (i + 1) % (l ++ [a, b]).length with hinext_def
          have hinext_lt : inext < (l ++ [a, b]).length :=
            Nat.mod_lt _ (by rw [hlen2]; omega)
          rw [hget i hi, hget inext hinext_lt]
          -- inext = (i+1) % (k+2) for case analysis
          have hinext_val : inext = (i + 1) % (k + 2) := by
            simp [hinext_def, hlen2]
          -- Four cases: i < k-1, i = k-1, i = k, i = k+1
          have hi4 : i < k - 1 ∨ i = k - 1 ∨ i = k ∨ i = k + 1 := by omega
          rcases hi4 with hilt | hilt | hilt | hilt
          · -- i < k-1: arc(l[i], l[i+1]) from interior arcs of l
            have hinext_eq : inext = i + 1 := by
              rw [hinext_val]; exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq, dif_pos (show i < k from by omega), dif_pos (show i + 1 < k from by omega)]
            exact (list_idx_congr (Nat.mod_eq_of_lt (show i + 1 < k from by omega))) ▸ harcs i (by omega)
          · -- i = k-1: arc(l[k-1], a)
            subst hilt
            have hinext_eq : inext = k := by
              rw [hinext_val, show k - 1 + 1 = k from by omega]
              exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq, dif_pos (show k - 1 < k from by omega),
                dif_neg (show ¬(k < k) from lt_irrefl k), if_pos rfl]
            exact ha_sm (k - 1) (by omega)
          · -- i = k: arc(a, b)
            subst hilt
            have hinext_eq : inext = k + 1 := by
              rw [hinext_val]; exact Nat.mod_eq_of_lt (by omega)
            rw [hinext_eq, dif_neg (show ¬(k < k) from lt_irrefl k), if_pos rfl,
                dif_neg (show ¬(k + 1 < k) from by omega), if_neg (show k + 1 ≠ k from by omega)]
            exact harc_ab
          · -- i = k+1: arc(b, l[0])
            subst hilt
            have hinext_eq : inext = 0 := by
              rw [hinext_val, show k + 1 + 1 = k + 2 from by omega, Nat.mod_self]
            rw [hinext_eq, dif_neg (show ¬(k + 1 < k) from by omega),
                if_neg (show k + 1 ≠ k from by omega), dif_pos (show (0 : ℕ) < k from by omega)]
            exact hb_sp 0 (by omega)
        · -- length grows: l.length < (l ++ [a, b]).length
          simp [hlen2, hk_def]
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
          (Option.some.inj ((List.getLast?_eq_some_getLast hpne).symm.trans hlast)) ▸
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
            (Option.some.inj ((List.getLast?_eq_some_getLast hpne).symm.trans hlast)) ▸
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
private lemma sc_digraph_has_directed_cycle (D : Digraph V) (hV : 0 < Fintype.card V)
    (hsc : D.IsStronglyConnected) (hout : ∀ v : V, 0 < D.outDegree v) :
    ∃ (l : List V), IsDirectedCycleList D l := by
  -- Get a starting vertex
  obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp hV
  -- A single vertex is a trivial Nodup directed path
  have hpath1 : IsDirectedPathList D [v₀] :=
    ⟨List.nodup_singleton v₀, fun i hi => by simp at hi⟩
  have hPbound : ∀ l, IsDirectedPathList D l → l.length ≤ Fintype.card V :=
    fun l hp => nodup_length_le_card l hp.1
  -- Find the maximal length Nodup directed path (lengths bounded by Fintype.card V)
  haveI hdec : DecidablePred (fun k => ∃ l : List V, IsDirectedPathList D l ∧ l.length = k) :=
    fun k => Classical.dec _
  let pathLengths : Finset ℕ :=
    (Finset.range (Fintype.card V + 1)).filter
      (fun k => ∃ l : List V, IsDirectedPathList D l ∧ l.length = k)
  have hne : pathLengths.Nonempty :=
    ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by linarith [hPbound [v₀] hpath1]),
       ⟨[v₀], hpath1, rfl⟩⟩⟩
  obtain ⟨kmax, hkmax_mem, hkmax_max⟩ := pathLengths.exists_max_image id hne
  have hkmax_ge1 : 1 ≤ kmax := by
    have := hkmax_max 1 (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by linarith [hPbound [v₀] hpath1]),
      ⟨[v₀], hpath1, rfl⟩⟩)
    simpa using this
  obtain ⟨path, hpath, hplen⟩ := (Finset.mem_filter.mp hkmax_mem).2
  -- path is a maximal Nodup directed path of length kmax
  have hpath_nd := hpath.1
  have hpath_arcs := hpath.2
  -- The last vertex of path has a successor (positive out-degree)
  have hplen_pos : 0 < kmax := by omega
  set t := path[kmax - 1]'(by omega) with ht_def
  obtain ⟨u, harc_tu⟩ : ∃ u : V, D.arc t u := by
    have h : Nonempty {u : V // D.arc t u} :=
      Fintype.card_pos_iff.mp (hout t)
    obtain ⟨⟨u, hu⟩⟩ := h; exact ⟨u, hu⟩
  -- u ∈ path (otherwise path ++ [u] would be a longer Nodup path, contradicting maximality)
  have hu_in_path : u ∈ path := by
    by_contra hu_notin
    -- Build longer path path ++ [u]
    have hpath_ext : IsDirectedPathList D (path ++ [u]) := by
      refine ⟨?_, ?_⟩
      · rw [List.nodup_append]
        exact ⟨hpath_nd, List.nodup_singleton u,
               fun a ha b hb => by simp only [List.mem_singleton] at hb; exact fun h => hu_notin (hb ▸ h ▸ ha)⟩
      · intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        rw [hplen] at hi
        by_cases hlt : i < kmax - 1
        · -- Both endpoints in path
          have h1 : (path ++ [u])[i]'(by simp; omega) = path[i]'(by omega) :=
            List.getElem_append_left (by omega)
          have h2 : (path ++ [u])[i + 1]'(by simp; omega) = path[i + 1]'(by omega) :=
            List.getElem_append_left (by omega)
          simp only [h1, h2]; exact hpath_arcs i (by omega)
        · -- i = kmax - 1: arc from path[kmax-1]=t to u
          have hieq : i = kmax - 1 := by omega
          have h1 : (path ++ [u])[i]'(by simp; omega) = t := by
            rw [List.getElem_append_left (by omega)]
            exact (list_idx_congr hieq).trans ht_def.symm
          have h2 : (path ++ [u])[i + 1]'(by simp; omega) = u := by
            have hi1_eq : i + 1 = path.length := by omega
            rw [List.getElem_append_right (by omega : path.length ≤ i + 1)]
            simp [hi1_eq]
          simp only [h1, h2]; exact harc_tu
    -- Contradicts maximality: path ++ [u] has length kmax + 1
    have hlen_ext : (path ++ [u]).length = kmax + 1 := by simp [hplen]
    have hext_mem : kmax + 1 ∈ pathLengths :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
          have hb := hPbound (path ++ [u]) hpath_ext
          rw [hlen_ext] at hb; omega),
        ⟨_, hpath_ext, hlen_ext⟩⟩
    exact absurd (hkmax_max (kmax + 1) hext_mem) (by simp [id])
  -- j = position of u in path; j < kmax - 1 (loopless: u ≠ t)
  obtain ⟨j, hj_lt, hj_get⟩ := List.mem_iff_getElem.mp hu_in_path
  have hj_ne_last : j ≠ kmax - 1 := by
    intro h
    have hut : u = t := by
      rw [← hj_get, ht_def]; exact list_idx_congr h
    exact D.loopless t (hut ▸ harc_tu)
  have hj_lt_last : j < kmax - 1 := by omega
  -- The suffix path.drop j is a directed cycle of length kmax - j ≥ 2
  refine ⟨path.drop j, (List.drop_sublist j path).nodup hpath_nd,
    by simp [List.length_drop, hplen]; omega,
    fun i hi => ?_⟩
  simp only [List.length_drop, hplen] at hi
  have hlen_drop := hplen  -- kmax = path.length
  -- Element access in path.drop j
  have hget : ∀ m (hm : m < kmax - j),
      (path.drop j)[m]'(by simp [List.length_drop, hplen]; omega) = path[j + m]'(by omega) :=
    fun m _ => List.getElem_drop ..
  rw [hget i (by omega)]
  have hdrop_len : (path.drop j).length = kmax - j := by
    simp [List.length_drop, hplen]
  by_cases hwrap : i + 1 = kmax - j
  · -- Closing arc: path[kmax-1]=t → path[j]=u
    have hmod : (i + 1) % (path.drop j).length = 0 := by
      simp [hdrop_len, hwrap]
    have hrhs : (path.drop j)[(i + 1) % (path.drop j).length]'(by omega) = u := by
      have h0 : (path.drop j)[0]'(by omega) = path[j + 0]'(by omega) := hget 0 (by omega)
      have h1 : path[j + 0]'(by omega) = path[j]'(by omega) := getElem_congr_idx (Nat.add_zero j)
      have h2 : (path.drop j)[(i + 1) % (path.drop j).length]'(by omega) = (path.drop j)[0]'(by omega) :=
        getElem_congr_idx hmod
      exact h2.trans (h0.trans (h1.trans hj_get))
    have h1 : path[j + i]'(by omega) = t := ht_def ▸ list_idx_congr (by omega)
    rw [h1, hrhs]; exact harc_tu
  · -- Interior arc: path[j+i] → path[j+i+1]
    have hmod : (i + 1) % (path.drop j).length = i + 1 := by
      simp [hdrop_len]; exact Nat.mod_eq_of_lt (by omega)
    have hrhs : (path.drop j)[(i + 1) % (path.drop j).length]'(by omega) = path[j + (i + 1)]'(by omega) :=
      (list_idx_congr hmod).trans (hget (i + 1) (by omega))
    rw [hrhs]
    exact hpath_arcs (j + i) (by omega)

/-- A nonempty finite digraph always has a longest directed cycle
(maximising list length over all directed cycle lists). -/
private lemma exists_longest_directed_cycle (D : Digraph V)
    (hcycle : ∃ l : List V, IsDirectedCycleList D l) :
    ∃ (lmax : List V), IsDirectedCycleList D lmax ∧
      ∀ (l' : List V), IsDirectedCycleList D l' → l'.length ≤ lmax.length := by
  obtain ⟨l₀, hc₀⟩ := hcycle
  have hbound : ∀ l, IsDirectedCycleList D l → l.length ≤ Fintype.card V :=
    fun l hc => nodup_length_le_card l hc.1
  -- Build a Finset of achievable cycle lengths ≤ Fintype.card V
  haveI hdec : DecidablePred (fun k => ∃ l : List V, IsDirectedCycleList D l ∧ l.length = k) :=
    fun k => Classical.dec _
  let lengths : Finset ℕ :=
    (Finset.range (Fintype.card V + 1)).filter
      (fun k => ∃ l : List V, IsDirectedCycleList D l ∧ l.length = k)
  have hlengths_ne : lengths.Nonempty :=
    ⟨l₀.length, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by linarith [hbound l₀ hc₀]),
       ⟨l₀, hc₀, rfl⟩⟩⟩
  obtain ⟨kmax, hkmax_mem, hkmax_max⟩ := lengths.exists_max_image id hlengths_ne
  obtain ⟨lmax, hcmax, hlmax_len⟩ := (Finset.mem_filter.mp hkmax_mem).2
  exact ⟨lmax, hcmax, fun l' hc' => by
    have hmem : l'.length ∈ lengths :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by linarith [hbound l' hc']), ⟨l', hc', rfl⟩⟩
    have hle : l'.length ≤ kmax := hkmax_max l'.length hmem
    linarith [hlmax_len.symm]⟩

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
    IsDirectedCycleList D (l.insertIdx (i + 1) u) := by
  obtain ⟨hnd, hlen2, harcs⟩ := hc
  set k := l.length with hk_def
  have hlen_ins : (l.insertIdx (i + 1) u).length = k + 1 := by
    rw [List.length_insertIdx_of_le_length (show i + 1 ≤ l.length by omega) u, ← hk_def]
  refine ⟨(List.perm_insertIdx u l (by omega : i + 1 ≤ k)).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hu, hnd⟩),
    by simp [hlen_ins]; omega, fun j hj => ?_⟩
  have hjk : j < k + 1 := hlen_ins ▸ hj
  have hjnext_lt : (j + 1) % (l.insertIdx (i + 1) u).length < (l.insertIdx (i + 1) u).length :=
    Nat.mod_lt _ (by rw [hlen_ins]; omega)
  -- Helper: getElem on insertIdx list with equal indices (V-level equality)
  have reindex : ∀ (m₁ m₂ : ℕ) (heq : m₁ = m₂)
      (hm₁ : m₁ < (l.insertIdx (i + 1) u).length)
      (hm₂ : m₂ < (l.insertIdx (i + 1) u).length),
      (l.insertIdx (i + 1) u)[m₁]'hm₁ = (l.insertIdx (i + 1) u)[m₂]'hm₂ :=
    fun _ _ h _ _ => list_idx_congr h
  by_cases hji : j < i
  · -- j < i: arc l[j] → l[j+1]
    have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
    have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = j + 1 :=
      by rw [hlen_ins]; exact Nat.mod_eq_of_lt (by omega)
    have h1 : (l.insertIdx (i + 1) u)[j]'hj = l[j]'(by omega) :=
      List.getElem_insertIdx_of_lt (by omega) hj
    have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
        l[j + 1]'(by omega) :=
      (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
        (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
    rw [h1, h2]
    exact (list_idx_congr (Nat.mod_eq_of_lt (show j + 1 < k from by omega))) ▸ harcs j (by omega)
  · by_cases hji2 : j = i
    · -- j = i: arc l[i] → u
      have hjnext_lt' : i + 1 < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
      have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = i + 1 :=
        by rw [hlen_ins, hji2]; exact Nat.mod_eq_of_lt (by omega)
      have h1 : (l.insertIdx (i + 1) u)[j]'hj = l[i]'(by omega) :=
        (List.getElem_insertIdx_of_lt (by omega : j < i + 1) hj).trans (list_idx_congr hji2)
      have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt = u :=
        (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
          (List.getElem_insertIdx_self hjnext_lt')
      rw [h1, h2]; exact harc_in
    · by_cases hji3 : j = i + 1
      · -- j = i+1: arc u → l[i+1] or l[0]
        have h1 : (l.insertIdx (i + 1) u)[j]'hj = u :=
          (list_idx_congr hji3).trans (List.getElem_insertIdx_self (hji3 ▸ hj))
        rw [h1]
        by_cases hwrap : j + 1 < k + 1
        · -- no wrap: arc u → l[i+1]
          have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
          have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = j + 1 :=
            by rw [hlen_ins]; exact Nat.mod_eq_of_lt hwrap
          have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
              l[i + 1]'(by omega) :=
            (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
              ((List.getElem_insertIdx_of_gt (by rw [hji3]; omega) hjnext_lt').trans
                (list_idx_congr (show j + 1 - 1 = i + 1 from by omega)))
          rw [h2]
          have h_out_eq : l[(i + 1) % k]'(Nat.mod_lt _ (by omega)) = l[i + 1]'(by omega) :=
            list_idx_congr (Nat.mod_eq_of_lt (show i + 1 < k from by omega))
          exact h_out_eq ▸ harc_out
        · -- wrap: j = k, arc u → l[0]
          have hik : i + 1 = k := by omega
          have hjnext_lt' : (0 : ℕ) < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
          have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = 0 :=
            by rw [hlen_ins, hji3, hik, Nat.mod_self]
          have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
              l[0]'(by omega) :=
            (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
              (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
          rw [h2]
          have h_out_eq : l[(i + 1) % k]'(Nat.mod_lt _ (by omega)) = l[0]'(by omega) :=
            list_idx_congr (show (i + 1) % k = 0 from by rw [hik, Nat.mod_self])
          exact h_out_eq ▸ harc_out
      · -- j > i+1: arc l[j-1] → l[j] or l[0]
        have hjgt : i + 1 < j := by omega
        have h1 : (l.insertIdx (i + 1) u)[j]'hj = l[j - 1]'(by omega) :=
          List.getElem_insertIdx_of_gt (by omega) hj
        rw [h1]
        by_cases hwrap : j + 1 < k + 1
        · -- no wrap: arc l[j-1] → l[j]
          have hjnext_lt' : j + 1 < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
          have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = j + 1 :=
            by rw [hlen_ins]; exact Nat.mod_eq_of_lt hwrap
          have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
              l[j]'(by omega) :=
            (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
              ((List.getElem_insertIdx_of_gt (by omega) hjnext_lt').trans
                (list_idx_congr (show j + 1 - 1 = j from by omega)))
          rw [h2]
          have h_eq : (j - 1 + 1) % k = j := by
            have hj1 : j - 1 + 1 = j := by omega
            rw [hj1]; exact Nat.mod_eq_of_lt (by omega)
          have step := harcs (j - 1) (by omega)
          exact (list_idx_congr h_eq) ▸ step
        · -- j = k: arc l[k-1] → l[0]
          have hjk : j = k := by omega
          have hjnext_lt' : (0 : ℕ) < (l.insertIdx (i + 1) u).length := by rw [hlen_ins]; omega
          have hjnext_eq : (j + 1) % (l.insertIdx (i + 1) u).length = 0 :=
            by rw [hlen_ins, hjk, Nat.mod_self]
          have h2 : (l.insertIdx (i + 1) u)[(j+1)%(l.insertIdx (i+1) u).length]'hjnext_lt =
              l[0]'(by omega) :=
            (reindex _ _ hjnext_eq hjnext_lt hjnext_lt').trans
              (List.getElem_insertIdx_of_lt (by omega) hjnext_lt')
          rw [h2]
          have h_eq : (k - 1 + 1) % k = 0 := by
            have hk1 : k - 1 + 1 = k := by omega
            rw [hk1, Nat.mod_self]
          have step := harcs (k - 1) (by omega)
          have eq1 : l[k - 1]'(by omega) = l[j - 1]'(by omega) := list_idx_congr (by omega)
          have eq2 : l[(k - 1 + 1) % k]'(Nat.mod_lt _ (by omega)) = l[0]'(by omega) :=
            list_idx_congr h_eq
          exact eq2 ▸ (eq1 ▸ step)

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
  obtain ⟨l₀, hc₀⟩ := sc_digraph_has_directed_cycle D (by omega) hsc hout_pos
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
    have hcins : IsDirectedCycleList D (lmax.insertIdx (i + 1) u) :=
      insertNth_directed_cycle D lmax u hcmax hu i hi_lt harc_in harc_out
    -- Contradiction: inserted cycle is longer than the supposedly maximal one
    have hlen_ins : lmax.length < (lmax.insertIdx (i + 1) u).length := by
      have h : (lmax.insertIdx (i + 1) u).length = lmax.length + 1 := by
        rw [List.length_insertIdx_of_le_length (show i + 1 ≤ lmax.length from by omega) u]
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
  set n := Fintype.card V with hn_def
  -- Fix bijection α : Fin n ≃ V
  let α : Fin n ≃ V := (Fintype.equivFin V).symm
  -- Missing arcs (as pairs in V, non-loop, not in D)
  -- Use Classical so we can build Finsets without Decidable instances
  classical
  let Missing : Finset (V × V) :=
    Finset.univ.filter (fun p : V × V => p.1 ≠ p.2 ∧ ¬D.arc p.1 p.2)
  -- |Missing| ≤ n - 2
  have hMissing_bound : Missing.card ≤ n - 2 := by
    -- Missing + arcCount = n*(n-1) (all non-loop pairs partition into arcs/missing)
    have h_partition : Missing.card + D.arcCount = n * (n - 1) := by
      -- ArcPairs as a Finset parallel to D.arcCount
      let ArcPairs : Finset (V × V) := Finset.univ.filter (fun p : V × V => D.arc p.1 p.2)
      have harcEq : D.arcCount = ArcPairs.card := rfl
      -- Missing and ArcPairs are disjoint subsets of univ
      have hdisjoint : Disjoint Missing ArcPairs := by
        rw [Finset.disjoint_left]
        intro ⟨u, v⟩ hm ha
        simp only [Missing, Finset.mem_filter, Finset.mem_univ, true_and] at hm
        simp only [ArcPairs, Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact hm.2 ha
      -- Their union is all non-loop pairs
      let NonLoop : Finset (V × V) := Finset.univ.filter (fun p : V × V => p.1 ≠ p.2)
      have hunion : Missing ∪ ArcPairs = NonLoop := by
        ext ⟨u, v⟩
        simp only [Missing, ArcPairs, NonLoop, Finset.mem_union, Finset.mem_filter,
                   Finset.mem_univ, true_and]
        constructor
        · rintro (⟨hne, -⟩ | harc)
          · exact hne
          · exact fun h => D.loopless v (h ▸ harc)
        · intro hne
          exact (Classical.em (D.arc u v)).elim (fun h => Or.inr h) (fun hna => Or.inl ⟨hne, hna⟩)
      -- |NonLoop| = n*(n-1): total n² pairs minus n diagonal pairs
      have hcard : NonLoop.card = n * (n - 1) := by
        have hDiag : (Finset.univ.filter (fun p : V × V => p.1 = p.2)).card = n := by
          rw [show Finset.univ.filter (fun p : V × V => p.1 = p.2) =
                   (Finset.univ : Finset V).image (fun v => (v, v)) from by
              ext ⟨u, v⟩; simp [eq_comm]]
          rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
              Finset.card_univ, ← hn_def]
        -- NonLoop = univ \ diagonal
        have hNonLoop_sdiff : NonLoop =
            Finset.univ \ Finset.univ.filter (fun p : V × V => p.1 = p.2) := by
          ext ⟨u, v⟩; simp [NonLoop, ne_eq]
        rw [hNonLoop_sdiff, Finset.card_sdiff, Finset.inter_univ,
            Finset.card_univ, Fintype.card_prod, ← hn_def, hDiag]
        -- Goal: n * n - n = n * (n - 1)
        have hn1 : 1 ≤ n := by omega
        have hnn : n ≤ n * n := by nlinarith
        zify [hn1, hnn]
        ring
      calc Missing.card + D.arcCount
          = Missing.card + ArcPairs.card := by rw [harcEq]
        _ = (Missing ∪ ArcPairs).card := (Finset.card_union_of_disjoint hdisjoint).symm
        _ = NonLoop.card := by rw [hunion]
        _ = n * (n - 1) := hcard
    omega
  -- "Bad" permutations: those using some missing arc in the cycle
  let BadFor : V × V → Finset (Equiv.Perm (Fin n)) := fun ab =>
    Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      ∃ i : Fin n, α (σ i) = ab.1 ∧
        α (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩) = ab.2)
  -- |BadFor (a,b)| ≤ n*(n-2)! for any missing arc (a,b).
  -- For each position k ∈ Fin n, the fiber {σ : σ k = α⁻¹(a) ∧ σ((k+1)%n) = α⁻¹(b)}
  -- has size (n-2)! (two values fixed). These fibers are disjoint (σ injective).
  -- Union bound: |BadFor(a,b)| ≤ n * (n-2)!
  have hBadFor_bound : ∀ p ∈ Missing, (BadFor p).card ≤ n * (n - 2).factorial := by
    intro ⟨a, b⟩ hmem
    simp only [Missing, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    obtain ⟨hab, _⟩ := hmem
    -- Preimages under α
    set c₁ : Fin n := α.symm a
    set c₂ : Fin n := α.symm b
    have hc12 : c₁ ≠ c₂ := by
      intro h; apply hab
      exact α.symm.injective (show α.symm a = α.symm b from h)
    -- Fiber at position k: perms that use the missing arc (a,b) at step k
    let nextPos : Fin n → Fin n := fun k =>
      ⟨(k.val + 1) % n, Nat.mod_lt _ (by omega)⟩
    let Fiber : Fin n → Finset (Equiv.Perm (Fin n)) := fun k =>
      Finset.univ.filter (fun σ => σ k = c₁ ∧ σ (nextPos k) = c₂)
    -- BadFor(a,b) ⊆ biUnion of fibers
    have hBad_sub : BadFor (a, b) ⊆ Finset.univ.biUnion Fiber := by
      intro σ hσ
      simp only [BadFor, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
      obtain ⟨i, hi1, hi2⟩ := hσ
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fiber, Finset.mem_filter,
                 and_true]
      refine ⟨i, ?_, ?_⟩
      · exact α.injective (hi1.trans (α.apply_symm_apply a).symm)
      · exact α.injective (hi2.trans (α.apply_symm_apply b).symm)
    -- Each fiber has ≤ (n-2)! elements, via injection into Perm(Fin(n-2))
    have hFiber_bound : ∀ k : Fin n, (Fiber k).card ≤ (n - 2).factorial := by
      intro k
      set k' := nextPos k with hk'_def
      -- k ≠ k': (k+1)%n ≠ k since n ≥ 3
      have hkk' : k ≠ k' := by
        intro h
        have h1 : k.val = (k.val + 1) % n := congr_arg Fin.val h
        rcases Nat.lt_or_ge (k.val + 1) n with hlt | hge
        · rw [Nat.mod_eq_of_lt hlt] at h1; omega
        · have heqn : k.val + 1 = n := Nat.le_antisymm (by omega) hge
          rw [heqn, Nat.mod_self] at h1; omega
      -- R = positions other than k, k'; C = values other than c₁, c₂
      set R := ((Finset.univ : Finset (Fin n)).erase k).erase k' with hR_def
      set C := ((Finset.univ : Finset (Fin n)).erase c₁).erase c₂ with hC_def
      have hR_card : R.card = n - 2 := by
        have hk'_mem : k' ∈ (Finset.univ : Finset (Fin n)).erase k :=
          Finset.mem_erase.mpr ⟨hkk'.symm, Finset.mem_univ _⟩
        rw [hR_def, Finset.card_erase_of_mem hk'_mem,
            Finset.card_erase_of_mem (Finset.mem_univ k),
            Finset.card_univ, Fintype.card_fin]; omega
      have hC_card : C.card = n - 2 := by
        have hc₂_mem : c₂ ∈ (Finset.univ : Finset (Fin n)).erase c₁ :=
          Finset.mem_erase.mpr ⟨hc12.symm, Finset.mem_univ _⟩
        rw [hC_def, Finset.card_erase_of_mem hc₂_mem,
            Finset.card_erase_of_mem (Finset.mem_univ c₁),
            Finset.card_univ, Fintype.card_fin]; omega
      -- Order isos Fin(n-2) ≃o R and Fin(n-2) ≃o C
      let φ_R := R.orderIsoOfFin hR_card
      let φ_C := C.orderIsoOfFin hC_card
      -- Bound: |Fiber k| ≤ |Perm(Fin(n-2))| = (n-2)!
      rw [show (n - 2).factorial = Fintype.card (Equiv.Perm (Fin (n - 2))) from by
          simp [Fintype.card_perm, Fintype.card_fin],
          ← Fintype.card_coe (Fiber k)]
      apply Fintype.card_le_of_injective (fun ⟨σ, hσ_mem⟩ =>
        -- For each m : Fin(n-2), σ maps position (φ_R m).val to a value in C
        have hσf : σ k = c₁ ∧ σ k' = c₂ := (Finset.mem_filter.mp hσ_mem).2
        have hmC : ∀ m : Fin (n - 2), σ ((φ_R m).val) ∈ C := fun m => by
          have hm_pos : (φ_R m : Fin n) ∈ R := (φ_R m).prop
          have hm_ne_k : (φ_R m : Fin n) ≠ k := fun h =>
            absurd (h ▸ hm_pos) (by simp [hR_def, Finset.mem_erase])
          have hm_ne_k' : (φ_R m : Fin n) ≠ k' := fun h =>
            absurd (h ▸ hm_pos) (by simp [hR_def, Finset.mem_erase])
          simp only [hC_def, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
          exact ⟨fun h => hm_ne_k' (σ.injective (h.trans hσf.2.symm)),
                 fun h => hm_ne_k (σ.injective (h.trans hσf.1.symm))⟩
        -- Build the permutation of Fin(n-2) by reindexing via φ_C
        let g : Fin (n - 2) → Fin (n - 2) := fun m =>
          φ_C.symm ⟨σ ((φ_R m).val), hmC m⟩
        have hg_inj : Function.Injective g := fun m₁ m₂ h => by
          apply φ_R.injective
          apply Subtype.ext_iff.mpr
          apply σ.injective
          exact congr_arg Subtype.val (φ_C.symm.injective
            (show φ_C.symm ⟨σ ((φ_R m₁).val), hmC m₁⟩ =
                 φ_C.symm ⟨σ ((φ_R m₂).val), hmC m₂⟩ from h))
        Equiv.ofBijective g ⟨hg_inj, hg_inj.surjective_of_fintype (Equiv.refl _)⟩)
      -- Injectivity of σ ↦ perm: σ₁ and σ₂ agree on all of Fin n
      intro ⟨σ₁, hσ₁⟩ ⟨σ₂, hσ₂⟩ heq
      simp only [Subtype.mk.injEq]
      have hf₁ := (Finset.mem_filter.mp hσ₁).2
      have hf₂ := (Finset.mem_filter.mp hσ₂).2
      ext x
      by_cases hxk : x = k
      · simp [hxk, hf₁.1, hf₂.1]
      by_cases hxk' : x = k'
      · subst hxk'; exact congr_arg Fin.val (hf₁.2.trans hf₂.2.symm)
      · -- x ∈ R, so x = (φ_R m).val for m = φ_R.symm ⟨x, hxR⟩
        have hxR : x ∈ R := by simp [hR_def, Finset.mem_erase, hxk, hxk']
        set m := φ_R.symm ⟨x, hxR⟩
        have hxm : (φ_R m : Fin n) = x :=
          congr_arg Subtype.val (φ_R.apply_symm_apply ⟨x, hxR⟩)
        -- heq gives pointwise equality of the two permutations of Fin(n-2)
        -- Extract: the two maps agree at m
        have hgm := Equiv.ext_iff.mp heq m
        simp only [Equiv.ofBijective_apply] at hgm
        -- hgm: φ_C.symm ⟨σ₁ (φ_R m).val, _⟩ = φ_C.symm ⟨σ₂ (φ_R m).val, _⟩
        have hval := congr_arg Subtype.val (φ_C.symm.injective hgm)
        -- hval : σ₁ (φ_R m).val = σ₂ (φ_R m).val (Fin n equality)
        -- hxm : (φ_R m : Fin n) = x; use to convert to goal about x
        have := congr_arg Fin.val hval
        rw [← hxm]; exact this
    -- Union bound: |BadFor| ≤ Σ_k |Fiber k| ≤ n * (n-2)!
    calc (BadFor (a, b)).card
        ≤ (Finset.univ.biUnion Fiber).card := Finset.card_le_card hBad_sub
      _ ≤ ∑ k : Fin n, (Fiber k).card := Finset.card_biUnion_le
      _ ≤ ∑ _k : Fin n, (n - 2).factorial :=
          Finset.sum_le_sum (fun k _ => hFiber_bound k)
      _ = n * (n - 2).factorial := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- AllBad = union over missing arcs of their bad permutation sets
  let AllBad : Finset (Equiv.Perm (Fin n)) := Missing.biUnion BadFor
  -- |AllBad| < n! by union bound.
  -- Each |BadFor(a,b)| ≤ n*(n-2)!, |Missing| ≤ n-2, so
  -- |AllBad| ≤ (n-2)*n*(n-2)! < n*(n-1)*(n-2)! = n!
  have hAllBad_lt : AllBad.card < n.factorial := by
    have h1 : AllBad.card ≤ ∑ p ∈ Missing, (BadFor p).card :=
      Finset.card_biUnion_le
    have h2 : ∑ p ∈ Missing, (BadFor p).card ≤ Missing.card * (n * (n - 2).factorial) :=
      (Finset.sum_le_sum hBadFor_bound).trans_eq
        (by simp [Finset.sum_const, smul_eq_mul])
    have h3 : Missing.card * (n * (n - 2).factorial) ≤ (n - 2) * (n * (n - 2).factorial) :=
      Nat.mul_le_mul_right _ hMissing_bound
    have h4 : (n - 2) * (n * (n - 2).factorial) < n.factorial := by
      -- n! = n * (n-1) * (n-2)!; need (n-2)*n*(n-2)! < n*(n-1)*(n-2)!
      -- which is n-2 < n-1 (true since n ≥ 3)
      have hn1 : n - 1 + 1 = n := by omega
      have hn2 : n - 2 + 1 = n - 1 := by omega
      have hfact_n : n.factorial = n * (n - 1).factorial := by
        have h := Nat.factorial_succ (n - 1); rw [hn1] at h; exact h
      have hfact_nm1 : (n - 1).factorial = (n - 1) * (n - 2).factorial := by
        have h := Nat.factorial_succ (n - 2); rw [hn2] at h; exact h
      rw [hfact_n, hfact_nm1]
      have hfact_pos : 0 < (n - 2).factorial := Nat.factorial_pos _
      calc (n - 2) * (n * (n - 2).factorial)
          = n * (n - 2) * (n - 2).factorial := by ring
        _ < n * (n - 1) * (n - 2).factorial := by
            nlinarith [hfact_pos, show 0 < n from by omega,
                       show n - 2 < n - 1 from by omega]
        _ = n * ((n - 1) * (n - 2).factorial) := by ring
    omega
  -- Extract a good permutation (not in AllBad)
  obtain ⟨σ, hσ_good⟩ : ∃ σ : Equiv.Perm (Fin n), σ ∉ AllBad := by
    by_contra hall
    push_neg at hall
    have hle : n.factorial ≤ AllBad.card := by
      calc n.factorial
          = Fintype.card (Equiv.Perm (Fin n)) := by
            simp [Fintype.card_perm, Fintype.card_fin]
        _ = (Finset.univ : Finset (Equiv.Perm (Fin n))).card := by
            simp [Finset.card_univ]
        _ ≤ AllBad.card := Finset.card_le_card (fun σ _ => hall σ)
    omega
  -- Good σ uses no missing arcs: ∀ i, D.arc (α (σ i)) (α (σ ((i+1)%n)))
  have hσ_arcs : ∀ i : Fin n,
      D.arc (α (σ i)) (α (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩)) := by
    intro i
    by_contra h_no_arc
    -- (α (σ i), α (σ ((i+1)%n))) is a missing arc → σ ∈ AllBad
    have hne : α (σ i) ≠ α (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩) := by
      intro heq
      have h1 : i.val = (i.val + 1) % n :=
        congr_arg Fin.val (σ.injective (α.injective heq))
      have hi := i.isLt
      rcases Nat.lt_or_ge (i.val + 1) n with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h1; omega
      · -- i.val + 1 ≥ n, and i.val < n, so i.val + 1 = n
        have heqn : i.val + 1 = n := Nat.le_antisymm (by omega) hge
        simp only [heqn, Nat.mod_self] at h1
        omega
    have hmem : (α (σ i), α (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩)) ∈ Missing := by
      simp only [Missing, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hne, h_no_arc⟩
    exact hσ_good (Finset.mem_biUnion.mpr ⟨_, hmem,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, rfl, rfl⟩⟩)
  -- τ = α.symm ∘ σ⁻¹ : V ≃ Fin n gives the Hamiltonian cycle
  -- τ.symm i = (σ ∘ α.symm.symm) i ... let's use τ.symm = σ.toEquiv.trans α
  -- With τ = α.symm.trans σ.symm: τ.symm = σ.trans α, τ.symm i = α (σ i) ✓
  refine ⟨α.symm.trans σ.symm, fun i => ?_⟩
  -- Goal: D.arc ((α.symm.trans σ.symm).symm i) ((α.symm.trans σ.symm).symm ⟨...⟩)
  -- (α.symm.trans σ.symm).symm = σ.symm.symm.trans α.symm.symm = σ.trans α
  -- So (α.symm.trans σ.symm).symm i = α (σ i) ✓
  have key : ∀ j : Fin n, (α.symm.trans σ.symm).symm j = α (σ j) := by
    intro j; simp [Equiv.trans_apply]
  rw [key i, key]
  exact hσ_arcs i

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

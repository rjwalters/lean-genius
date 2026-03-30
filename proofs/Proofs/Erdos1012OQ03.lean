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
- [ ] Ghouila-Houri proof
- [ ] Moon-Moser proof
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

/-- **Moon-Moser Theorem (1963)**

Every strongly connected tournament has a directed Hamiltonian path.

In fact, every tournament (even non-strongly connected ones) has a
Hamiltonian path (Rédei's theorem, 1934). The Moon-Moser result adds
that strong connectivity gives a Hamiltonian CYCLE. -/
theorem moon_moser (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hT : D.IsTournament) (hsc : D.IsStronglyConnected) :
    D.HasHamiltonianCycle := by
  sorry

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

### Ghouila-Houri (~200 lines)
The proof follows the same structure as Dirac's theorem for undirected graphs:
1. Start with a longest directed path P in D
2. Show P must be Hamiltonian (otherwise, degree conditions force extension)
3. Close P into a cycle using the pigeonhole principle on in/out neighborhoods

### Moon-Moser (~150 lines)
1. Start with a Hamiltonian path (exists by Rédei's theorem)
2. Attempt to close into a cycle: try arc from last to first vertex
3. If not, use tournament property to find a "rotation" that closes the cycle

### Rédei (~100 lines)
Induction on n: remove one vertex, get a Hamiltonian path on n-1 vertices,
then insert the removed vertex into the path using tournament comparisons.
-/

#check @ghouila_houri
#check @moon_moser
#check @redei
#check @directed_hamiltonian_threshold

end Erdos1012OQ03

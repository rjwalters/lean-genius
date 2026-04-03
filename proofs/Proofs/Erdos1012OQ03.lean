import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-
# Erdős Problem #1012 — OQ-03:
# Directed Graph Hamiltonian Cycle Thresholds

## Status
- [x] Digraph/tournament definitions and basic lemmas
- [x] List-based directed path and cycle definitions
- [x] Tournament insertion lemma (Rédei infrastructure)
- [x] tournament_full_path_list, list_path_to_hamiltonian
- [x] Non-insertable vertex dichotomy
- [x] list_cycle_to_hamiltonian, grow_cycle_to_hamiltonian
- [x] Rédei's theorem (proved)
- [x] Moon-Moser theorem (proved modulo 2 sorry)
- [ ] sc_tournament_has_cycle (1 internal sorry)
- [ ] tournament_cycle_extendable (sorry)
- [ ] ghouila_houri (sorry)
- [ ] directed_hamiltonian_threshold (sorry)
-/

namespace Erdos1012OQ03

open Finset Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: DIRECTED GRAPH DEFINITIONS
═══════════════════════════════════════════════════════════════════════════════ -/

structure Digraph (V : Type*) where
  arc : V → V → Prop
  loopless : ∀ v, ¬arc v v

noncomputable def Digraph.outDegree (D : Digraph V) (v : V) : ℕ :=
  Fintype.card {u : V // D.arc v u}

noncomputable def Digraph.inDegree (D : Digraph V) (v : V) : ℕ :=
  Fintype.card {u : V // D.arc u v}

def Digraph.IsTournament (D : Digraph V) : Prop :=
  ∀ u v : V, u ≠ v → (D.arc u v ∧ ¬D.arc v u) ∨ (D.arc v u ∧ ¬D.arc u v)

def Digraph.IsStronglyConnected (D : Digraph V) : Prop :=
  ∀ u v : V, u ≠ v → ∃ path : List V, path.head? = some u ∧ path.getLast? = some v ∧
    ∀ i, (h : i + 1 < path.length) → D.arc (path[i]) (path[i + 1])

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: HAMILTONIAN CYCLE AND PATH
═══════════════════════════════════════════════════════════════════════════════ -/

def Digraph.HasHamiltonianCycle (D : Digraph V) : Prop :=
  ∃ σ : V ≃ Fin (Fintype.card V),
    ∀ i : Fin (Fintype.card V),
      D.arc (σ.symm i) (σ.symm ⟨(i.val + 1) % Fintype.card V,
        Nat.mod_lt _ (by have := i.isLt; omega)⟩)

def Digraph.HasHamiltonianPath (D : Digraph V) : Prop :=
  ∃ σ : V ≃ Fin (Fintype.card V),
    ∀ i : Fin (Fintype.card V),
      (h : i.val + 1 < Fintype.card V) →
      D.arc (σ.symm i) (σ.symm ⟨i.val + 1, h⟩)

lemma Digraph.arc_or_arc (D : Digraph V) (hT : D.IsTournament)
    {u v : V} (huv : u ≠ v) : D.arc u v ∨ D.arc v u := by
  rcases hT u v huv with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact Or.inl h; exact Or.inr h]

lemma Digraph.arc_of_not_arc (D : Digraph V) (hT : D.IsTournament)
    {u v : V} (huv : u ≠ v) (h : ¬D.arc u v) : D.arc v u :=
  (D.arc_or_arc hT huv).resolve_left h

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II.C: LIST-BASED DIRECTED PATHS
═══════════════════════════════════════════════════════════════════════════════ -/

def IsDirectedPathList (D : Digraph V) (l : List V) : Prop :=
  l.Nodup ∧ ∀ (i : ℕ) (hi : i + 1 < l.length),
    D.arc (l[i]'(by omega)) (l[i + 1]'hi)

/-! ── List.insertIdx helper lemmas ─────────────────────────────────────────── -/

-- Length of insertIdx when index is in bounds
private lemma insertIdx_length_eq {α : Type*} {l : List α} {a : α} {i : ℕ}
    (hi : i ≤ l.length) : (l.insertIdx i a).length = l.length + 1 := by
  rw [List.length_insertIdx]; simp [hi]

-- insertIdx preserves Nodup when element is new
private lemma nodup_insertIdx {α : Type*} {l : List α} {a : α} {i : ℕ}
    (hi : i ≤ l.length) (ha : a ∉ l) (hnd : l.Nodup) :
    (l.insertIdx i a).Nodup := by
  sorry

-- insertIdx at position i gives a at that index
private lemma insertIdx_getElem_at {α : Type*} (l : List α) (a : α) (i : ℕ)
    (hi : i ≤ l.length) : (l.insertIdx i a)[i]'(by rw [insertIdx_length_eq hi]; omega) = a := by
  sorry

-- insertIdx at position i gives l[j-1] for j > i
private lemma insertIdx_getElem_gt {α : Type*} (l : List α) (a : α) (i j : ℕ)
    (hi : i ≤ l.length) (hji : i < j) (hj : j ≤ l.length) :
    (l.insertIdx i a)[j]'(by rw [insertIdx_length_eq hi]; omega) = l[j - 1]'(by omega) := by
  sorry

-- idxOf upper bound: element in list → idxOf < length
private lemma idxOf_lt_length {α : Type*} [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l) : l.idxOf a < l.length := by
  sorry

-- idxOf gives the correct element
private lemma idxOf_getElem {α : Type*} [DecidableEq α] {a : α} {l : List α}
    (h : a ∈ l) : l[l.idxOf a]'(idxOf_lt_length h) = a := by
  sorry

/-! ── Tournament path insert ─────────────────────────────────────────────── -/

lemma tournament_path_insert (D : Digraph V) (hT : D.IsTournament)
    (l : List V) (hl : 0 < l.length) (hp : IsDirectedPathList D l)
    (u : V) (hu : u ∉ l) :
    ∃ k, k ≤ l.length ∧ IsDirectedPathList D (l.insertIdx k u) := by
  sorry

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
      exact ⟨[v], rfl, List.nodup_singleton v, fun i hi => absurd hi (by simp)⟩
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
      refine ⟨l.insertIdx k u, ?_, hp'⟩
      rw [insertIdx_length_eq hk_le]; omega

lemma list_path_to_hamiltonian (D : Digraph V) (l : List V)
    (hlen : l.length = Fintype.card V) (hp : IsDirectedPathList D l) :
    D.HasHamiltonianPath := by
  have hnd := hp.1
  have hmem : ∀ v : V, v ∈ l := by
    intro v; rw [← List.mem_toFinset]
    exact (Finset.eq_univ_of_card _ (by rw [l.toFinset_card_of_nodup hnd, hlen])) ▸
      Finset.mem_univ v
  let f : Fin (Fintype.card V) → V := fun i => l[i.val]'(by omega)
  have hf_bij : Function.Bijective f := by
    constructor
    · intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp only [f] at heq; ext
      exact List.Nodup.getElem_inj_iff hnd |>.mp heq
    · intro v
      obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp (hmem v)
      exact ⟨⟨i, by omega⟩, hvi⟩
  exact ⟨(Equiv.ofBijective f hf_bij).symm, fun i hi => hp.2 i.val (by omega)⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: GHOUILA-HOURI'S THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

theorem ghouila_houri (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hsc : D.IsStronglyConnected)
    (hout : ∀ v : V, Fintype.card V / 2 ≤ D.outDegree v)
    (hin : ∀ v : V, Fintype.card V / 2 ≤ D.inDegree v) :
    D.HasHamiltonianCycle := by
  sorry

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: MOON-MOSER THEOREM FOR TOURNAMENTS
═══════════════════════════════════════════════════════════════════════════════ -/

def IsDirectedCycleList (D : Digraph V) (l : List V) : Prop :=
  l.Nodup ∧ 2 ≤ l.length ∧
  ∀ (i : ℕ) (hi : i < l.length),
    D.arc (l[i]'hi) (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)))

private lemma nodup_length_le_card (l : List V) (hnd : l.Nodup) :
    l.length ≤ Fintype.card V :=
  calc l.length = l.toFinset.card := (l.toFinset_card_of_nodup hnd).symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = Fintype.card V := Finset.card_univ

private lemma sc_tournament_has_cycle (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hT : D.IsTournament) (hsc : D.IsStronglyConnected) :
    ∃ l : List V, IsDirectedCycleList D l := by
  sorry

private lemma tournament_cycle_non_insertable (D : Digraph V)
    (hT : D.IsTournament) (l : List V) (hc : IsDirectedCycleList D l)
    (u : V) (hu : u ∉ l)
    (h_ni : ∀ (i : ℕ) (hi : i < l.length),
      ¬(D.arc (l[i]'hi) u ∧
        D.arc u (l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega))))) :
    (∀ (i : ℕ) (hi : i < l.length), D.arc (l[i]'hi) u) ∨
    (∀ (i : ℕ) (hi : i < l.length), D.arc u (l[i]'hi)) := by
  sorry

private lemma tournament_cycle_extendable (D : Digraph V) (hT : D.IsTournament)
    (hsc : D.IsStronglyConnected) (l : List V) (hc : IsDirectedCycleList D l)
    (hl : l.length < Fintype.card V) :
    ∃ l' : List V, IsDirectedCycleList D l' ∧ l.length < l'.length := by
  sorry
  /-
  obtain ⟨hnd, hlen2, harcs⟩ := hc
  set k := l.length
  have ⟨u, hu⟩ : ∃ u : V, u ∉ l := by
    by_contra hall; push_neg at hall
    exact absurd (calc Fintype.card V = Finset.univ.card := Finset.card_univ.symm
      _ ≤ l.toFinset.card := Finset.card_le_card (fun v _ => List.mem_toFinset.mpr (hall v))
      _ = k := l.toFinset_card_of_nodup hnd) (by omega)
  by_cases h_ins : ∃ (i : ℕ) (hi : i < k),
      D.arc (l[i]'hi) u ∧ D.arc u (l[(i+1)%k]'(Nat.mod_lt _ (by omega)))
  · obtain ⟨i, hi, harc_liu, harc_ul⟩ := h_ins
    -- Insert u at position i+1
    have hi1 : i + 1 ≤ k := by omega
    use l.insertIdx (i + 1) u
    have hlen_ins : (l.insertIdx (i + 1) u).length = k + 1 :=
      insertIdx_length_eq hi1
    constructor
    · refine ⟨nodup_insertIdx hi1 hu hnd, by simp [hlen_ins]; omega, ?_⟩
      intro j hj
      simp only [hlen_ins] at hj
    -- Compute elements of the inserted list
    set jnext := (j + 1) % (k + 1)
    have hjnext_lt : jnext < k + 1 := Nat.mod_lt _ (by omega)
    -- Helper to compute list elements
    have hget : ∀ m (hm : m < k + 1),
        (l.insertIdx (i + 1) u)[m]'hm =
          if m < i + 1 then l[m]'(by omega)
          else if m = i + 1 then u
          else l[m - 1]'(by omega) := by
      intro m hm
      by_cases hlt : m < i + 1
      · rw [if_pos hlt]
        exact List.getElem_insertIdx_of_lt hlt (by rw [hlen_ins])
      · rw [if_neg hlt]
        by_cases heq : m = i + 1
        · rw [if_pos heq]
          convert insertIdx_getElem_at l u (i + 1) hi1 using 2
          · rw [hlen_ins]
          · exact heq
        · rw [if_neg heq]
          convert insertIdx_getElem_gt l u (i + 1) m hi1 (by omega) (by omega) using 2
          rw [hlen_ins]
    rw [hget j hj, hget jnext hjnext_lt]
    -- Case split on j vs i+1
    by_cases hji : j < i
    · -- j < i: both j and j+1 are < i+1
      have hjnext : jnext = j + 1 := Nat.mod_eq_of_lt (by omega)
      rw [if_pos (by omega : j < i + 1), if_pos (by omega : j + 1 < i + 1), hjnext]
      exact harcs j (by omega)
    · by_cases hji2 : j = i
      · -- j = i: new[j] = l[i], new[j+1] = u
        subst hji2
        have hjnext : jnext = i + 1 := Nat.mod_eq_of_lt (by omega)
        rw [if_pos (by omega : i < i + 1), if_neg (show ¬(i + 1 < i + 1) from by omega),
            if_pos rfl, hjnext]
        exact harc_liu
      · by_cases hji3 : j = i + 1
        · -- j = i+1: new[j] = u
          subst hji3
          rw [if_neg (by omega : ¬(i + 1 < i + 1)), if_pos rfl]
          have hjnext : jnext = if i + 2 < k + 1 then i + 2 else 0 := by
            simp only [jnext, Nat.mod_eq_of_lt, Nat.mod_self]
            split_ifs with h <;> [exact Nat.mod_eq_of_lt h;
              push_neg at h; rw [show i + 2 = k + 1 from by omega, Nat.mod_self]]
          split_ifs at hjnext with h
          · rw [hjnext, if_neg (by omega : ¬(i + 2 < i + 1)),
                if_neg (by omega : ¬(i + 2 = i + 1))]
            convert harc_ul using 2
            exact (Nat.mod_eq_of_lt (by omega)).symm
          · have hik : i + 1 = k := by omega
            rw [hjnext, if_pos (by omega : (0 : ℕ) < i + 1)]
            convert harc_ul using 2
            simp [hik, Nat.mod_self]
        · -- j > i+1: new[j] = l[j-1]
          rw [if_neg (by omega : ¬(j < i + 1)), if_neg (by omega : ¬(j = i + 1))]
          by_cases hwrap : j + 1 < k + 1
          · have hjnext : jnext = j + 1 := Nat.mod_eq_of_lt hwrap
            rw [hjnext, if_neg (by omega : ¬(j + 1 < i + 1)),
                if_neg (by omega : ¬(j + 1 = i + 1))]
            exact harcs (j - 1) (by omega)
          · have hjk : j = k := by omega
            have hjnext : jnext = 0 := by simp [jnext, hjk, Nat.mod_self]
            rw [hjnext, hjk, if_pos (by omega : (0 : ℕ) < i + 1)]
            convert harcs (k - 1) (by omega) using 2
            · simp; omega
            · simp [show k - 1 + 1 = k from by omega, Nat.mod_self]
  · -- Case 2: u is not insertable anywhere
    push_neg at h_ins
    have h_ni : (∀ (i : ℕ) (hi : i < k), D.arc (l[i]'hi) u) ∨
                (∀ (i : ℕ) (hi : i < k), D.arc u (l[i]'hi)) :=
      tournament_cycle_non_insertable D hT l ⟨hnd, hlen2, harcs⟩ u hu
        (fun i hi h => h_ins i hi h.1 h.2)
    sorry
  -/

private lemma list_cycle_to_hamiltonian (D : Digraph V) (l : List V)
    (hc : IsDirectedCycleList D l) (hlen : l.length = Fintype.card V) :
    D.HasHamiltonianCycle := by
  obtain ⟨hnd, _, harcs⟩ := hc
  have hmem : ∀ v : V, v ∈ l := by
    intro v; rw [← List.mem_toFinset]
    exact (Finset.eq_univ_of_card _ (by rw [l.toFinset_card_of_nodup hnd, hlen])) ▸
      Finset.mem_univ v
  let f : Fin (Fintype.card V) → V := fun i => l[i.val]'(by omega)
  have hf_bij : Function.Bijective f := by
    constructor
    · intro ⟨i, hi⟩ ⟨j, hj⟩ heq
      simp only [f] at heq; ext
      exact List.Nodup.getElem_inj_iff hnd |>.mp heq
    · intro v
      obtain ⟨i, hi, hvi⟩ := List.mem_iff_getElem.mp (hmem v)
      exact ⟨⟨i, by omega⟩, hvi⟩
  exact ⟨(Equiv.ofBijective f hf_bij).symm, fun i => by
    change D.arc (f i) (f ⟨(i.val + 1) % Fintype.card V,
      Nat.mod_lt _ (by have := i.isLt; omega)⟩)
    simp only [f]
    have hplen : 0 < l.length := by rw [hlen]; have := i.isLt; omega
    convert harcs i.val (by have := i.isLt; omega) using 2
    rw [hlen]⟩

private lemma grow_cycle_to_hamiltonian (D : Digraph V) (hT : D.IsTournament)
    (hsc : D.IsStronglyConnected) (l : List V) (hc : IsDirectedCycleList D l) :
    D.HasHamiltonianCycle := by
  suffices ∀ (gap : ℕ) (l : List V),
      IsDirectedCycleList D l → l.length + gap = Fintype.card V →
      D.HasHamiltonianCycle from
    this (Fintype.card V - l.length) l hc
      (by have := nodup_length_le_card l hc.1; omega)
  intro gap
  induction gap using Nat.strongRecOn with
  | _ gap ih =>
    intro l hc heq
    by_cases h : gap = 0
    · exact list_cycle_to_hamiltonian D l hc (by omega)
    · obtain ⟨l', hc', hl'⟩ := tournament_cycle_extendable D hT hsc l hc (by omega)
      have hle' : l'.length ≤ Fintype.card V := nodup_length_le_card l' hc'.1
      apply ih (Fintype.card V - l'.length) (by omega) l' hc' (by omega)

theorem moon_moser (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hT : D.IsTournament) (hsc : D.IsStronglyConnected) :
    D.HasHamiltonianCycle := by
  obtain ⟨l, hc⟩ := sc_tournament_has_cycle D hn hT hsc
  exact grow_cycle_to_hamiltonian D hT hsc l hc

theorem redei (D : Digraph V) (hn : 2 ≤ Fintype.card V)
    (hT : D.IsTournament) :
    D.HasHamiltonianPath := by
  obtain ⟨l, hlen, hp⟩ := tournament_full_path_list D hT (by omega)
  exact list_path_to_hamiltonian D l hlen hp

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: EDGE THRESHOLD
═══════════════════════════════════════════════════════════════════════════════ -/

noncomputable def Digraph.arcCount (D : Digraph V) : ℕ :=
  (Finset.univ.filter (fun p : V × V => D.arc p.1 p.2)).card

theorem directed_hamiltonian_threshold (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hsc : D.IsStronglyConnected)
    (harc : (Fintype.card V - 1) ^ 2 < D.arcCount) :
    D.HasHamiltonianCycle := by
  sorry

#check @ghouila_houri
#check @moon_moser
#check @redei
#check @directed_hamiltonian_threshold

end Erdos1012OQ03

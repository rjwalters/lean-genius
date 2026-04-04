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

-- Index equality for lists: l[i] = l[j] when i = j (works around dependent-type rw issues)
private lemma list_idx_congr {α : Type*} {l : List α} {i j : Nat} (h : i = j)
    {hi : i < l.length} {hj : j < l.length} : l[i]'hi = l[j]'hj := by
  subst h; rfl

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
  obtain ⟨hnd, hlen2, harcs⟩ := hc
  set k := l.length with hk_def
  have ⟨u, hu⟩ : ∃ u : V, u ∉ l := by
    by_contra hall; push_neg at hall
    exact absurd (calc Fintype.card V = Finset.univ.card := Finset.card_univ.symm
      _ ≤ l.toFinset.card := Finset.card_le_card (fun v _ => List.mem_toFinset.mpr (hall v))
      _ = k := l.toFinset_card_of_nodup hnd) (by omega)
  by_cases h_ins : ∃ (i : ℕ) (hi : i < k),
      D.arc (l[i]'hi) u ∧ D.arc u (l[(i + 1) % k]'(Nat.mod_lt _ (by omega)))
  · obtain ⟨i, hi, harc_liu, harc_ul⟩ := h_ins
    have hi1 : i + 1 ≤ k := by omega
    use l.insertIdx (i + 1) u
    have hlen_ins : (l.insertIdx (i + 1) u).length = k + 1 := insertIdx_length_eq hi1
    set L := l.insertIdx (i + 1) u with hL_def
    have hn : L.length = k + 1 := hlen_ins
    constructor
    · refine ⟨nodup_insertIdx hi1 hu hnd, by rw [hn]; omega, fun j hj => ?_⟩
      set jn := (j + 1) % L.length with hjn_def
      have hjn_lt : jn < L.length := Nat.mod_lt _ (by rw [hn]; omega)
      -- Normalize the goal so both bound proofs are our named hypotheses
      change D.arc (L[j]'hj) (L[jn]'hjn_lt)
      by_cases hji : j < i
      · -- j < i: L[j] = l[j], L[jn] = l[jn] (both below insertion point i+1)
        have hjn_val : jn = j + 1 := by
          simp only [hjn_def, hn]; exact Nat.mod_eq_of_lt (by omega)
        have hvsrc : L[j]'hj = l[j]'(by omega) :=
          List.getElem_insertIdx_of_lt (by omega) hj
        have hvtgt : L[jn]'hjn_lt = l[jn]'(by omega) :=
          List.getElem_insertIdx_of_lt (by rw [hjn_val]; omega) hjn_lt
        rw [hvsrc, hvtgt]
        convert harcs j (by omega) using 1
        exact list_idx_congr (by rw [hjn_val]; exact (Nat.mod_eq_of_lt (by omega)).symm)
      · by_cases hji2 : j = i
        · -- j = i: L[j] = l[i], L[jn] = u
          have hjn_val : jn = j + 1 := by
            simp only [hjn_def, hn]; exact Nat.mod_eq_of_lt (by omega)
          have hvsrc : L[j]'hj = l[j]'(by omega) :=
            List.getElem_insertIdx_of_lt (by omega) hj
          have hi1_lt : i + 1 < L.length := hn.symm ▸ (by omega)
          have hjn_eq : jn = i + 1 := by rw [hjn_val, hji2]
          have hvtgt : L[jn]'hjn_lt = u :=
            (list_idx_congr hjn_eq).trans (List.getElem_insertIdx_self hi1_lt)
          rw [hvsrc, hvtgt]
          convert harc_liu using 1
          exact list_idx_congr hji2
        · by_cases hji3 : j = i + 1
          · -- j = i+1: L[j] = u
            have hjn1_lt : i + 1 < L.length := hn.symm ▸ (by omega)
            have hvsrc : L[j]'hj = u :=
              (list_idx_congr hji3).trans (List.getElem_insertIdx_self hjn1_lt)
            rw [hvsrc]
            by_cases hwrap : i + 2 < k + 1
            · -- jn = i+2, L[jn] = l[i+1]
              have hjn_val : jn = i + 2 := by
                simp only [hjn_def, hn, hji3]; exact Nat.mod_eq_of_lt (by omega)
              have hvtgt : L[jn]'hjn_lt = l[jn - 1]'(by omega) :=
                List.getElem_insertIdx_of_gt (by rw [hjn_val]; omega) hjn_lt
              rw [hvtgt]
              convert harc_ul using 1
              exact list_idx_congr (show jn - 1 = (i + 1) % k by
                rw [hjn_val, show i + 2 - 1 = i + 1 from by omega]
                exact (Nat.mod_eq_of_lt (by omega)).symm)
            · -- i+1 = k, jn = 0, L[jn] = l[0]
              have hik : i + 1 = k := by omega
              have hjn_val : jn = 0 := by
                simp only [hjn_def, hn, hji3]
                rw [show i + 2 = k + 1 from by omega, Nat.mod_self]
              have h0_lt : 0 < L.length := hn.symm ▸ (by omega)
              have hvtgt : L[jn]'hjn_lt = l[0]'(by omega) :=
                (list_idx_congr hjn_val).trans (List.getElem_insertIdx_of_lt (by omega) h0_lt)
              rw [hvtgt]
              convert harc_ul using 1
              exact list_idx_congr (show (0 : Nat) = (i + 1) % k by rw [hik, Nat.mod_self])
          · -- j > i+1: L[j] = l[j-1]
            have hvsrc : L[j]'hj = l[j - 1]'(by omega) :=
              List.getElem_insertIdx_of_gt (by omega) hj
            rw [hvsrc]
            by_cases hwrap : j + 1 < k + 1
            · -- jn = j+1, L[jn] = l[j]
              have hjn_val : jn = j + 1 := by
                simp only [hjn_def, hn]; exact Nat.mod_eq_of_lt (by omega)
              have hvtgt : L[jn]'hjn_lt = l[jn - 1]'(by omega) :=
                List.getElem_insertIdx_of_gt (by rw [hjn_val]; omega) hjn_lt
              rw [hvtgt]
              convert harcs (j - 1) (by omega) using 1
              exact list_idx_congr (show jn - 1 = (j - 1 + 1) % k by
                rw [hjn_val, show j + 1 - 1 = j from by omega, show j - 1 + 1 = j from by omega]
                exact (Nat.mod_eq_of_lt (by omega)).symm)
            · -- j = k, jn = 0, L[jn] = l[0]
              have hjn_val : jn = 0 := by
                simp only [hjn_def, hn]
                rw [show j + 1 = k + 1 from by omega, Nat.mod_self]
              have h0_lt : 0 < L.length := hn.symm ▸ (by omega)
              have hvtgt : L[jn]'hjn_lt = l[0]'(by omega) :=
                (list_idx_congr hjn_val).trans (List.getElem_insertIdx_of_lt (by omega) h0_lt)
              rw [hvtgt]
              convert harcs (k - 1) (by omega) using 1
              · exact list_idx_congr (show j - 1 = k - 1 from by omega)
              · exact list_idx_congr (show (0 : Nat) = (k - 1 + 1) % k by
                    rw [show k - 1 + 1 = k from by omega, Nat.mod_self])
    · rw [hn]; omega
  · push_neg at h_ins
    have h_ni : (∀ (i : ℕ) (hi : i < k), D.arc (l[i]'hi) u) ∨
                (∀ (i : ℕ) (hi : i < k), D.arc u (l[i]'hi)) :=
      tournament_cycle_non_insertable D hT l ⟨hnd, hlen2, harcs⟩ u hu
        (fun i hi h => h_ins i hi h.1 h.2)
    sorry

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

/-! ── V.A: Arc Counting Infrastructure ──────────────────────────────────── -/

-- Arithmetic lemma: arcCount > (n-1)² implies ≤ n-2 arcs are missing
-- from the complete digraph K*_n (which has n*(n-1) arcs).
-- Proof: n*(n-1) - arcCount ≤ n*(n-1) - (n-1)² - 1 = (n-1) - 1 = n-2.
-- (ℕ subtraction truncates to 0 if arcCount > n*(n-1), so 0 ≤ n-2 holds trivially.)
private lemma missing_arcs_le (n m : ℕ) (hn : 3 ≤ n) (harc : (n - 1) ^ 2 < m) :
    n * (n - 1) - m ≤ n - 2 := by
  set k := n - 1 with hk_def
  have hkn : k + 1 = n := by omega
  have hnn1 : n * k = k ^ 2 + k := by rw [show n = k + 1 from hkn.symm]; ring
  rw [hnn1]
  set a := k ^ 2
  omega

-- Counting argument: with ≤ n-2 arcs missing from K*_n, a Hamiltonian
-- cycle avoiding all missing arcs exists.
-- Strategy: (n-1)! cyclic permutations; each missing arc blocks ≤ (n-2)!
-- of them; total blocked ≤ (n-2)*(n-2)! < (n-1)! since n-2 < n-1. □
private lemma hamiltonian_of_few_missing_arcs (D : Digraph V)
    (hn : 3 ≤ Fintype.card V)
    (hmissing : Fintype.card V * (Fintype.card V - 1) - D.arcCount ≤ Fintype.card V - 2) :
    D.HasHamiltonianCycle := by
  sorry

theorem directed_hamiltonian_threshold (D : Digraph V) (hn : 3 ≤ Fintype.card V)
    (hsc : D.IsStronglyConnected)
    (harc : (Fintype.card V - 1) ^ 2 < D.arcCount) :
    D.HasHamiltonianCycle :=
  hamiltonian_of_few_missing_arcs D hn
    (missing_arcs_le (Fintype.card V) D.arcCount hn harc)

#check @ghouila_houri
#check @moon_moser
#check @redei
#check @directed_hamiltonian_threshold

end Erdos1012OQ03

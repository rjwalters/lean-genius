import Proofs.Erdos85OneHighV2ProfileSymmetry

/-!
# Constrained enumeration completeness for admissible one-high tables

Lean transcription of `enumerate_h1_miss_tables.py`'s recursive
edge-degree search, with a completeness proof: the sorted relevant-pair
restriction of every `OneHighFamilyV2Admissible` table occurs in the
enumerated list.  The enumerator is computable so downstream canonical
image membership in the artifact inventory can be checked by evaluation.
-/

namespace Erdos85

/-- The 24 relevant pairs in the worker's nested-loop order. -/
def oneHighRelevantPairList : List OneHighRelevantPair :=
  (List.finRange 8).flatMap fun c => (List.finRange 8).filterMap fun j =>
    if h : c < j ∧ j ≠ oneHighStandardMate c then
      some ⟨(c, j), h.1, h.2⟩ else none

theorem oneHighRelevantPairList_complete :
    ∀ pair : OneHighRelevantPair, pair ∈ oneHighRelevantPairList := by
  native_decide +revert

theorem oneHighRelevantPairList_nodup :
    oneHighRelevantPairList.Nodup := by
  native_decide

/-- One row target per branch label: twice the profile's internal-edge
count. -/
def oneHighProfileRows (profile : Nat) : Fin 8 → Nat := fun i =>
  2 * oneHighFamilyInternalEdges profile i

/-- Recursive edge-degree enumerator: assign each remaining pair every
value compatible with the residual row budgets, and keep exactly the
assignments meeting the row targets. -/
def oneHighEnumGo (rows : Fin 8 → Nat) :
    List OneHighRelevantPair → (Fin 8 → Nat) →
      List (OneHighRelevantPair → Nat)
  | [], deg => if deg = rows then [fun _ => 0] else []
  | e :: rest, deg =>
    (List.range (Nat.min (rows e.1.1 - deg e.1.1)
        (rows e.1.2 - deg e.1.2) + 1)).flatMap fun n =>
      (oneHighEnumGo rows rest
        (Function.update (Function.update deg e.1.1 (deg e.1.1 + n))
          e.1.2 (deg e.1.2 + n))).map
        fun w => Function.update w e n

/-- The enumerated candidate lists per profile. -/
def oneHighEnumFiniteTables (profile : Nat) :
    List (OneHighRelevantPair → Nat) :=
  oneHighEnumGo (oneHighProfileRows profile)
    oneHighRelevantPairList (fun _ => 0)

/-- Incidence of a relevant pair on a branch label. -/
def oneHighPairIncident (i : Fin 8) (e : OneHighRelevantPair) : Prop :=
  e.1.1 = i ∨ e.1.2 = i

instance (i : Fin 8) (e : OneHighRelevantPair) :
    Decidable (oneHighPairIncident i e) := by
  unfold oneHighPairIncident
  infer_instance

/-- DFS completeness: any target assignment whose residual incidence
sums meet the row budgets is enumerated (as its restriction to the
processed pairs). -/
theorem oneHighEnumGo_complete (rows : Fin 8 → Nat)
    (target : OneHighRelevantPair → Nat) :
    ∀ (pairs : List OneHighRelevantPair) (deg : Fin 8 → Nat),
      (∀ i, deg i +
        ((pairs.filter fun e =>
          decide (oneHighPairIncident i e)).map target).sum = rows i) →
      (fun e => if e ∈ pairs then target e else 0) ∈
        oneHighEnumGo rows pairs deg := by
  intro pairs
  induction pairs with
  | nil =>
      intro deg hinv
      have hdeg : deg = rows := by
        funext i
        have h := hinv i
        simpa using h
      subst hdeg
      unfold oneHighEnumGo
      rw [if_pos rfl, List.mem_singleton]
      funext e
      simp
  | cons e rest ih =>
      intro deg hinv
      have hne : e.1.1 ≠ e.1.2 := Fin.ne_of_lt e.2.1
      have hheadl : decide (oneHighPairIncident e.1.1 e) = true := by
        simp [oneHighPairIncident]
      have hheadr : decide (oneHighPairIncident e.1.2 e) = true := by
        simp [oneHighPairIncident]
      have hboundl : deg e.1.1 + target e ≤ rows e.1.1 := by
        have h := hinv e.1.1
        rw [List.filter_cons, if_pos hheadl] at h
        simp only [List.map_cons, List.sum_cons] at h
        omega
      have hboundr : deg e.1.2 + target e ≤ rows e.1.2 := by
        have h := hinv e.1.2
        rw [List.filter_cons, if_pos hheadr] at h
        simp only [List.map_cons, List.sum_cons] at h
        omega
      set deg' := Function.update
        (Function.update deg e.1.1 (deg e.1.1 + target e))
        e.1.2 (deg e.1.2 + target e) with hdeg'
      have hinv' : ∀ i, deg' i +
          ((rest.filter fun e' =>
            decide (oneHighPairIncident i e')).map target).sum =
            rows i := by
        intro i
        have h := hinv i
        rw [List.filter_cons] at h
        by_cases hil : e.1.1 = i
        · subst hil
          rw [if_pos hheadl] at h
          simp only [List.map_cons, List.sum_cons] at h
          have hdval : deg' e.1.1 = deg e.1.1 + target e := by
            rw [hdeg', Function.update_apply, if_neg hne,
              Function.update_apply, if_pos rfl]
          rw [hdval]
          omega
        · by_cases hir : e.1.2 = i
          · subst hir
            rw [if_pos hheadr] at h
            simp only [List.map_cons, List.sum_cons] at h
            have hdval : deg' e.1.2 = deg e.1.2 + target e := by
              rw [hdeg', Function.update_apply, if_pos rfl]
            rw [hdval]
            omega
          · have hnotinc : decide (oneHighPairIncident i e) = false := by
              simp [oneHighPairIncident, hil, hir]
            rw [if_neg (by simp [hnotinc])] at h
            have hdval : deg' i = deg i := by
              rw [hdeg', Function.update_apply,
                if_neg (fun hh => hir hh.symm), Function.update_apply,
                if_neg (fun hh => hil hh.symm)]
            rw [hdval]
            exact h
      have hrec := ih deg' hinv'
      simp only [oneHighEnumGo, List.mem_flatMap, List.mem_range,
        List.mem_map]
      refine ⟨target e,
        Nat.lt_succ_of_le (Nat.le_min.mpr ⟨by omega, by omega⟩), ?_⟩
      refine ⟨fun e' => if e' ∈ rest then target e' else 0, hrec, ?_⟩
      funext p
      by_cases hp : p = e
      · subst hp
        simp [Function.update_apply]
      · rw [Function.update_apply, if_neg hp]
        by_cases hpr : p ∈ rest
        · simp [hpr, List.mem_cons]
        · simp [hpr, List.mem_cons, hp]

/-- Sorted relevant-pair restriction of a total table. -/
def oneHighNatRestrict (table : OneHighMissTable) :
    OneHighRelevantPair → Nat := fun pair =>
  table pair.1.1.val pair.1.2.val

/-- Build the relevant pair with endpoints `{i, j}` for a non-self,
non-mate label pair. -/
def oneHighMkRelevantPair (i j : Fin 8) (hne : j ≠ i)
    (hm : j ≠ oneHighStandardMate i) : OneHighRelevantPair :=
  if h : i < j then ⟨(i, j), h, hm⟩
  else ⟨(j, i), lt_of_le_of_ne (not_lt.mp h) hne, by
    intro hh
    apply hm
    have hh' : i = oneHighStandardMate j := hh
    rw [hh']
    exact (oneHighStandardMate_involutive j).symm⟩

/-- The bridge: the incidence-filtered enumeration sum at label `i`
equals the admissibility row sum. -/
theorem oneHighIncidentSum_eq_rowSum {profile : Nat}
    {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table) (i : Fin 8) :
    ((oneHighRelevantPairList.filter fun e =>
      decide (oneHighPairIncident i e)).map
        (oneHighNatRestrict table)).sum =
      ∑ j ∈ ((Finset.univ.erase i).erase (oneHighStandardMate i)),
        table i.val j.val := by
  classical
  have hnodup : (oneHighRelevantPairList.filter fun e =>
      decide (oneHighPairIncident i e)).Nodup :=
    oneHighRelevantPairList_nodup.filter _
  rw [← List.sum_toFinset _ hnodup]
  have hsmem : ∀ e : OneHighRelevantPair,
      e ∈ (oneHighRelevantPairList.filter fun e' =>
        decide (oneHighPairIncident i e')).toFinset ↔
      (e.1.1 = i ∨ e.1.2 = i) := by
    intro e
    simp [List.mem_toFinset, List.mem_filter,
      oneHighRelevantPairList_complete e, oneHighPairIncident]
  refine Finset.sum_bij
    (fun e _ => if e.1.1 = i then e.1.2 else e.1.1) ?_ ?_ ?_ ?_
  · -- maps into the erased row domain
    intro e he
    rcases (hsmem e).mp he with hl | hr
    · rw [if_pos hl]
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr
        ⟨?_, Finset.mem_univ _⟩⟩
      · rw [← hl]
        exact e.2.2
      · rw [← hl]
        exact (Fin.ne_of_lt e.2.1).symm
    · have hne₁ : e.1.1 ≠ i := by
        rw [← hr]
        exact Fin.ne_of_lt e.2.1
      rw [if_neg hne₁]
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr
        ⟨hne₁, Finset.mem_univ _⟩⟩
      intro hmate
      apply e.2.2
      rw [hr, hmate]
      exact (oneHighStandardMate_involutive i).symm
  · -- injective
    intro e₁ he₁ e₂ he₂ heq
    have h₁ := (hsmem e₁).mp he₁
    have h₂ := (hsmem e₂).mp he₂
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · rw [if_pos h₁, if_pos h₂] at heq
      exact Subtype.ext (Prod.ext (h₁.trans h₂.symm) heq)
    · have hne₂ : e₂.1.1 ≠ i := by
        rw [← h₂]
        exact Fin.ne_of_lt e₂.2.1
      rw [if_pos h₁, if_neg hne₂] at heq
      exfalso
      have h1lt : i < e₁.1.2 := h₁ ▸ e₁.2.1
      have h2lt : e₂.1.1 < i := h₂ ▸ e₂.2.1
      rw [heq] at h1lt
      exact absurd h2lt (asymm h1lt)
    · have hne₁ : e₁.1.1 ≠ i := by
        rw [← h₁]
        exact Fin.ne_of_lt e₁.2.1
      rw [if_neg hne₁, if_pos h₂] at heq
      exfalso
      have h1lt : e₁.1.1 < i := h₁ ▸ e₁.2.1
      have h2lt : i < e₂.1.2 := h₂ ▸ e₂.2.1
      rw [← heq] at h2lt
      exact absurd h2lt (asymm h1lt)
    · have hne₁ : e₁.1.1 ≠ i := by
        rw [← h₁]
        exact Fin.ne_of_lt e₁.2.1
      have hne₂ : e₂.1.1 ≠ i := by
        rw [← h₂]
        exact Fin.ne_of_lt e₂.2.1
      rw [if_neg hne₁, if_neg hne₂] at heq
      exact Subtype.ext (Prod.ext heq (h₁.trans h₂.symm))
  · -- surjective
    intro j hj
    have hjm : j ≠ oneHighStandardMate i := (Finset.mem_erase.mp hj).1
    have hji : j ≠ i :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    refine ⟨oneHighMkRelevantPair i j hji hjm, ?_, ?_⟩
    · apply (hsmem _).mpr
      unfold oneHighMkRelevantPair
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
    · unfold oneHighMkRelevantPair
      split
      · simp
      · simp [hji]
  · -- values
    intro e he
    rcases (hsmem e).mp he with hl | hr
    · rw [if_pos hl]
      unfold oneHighNatRestrict
      rw [hl]
    · have hne₁ : e.1.1 ≠ i := by
        rw [← hr]
        exact Fin.ne_of_lt e.2.1
      rw [if_neg hne₁]
      unfold oneHighNatRestrict
      rw [← hr]
      exact h.symm e.1.1 e.1.2 (Fin.ne_of_lt e.2.1).symm e.2.2

/-- Enumeration completeness: the relevant-pair restriction of every
admissible table is produced by the constrained enumerator. -/
theorem OneHighFamilyV2Admissible.natRestrict_mem_enum {profile : Nat}
    {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table) :
    oneHighNatRestrict table ∈ oneHighEnumFiniteTables profile := by
  have hinv : ∀ i, (fun _ : Fin 8 => 0) i +
      ((oneHighRelevantPairList.filter fun e =>
        decide (oneHighPairIncident i e)).map
          (oneHighNatRestrict table)).sum =
        oneHighProfileRows profile i := by
    intro i
    rw [oneHighIncidentSum_eq_rowSum h i, h.row_sum i]
    simp [oneHighProfileRows]
  have hmem := oneHighEnumGo_complete (oneHighProfileRows profile)
    (oneHighNatRestrict table) oneHighRelevantPairList
    (fun _ => 0) hinv
  have heq : (fun e => if e ∈ oneHighRelevantPairList
      then oneHighNatRestrict table e else 0) =
      oneHighNatRestrict table := by
    funext e
    rw [if_pos (oneHighRelevantPairList_complete e)]
  rw [heq] at hmem
  exact hmem

end Erdos85

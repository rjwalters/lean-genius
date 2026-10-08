import Proofs.Erdos85OneHighV2Enumerator
import Proofs.Erdos85OneHighV2EnumCompleteness

/-!
# Completeness of the pruned executable enumerator

`enumerateOneHighTableValues` (the fast future-deficit/even-pruned DFS)
retains the value list of every `OneHighFamilyV2Admissible` table.  The
two pruning tests are shown to be *necessary* along any
solution-consistent search state:

* parity — the total remaining deficit is twice the remaining target
  edge mass;
* capacity — each row's remaining deficit is dominated by the deficits
  of its possible future neighbors.

Together with the residual row-budget invariant this replays the
unpruned completeness argument inside the pruned search, ending in
`enumerateOneHighTableValues_complete`.
-/

namespace Erdos85

/-- Incident target mass of the remaining edges at row `i`. -/
def oneHighIncidentSum (t : Nat × Nat → Nat)
    (edges : List (Nat × Nat)) (i : Nat) : Nat :=
  ((edges.filter fun e => e.1 = i || e.2 = i).map t).sum

theorem oneHighIncidentSum_nil (t : Nat × Nat → Nat) (i : Nat) :
    oneHighIncidentSum t [] i = 0 := rfl

theorem oneHighIncidentSum_cons (t : Nat × Nat → Nat)
    (f : Nat × Nat) (es : List (Nat × Nat)) (i : Nat) :
    oneHighIncidentSum t (f :: es) i =
      (if f.1 = i ∨ f.2 = i then t f else 0) +
        oneHighIncidentSum t es i := by
  unfold oneHighIncidentSum
  rw [List.filter_cons]
  by_cases h : f.1 = i ∨ f.2 = i
  · rw [if_pos (by simpa using h), if_pos h]
    simp
  · rw [if_neg (by simpa using h), if_neg h]
    simp

/-- Each incident edge's value is at most the incident mass. -/
theorem oneHighIncidentSum_le (t : Nat × Nat → Nat)
    (edges : List (Nat × Nat)) (i : Nat) {e : Nat × Nat}
    (he : e ∈ edges) (hinc : e.1 = i ∨ e.2 = i) :
    t e ≤ oneHighIncidentSum t edges i := by
  induction edges with
  | nil => exact absurd he (List.not_mem_nil)
  | cons f es ih =>
      rw [oneHighIncidentSum_cons]
      rcases List.mem_cons.mp he with rfl | he
      · rw [if_pos hinc]
        exact Nat.le_add_right _ _
      · exact le_trans (ih he) (Nat.le_add_left _ _)

/-! ## getD arithmetic -/

theorem oneHighGetD_zipWith_sub (rows : List Nat) :
    ∀ (degrees : List Nat) (i : Nat), i < rows.length →
      i < degrees.length →
    (List.zipWith (· - ·) rows degrees).getD i 0 =
      rows.getD i 0 - degrees.getD i 0 := by
  induction rows with
  | nil => intro degrees i h1 _; exact absurd h1 (by simp)
  | cons r rs ih =>
      intro degrees i h1 h2
      cases degrees with
      | nil => exact absurd h2 (by simp)
      | cons d ds =>
          cases i with
          | zero => simp
          | succ n =>
              simp only [List.zipWith_cons_cons, List.getD_cons_succ]
              exact ih ds n (by simpa using h1) (by simpa using h2)

theorem oneHighGetD_set_self (l : List Nat) (i v : Nat)
    (h : i < l.length) : (l.set i v).getD i 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self
    (by simpa using h)]
  rfl

theorem oneHighGetD_set_other (l : List Nat) {i j : Nat} (v : Nat)
    (h : j ≠ i) : (l.set i v).getD j 0 = l.getD j 0 := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_set_ne (fun hh => h hh.symm),
    ← List.getD_eq_getElem?_getD]

theorem oneHighAddDegree_getD_self (l : List Nat) (i v : Nat)
    (h : i < l.length) :
    (oneHighAddDegree l i v).getD i 0 = l.getD i 0 + v := by
  unfold oneHighAddDegree
  exact oneHighGetD_set_self l i _ h

theorem oneHighAddDegree_getD_other (l : List Nat) {i j : Nat} (v : Nat)
    (h : j ≠ i) :
    (oneHighAddDegree l i v).getD j 0 = l.getD j 0 := by
  unfold oneHighAddDegree
  exact oneHighGetD_set_other l _ h

theorem oneHighAddDegree_length (l : List Nat) (i v : Nat) :
    (oneHighAddDegree l i v).length = l.length := by
  unfold oneHighAddDegree
  exact List.length_set ..

/-- List sum as a range-indexed `getD` sum. -/
theorem oneHighList_sum_eq_range (l : List Nat) :
    l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp [List.getD_cons_succ, List.getD_cons_zero, Nat.add_comm]

/-- Total incident mass double-counts the remaining edges. -/
theorem oneHighIncidentSum_total (t : Nat × Nat → Nat)
    (edges : List (Nat × Nat))
    (hE : ∀ e ∈ edges, e.1 < 8 ∧ e.2 < 8 ∧ e.1 ≠ e.2) :
    (∑ i ∈ Finset.range 8, oneHighIncidentSum t edges i) =
      2 * (edges.map t).sum := by
  induction edges with
  | nil => simp [oneHighIncidentSum_nil]
  | cons f es ih =>
      obtain ⟨h1, h2, hne⟩ := hE f (List.mem_cons_self ..)
      have hrec := ih fun e he => hE e (List.mem_cons_of_mem f he)
      have hsplit : ∀ i, oneHighIncidentSum t (f :: es) i =
          (if i ∈ ({f.1, f.2} : Finset Nat) then t f else 0) +
            oneHighIncidentSum t es i := by
        intro i
        rw [oneHighIncidentSum_cons]
        congr 1
        by_cases h : f.1 = i ∨ f.2 = i
        · rw [if_pos h, if_pos (by
            rcases h with h | h <;> simp [h.symm])]
        · rw [if_neg h, if_neg (by
            intro hmem
            rcases Finset.mem_insert.mp hmem with rfl | hmem
            · exact h (Or.inl rfl)
            · exact h (Or.inr (Finset.mem_singleton.mp hmem).symm))]
      calc (∑ i ∈ Finset.range 8, oneHighIncidentSum t (f :: es) i) =
            (∑ i ∈ Finset.range 8,
              ((if i ∈ ({f.1, f.2} : Finset Nat) then t f else 0) +
                oneHighIncidentSum t es i)) :=
            Finset.sum_congr rfl fun i _ => hsplit i
        _ = (∑ i ∈ Finset.range 8,
              (if i ∈ ({f.1, f.2} : Finset Nat) then t f else 0)) +
            (∑ i ∈ Finset.range 8, oneHighIncidentSum t es i) :=
            Finset.sum_add_distrib
        _ = 2 * t f + 2 * (es.map t).sum := by
            rw [hrec]
            congr 1
            rw [Finset.sum_ite_mem]
            have hsub : ({f.1, f.2} : Finset Nat) ⊆ Finset.range 8 := by
              intro x hx
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact Finset.mem_range.mpr h1
              · rw [Finset.mem_singleton.mp hx]
                exact Finset.mem_range.mpr h2
            rw [Finset.inter_eq_right.mpr hsub, Finset.sum_const,
              Finset.card_pair hne]
            ring
        _ = 2 * ((f :: es).map t).sum := by
            simp only [List.map_cons, List.sum_cons]
            ring

/-- The future-neighbor image under `d` is the incident-edge image
under `d` of the other endpoint. -/
theorem oneHighFutureNeighbors_map_sum (edges : List (Nat × Nat))
    (i : Nat) (d : Nat → Nat) :
    ((oneHighFutureNeighbors edges i).map d).sum =
      ((edges.filter fun e => e.1 = i || e.2 = i).map
        (fun e => d (if e.1 = i then e.2 else e.1))).sum := by
  induction edges with
  | nil => rfl
  | cons f es ih =>
      unfold oneHighFutureNeighbors at ih ⊢
      rw [List.filterMap_cons, List.filter_cons]
      by_cases h1 : f.1 = i
      · rw [if_pos h1, if_pos (by simp [h1])]
        simp only [List.map_cons, List.sum_cons, if_pos h1]
        rw [ih]
      · rw [if_neg h1]
        by_cases h2 : f.2 = i
        · rw [if_pos h2, if_pos (by simp [h2])]
          simp only [List.map_cons, List.sum_cons, if_neg h1]
          rw [ih]
        · rw [if_neg h2, if_neg (by simp [h1, h2])]
          exact ih

/-- Pointwise map domination gives sum domination. -/
theorem oneHighSum_map_le {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h y (List.mem_cons_self ..))
        (ih fun x hx => h x (List.mem_cons_of_mem y hx))

/-! ## The pruning gate is necessary -/

theorem oneHighEnumerationFeasible_of_invariant
    (rows degrees : List Nat) (t : Nat × Nat → Nat)
    (edges : List (Nat × Nat))
    (hrows : rows.length = 8) (hdeg : degrees.length = 8)
    (hE : ∀ e ∈ edges, e.1 < 8 ∧ e.2 < 8 ∧ e.1 ≠ e.2)
    (hinv : ∀ i, i < 8 → degrees.getD i 0 +
      oneHighIncidentSum t edges i = rows.getD i 0) :
    oneHighEnumerationFeasible rows degrees edges = true := by
  have hdefget : ∀ i, i < 8 →
      (oneHighRowDeficits rows degrees).getD i 0 =
        oneHighIncidentSum t edges i := by
    intro i hi
    unfold oneHighRowDeficits
    rw [oneHighGetD_zipWith_sub rows degrees i (by omega) (by omega)]
    have := hinv i hi
    omega
  have hdeflen : (oneHighRowDeficits rows degrees).length = 8 := by
    unfold oneHighRowDeficits
    rw [List.length_zipWith]
    omega
  unfold oneHighEnumerationFeasible
  rw [Bool.and_eq_true]
  constructor
  · rw [decide_eq_true_eq]
    have hsum : (oneHighRowDeficits rows degrees).sum =
        2 * (edges.map t).sum := by
      rw [oneHighList_sum_eq_range, hdeflen]
      rw [Finset.sum_congr rfl fun i hi =>
        hdefget i (Finset.mem_range.mp hi)]
      exact oneHighIncidentSum_total t edges hE
    omega
  · rw [List.all_eq_true]
    intro i hi
    have hi8 : i < 8 := List.mem_range.mp hi
    rw [decide_eq_true_eq, hdefget i hi8,
      oneHighFutureNeighbors_map_sum]
    unfold oneHighIncidentSum
    apply oneHighSum_map_le
    intro e he
    have hmem := List.mem_filter.mp he
    obtain ⟨hb1, hb2, hbne⟩ := hE e hmem.1
    by_cases hcase : e.1 = i
    · rw [if_pos hcase, hdefget e.2 hb2]
      exact oneHighIncidentSum_le t edges e.2 hmem.1 (Or.inr rfl)
    · rw [if_neg hcase, hdefget e.1 hb1]
      exact oneHighIncidentSum_le t edges e.1 hmem.1 (Or.inl rfl)

/-! ## Completeness of the pruned search -/

theorem enumerateOneHighTableValuesAux_complete
    (rows : List Nat) (t : Nat × Nat → Nat) (hrows : rows.length = 8) :
    ∀ (edges : List (Nat × Nat)) (degrees : List Nat)
      (rev : List Nat),
      degrees.length = 8 →
      (∀ e ∈ edges, e.1 < 8 ∧ e.2 < 8 ∧ e.1 ≠ e.2) →
      (∀ i, i < 8 → degrees.getD i 0 +
        oneHighIncidentSum t edges i = rows.getD i 0) →
      (rev.reverse ++ edges.map t) ∈
        enumerateOneHighTableValuesAux rows edges degrees rev := by
  intro edges
  induction edges with
  | nil =>
      intro degrees rev hdeg hE hinv
      unfold enumerateOneHighTableValuesAux
      rw [if_pos (oneHighEnumerationFeasible_of_invariant rows degrees
        t [] hrows hdeg hE hinv)]
      have hEq : degrees = rows := by
        apply List.ext_getElem (by omega)
        intro i hi1 hi2
        have h := hinv i (by omega)
        rw [oneHighIncidentSum_nil] at h
        have hd : degrees[i] = degrees.getD i 0 := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hi1]
          rfl
        have hr : rows[i] = rows.getD i 0 := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hi2]
          rfl
        omega
      rw [if_pos hEq]
      simp
  | cons e remaining ih =>
      intro degrees rev hdeg hE hinv
      obtain ⟨he1, he2, hene⟩ := hE e (List.mem_cons_self ..)
      unfold enumerateOneHighTableValuesAux
      rw [if_pos (oneHighEnumerationFeasible_of_invariant rows degrees
        t (e :: remaining) hrows hdeg hE hinv)]
      show _ ∈ (List.range _).flatMap _
      rw [List.mem_flatMap]
      have hle1 : t e ≤ rows.getD e.1 0 - degrees.getD e.1 0 := by
        have h := hinv e.1 he1
        have hle := oneHighIncidentSum_le t (e :: remaining) e.1
          (List.mem_cons_self ..) (Or.inl rfl)
        omega
      have hle2 : t e ≤ rows.getD e.2 0 - degrees.getD e.2 0 := by
        have h := hinv e.2 he2
        have hle := oneHighIncidentSum_le t (e :: remaining) e.2
          (List.mem_cons_self ..) (Or.inr rfl)
        omega
      refine ⟨t e, List.mem_range.mpr ?_, ?_⟩
      · unfold oneHighEdgeUpper
        have := Nat.le_min.mpr ⟨hle1, hle2⟩
        omega
      · set degrees' := oneHighAddEdgeDegrees degrees e (t e)
          with hdeg'
        have hlen' : degrees'.length = 8 := by
          rw [hdeg']
          unfold oneHighAddEdgeDegrees
          rw [oneHighAddDegree_length, oneHighAddDegree_length]
          exact hdeg
        have hget1 : degrees'.getD e.1 0 =
            degrees.getD e.1 0 + t e := by
          rw [hdeg']
          unfold oneHighAddEdgeDegrees
          rw [oneHighAddDegree_getD_other _ _ hene,
            oneHighAddDegree_getD_self _ _ _ (by omega)]
        have hget2 : degrees'.getD e.2 0 =
            degrees.getD e.2 0 + t e := by
          rw [hdeg']
          unfold oneHighAddEdgeDegrees
          rw [oneHighAddDegree_getD_self _ _ _
            (by rw [oneHighAddDegree_length]; omega),
            oneHighAddDegree_getD_other _ _ hene.symm]
        have hgeto : ∀ i, i ≠ e.1 → i ≠ e.2 →
            degrees'.getD i 0 = degrees.getD i 0 := by
          intro i hi1 hi2
          rw [hdeg']
          unfold oneHighAddEdgeDegrees
          rw [oneHighAddDegree_getD_other _ _ hi2,
            oneHighAddDegree_getD_other _ _ hi1]
        have hinv' : ∀ i, i < 8 → degrees'.getD i 0 +
            oneHighIncidentSum t remaining i = rows.getD i 0 := by
          intro i hi
          have h := hinv i hi
          rw [oneHighIncidentSum_cons] at h
          by_cases hi1 : e.1 = i
          · subst hi1
            rw [if_pos (Or.inl rfl)] at h
            rw [hget1]
            omega
          · by_cases hi2 : e.2 = i
            · subst hi2
              rw [if_pos (Or.inr rfl)] at h
              rw [hget2]
              omega
            · rw [if_neg (by tauto)] at h
              rw [hgeto i (fun hh => hi1 hh.symm)
                (fun hh => hi2 hh.symm)]
              omega
        have hrec := ih degrees' (t e :: rev) hlen'
          (fun e' he' => hE e' (List.mem_cons_of_mem e he')) hinv'
        rw [List.reverse_cons, List.append_assoc] at hrec
        simpa using hrec

/-- The pruned executable enumerator retains the value list of every
admissible table. -/
theorem enumerateOneHighTableValues_complete (profile : Nat)
    {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table) :
    (oneHighFamilyTablePairs.map fun e => table e.1 e.2) ∈
      enumerateOneHighTableValues profile := by
  classical
  have hpairs : oneHighFamilyTablePairs =
      oneHighRelevantPairList.map fun p => (p.1.1.val, p.1.2.val) := by
    native_decide
  have hrowslen : (oneHighTableRows profile).length = 8 := by
    unfold oneHighTableRows
    simp
  have hrowsget : ∀ i (hi : i < 8),
      (oneHighTableRows profile).getD i 0 =
        2 * oneHighFamilyInternalEdges profile ⟨i, hi⟩ := by
    intro i hi
    unfold oneHighTableRows
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by simpa using hi)]
    simp only [Option.getD_some, List.getElem_ofFn]
  have hE₀ : ∀ e ∈ oneHighFamilyTablePairs,
      e.1 < 8 ∧ e.2 < 8 ∧ e.1 ≠ e.2 := by
    intro e he
    obtain ⟨h1, h2, h3, -⟩ := oneHighFamilyTablePairs_mem_bounds he
    exact ⟨h1, h2, Nat.ne_of_lt h3⟩
  have hinv₀ : ∀ i, i < 8 → (List.replicate 8 0).getD i 0 +
      oneHighIncidentSum (fun e => table e.1 e.2)
        oneHighFamilyTablePairs i =
      (oneHighTableRows profile).getD i 0 := by
    intro i hi
    have hrep : (List.replicate 8 (0 : Nat)).getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp [hi]
    rw [hrep, hrowsget i hi]
    simp only [Nat.zero_add]
    unfold oneHighIncidentSum
    rw [hpairs, List.filter_map, List.map_map]
    have hfilter : (oneHighRelevantPairList.filter
        ((fun e : Nat × Nat => e.1 = i || e.2 = i) ∘
          fun p : OneHighRelevantPair => (p.1.1.val, p.1.2.val))) =
        (oneHighRelevantPairList.filter fun p =>
          decide (oneHighPairIncident ⟨i, hi⟩ p)) := by
      apply List.filter_congr
      intro p _
      simp only [Function.comp_apply, oneHighPairIncident,
        Bool.decide_or]
      congr 1 <;> rw [decide_eq_decide] <;>
        exact ⟨fun hh => Fin.ext hh, fun hh => congrArg Fin.val hh⟩
    rw [hfilter]
    have hbridge := oneHighIncidentSum_eq_rowSum h ⟨i, hi⟩
    unfold oneHighNatRestrict at hbridge
    rw [Function.comp_def]
    rw [hbridge]
    exact h.row_sum ⟨i, hi⟩
  have hmain := enumerateOneHighTableValuesAux_complete
    (oneHighTableRows profile) (fun e => table e.1 e.2) hrowslen
    oneHighFamilyTablePairs (List.replicate 8 0) []
    (by simp) hE₀ hinv₀
  unfold enumerateOneHighTableValues
  simpa using hmain

end Erdos85

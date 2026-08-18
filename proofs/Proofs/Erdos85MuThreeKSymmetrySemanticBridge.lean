import Proofs.Erdos85MuThreeAllTriangleKSymmetryEnumeration

/-!
# Semantic bridge into the pruned K-symmetry search

The graph supplies final column degree two, while the executable search uses
the necessary incremental test that no partial column already has degree two
before installing another incident row.  This module proves the latter from
the former, removing procedural search bookkeeping from the graph adapter.
-/

namespace Erdos85

theorem image_finVal_mem_mu3KRowChoices
    (row : Finset (Fin 8)) (hcard : row.card = 2) :
    row.image Fin.val ∈ mu3KRowChoices := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hcard
  fin_cases a <;> fin_cases b <;> simp_all [mu3KRowChoices] <;> decide

def mu3KRowsOfRelation (K : Fin 8 → Fin 8 → Prop) [DecidableRel K] :
    Mu3KRows :=
  List.ofFn fun x : Fin 8 =>
    (Finset.range 8).filter fun y => K x (Fin.ofNat 8 y)

theorem mu3KRowsOfRelation_length
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K] :
    (mu3KRowsOfRelation K).length = 8 := by
  simp [mu3KRowsOfRelation]

theorem mu3KRowsOfRelation_getD
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (x : Nat) (hx : x < 8) :
    (mu3KRowsOfRelation K).getD x ∅ =
      ((Finset.range 8).filter fun y => K ⟨x, hx⟩ (Fin.ofNat 8 y)) := by
  interval_cases x <;> simp [mu3KRowsOfRelation]

theorem mu3KRowsOfRelation_getD_eq_image
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K] (x : Fin 8) :
    (mu3KRowsOfRelation K).getD x.val ∅ =
      ((Finset.univ.filter fun y => K x y).image Fin.val) := by
  rw [mu3KRowsOfRelation_getD K x.val x.isLt]
  ext y
  constructor
  · intro hy
    obtain ⟨hy8, hK⟩ := Finset.mem_filter.mp hy
    have hylt : y < 8 := Finset.mem_range.mp hy8
    let z : Fin 8 := ⟨y, hylt⟩
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    have hof : Fin.ofNat 8 y = z := by apply Fin.ext; simp [z, hylt]
    rwa [hof] at hK
  · intro hy
    obtain ⟨z, hz, hval⟩ := Finset.mem_image.mp hy
    have hy8 : y < 8 := by
      rw [← hval]
      exact z.isLt
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hy8, ?_⟩
    have hof : Fin.ofNat 8 z.val = z := by apply Fin.ext; simp
    rw [← hval, hof]
    exact (Finset.mem_filter.mp hz).2

@[simp] theorem mem_image_finVal_filter_iff
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K] (x y : Fin 8) :
    y.val ∈ ((Finset.univ.filter fun z => K x z).image Fin.val) ↔ K x y := by
  constructor
  · intro h
    obtain ⟨z, hz, hval⟩ := Finset.mem_image.mp h
    have hzy : z = y := Fin.ext hval
    simpa [hzy] using (Finset.mem_filter.mp hz).2
  · intro h
    exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

theorem mu3KRowsOfRelation_row_mem_choices
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hrow : ∀ x,
      ((Finset.univ : Finset (Fin 8)).filter fun y => K x y).card = 2)
    (x : Fin 8) :
    (mu3KRowsOfRelation K).getD x.val ∅ ∈ mu3KRowChoices := by
  rw [mu3KRowsOfRelation_getD_eq_image K x]
  exact image_finVal_mem_mu3KRowChoices _ (hrow x)

def mu3KColumnCount (rows : Mu3KRows) (y : Nat) : Nat :=
  (rows.map fun row => if y ∈ row then 1 else 0).sum

theorem mu3KColumnCount_rowsOfRelation
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K] (y : Fin 8) :
    mu3KColumnCount (mu3KRowsOfRelation K) y.val =
      ((Finset.univ : Finset (Fin 8)).filter fun x => K x y).card := by
  have hof (z : Fin 8) : Fin.ofNat 8 z.val = z := by
    apply Fin.ext
    simp
  rw [Finset.card_filter]
  simp [-Finset.sum_boole, mu3KColumnCount, mu3KRowsOfRelation,
    Fin.sum_univ_succ, hof] <;> rfl

theorem mu3KAddColumns_getD (counts : List Nat) (row : Mu3KRow)
    (hlen : counts.length = 8) (y : Nat) (hy : y < 8) :
    (mu3KAddColumns counts row).getD y 0 =
      counts.getD y 0 + if y ∈ row then 1 else 0 := by
  unfold mu3KAddColumns
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hy])]
  simp [hy]

theorem mu3KAddColumns_length (counts : List Nat) (row : Mu3KRow) :
    (mu3KAddColumns counts row).length = 8 := by
  simp [mu3KAddColumns]

theorem mu3KFoldColumns_length (rows : Mu3KRows) (counts : List Nat)
    (hlen : counts.length = 8) :
    (rows.foldl mu3KAddColumns counts).length = 8 := by
  induction rows generalizing counts with
  | nil => simpa using hlen
  | cons row rows ih =>
      rw [List.foldl_cons]
      exact ih (mu3KAddColumns counts row)
        (mu3KAddColumns_length counts row)

theorem mu3KColumnCounts_length (rows : Mu3KRows) :
    (mu3KColumnCounts rows).length = 8 := by
  unfold mu3KColumnCounts
  exact mu3KFoldColumns_length rows (List.replicate 8 0) (by simp)

theorem mu3KFoldColumns_getD (rows : Mu3KRows) (counts : List Nat)
    (hlen : counts.length = 8) (y : Nat) (hy : y < 8) :
    (rows.foldl mu3KAddColumns counts).getD y 0 =
      counts.getD y 0 + mu3KColumnCount rows y := by
  induction rows generalizing counts with
  | nil => simp [mu3KColumnCount]
  | cons row rows ih =>
      rw [List.foldl_cons,
        ih (mu3KAddColumns counts row)
          (mu3KAddColumns_length counts row)]
      rw [mu3KAddColumns_getD counts row hlen y hy]
      unfold mu3KColumnCount
      by_cases hmem : y ∈ row
      · simp only [List.map_cons, List.sum_cons, if_pos hmem]
        omega
      · simp only [List.map_cons, List.sum_cons, if_neg hmem]
        omega

theorem mu3KColumnCounts_getD (rows : Mu3KRows) (y : Nat) (hy : y < 8) :
    (mu3KColumnCounts rows).getD y 0 = mu3KColumnCount rows y := by
  unfold mu3KColumnCounts
  rw [mu3KFoldColumns_getD rows (List.replicate 8 0) (by simp) y hy]
  rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  simp [hy]

theorem mu3KColumnCounts_rowsOfRelation_eq_two
    (K : Fin 8 → Fin 8 → Prop) [DecidableRel K]
    (hcolumn : ∀ y,
      ((Finset.univ : Finset (Fin 8)).filter fun x => K x y).card = 2) :
    mu3KColumnCounts (mu3KRowsOfRelation K) = List.replicate 8 2 := by
  apply List.ext_getElem
  · rw [mu3KColumnCounts_length]
    simp
  · intro i hiLeft hiRight
    have hi8 : i < 8 := by
      rw [mu3KColumnCounts_length] at hiLeft
      exact hiLeft
    have hleft :
        (mu3KColumnCounts (mu3KRowsOfRelation K))[i] =
          (mu3KColumnCounts (mu3KRowsOfRelation K)).getD i 0 := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by simpa using hiLeft)]
      rfl
    let y : Fin 8 := ⟨i, hi8⟩
    calc
      (mu3KColumnCounts (mu3KRowsOfRelation K))[i] =
          (mu3KColumnCounts (mu3KRowsOfRelation K)).getD i 0 := hleft
      _ = mu3KColumnCount (mu3KRowsOfRelation K) i :=
        mu3KColumnCounts_getD _ i hi8
      _ = ((Finset.univ : Finset (Fin 8)).filter fun x => K x y).card := by
        exact mu3KColumnCount_rowsOfRelation K y
      _ = 2 := hcolumn y
      _ = (List.replicate 8 2)[i] := (List.getElem_replicate hiRight).symm

theorem mu3KColumnCount_take_lt_two_of_full_eq_two
    (rows : Mu3KRows) (n y : Nat)
    (hn : n < rows.length) (hyrow : y ∈ rows.getD n ∅)
    (hfull : mu3KColumnCount rows y = 2) :
    mu3KColumnCount (rows.take n) y < 2 := by
  have hsplit : rows = rows.take n ++ rows.drop n :=
    (List.take_append_drop n rows).symm
  have hdrop : rows.drop n = rows[n] :: rows.drop (n + 1) := by
    rw [List.drop_eq_getElem_cons hn]
  have hget : rows.getD n ∅ = rows[n] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl
  rw [hget] at hyrow
  unfold mu3KColumnCount at hfull ⊢
  rw [hsplit, hdrop] at hfull
  simp only [List.map_append, List.sum_append, List.map_cons,
    List.sum_cons] at hfull
  rw [if_pos hyrow] at hfull
  omega

theorem mu3KColumnCapacity_of_full_counts
    (rows : Mu3KRows) (n : Nat) (hn : n < rows.length)
    (hfull : mu3KColumnCounts rows = List.replicate 8 2) :
    mu3KColumnCapacity (mu3KColumnCounts (rows.take n))
      (rows.getD n ∅) = true := by
  unfold mu3KColumnCapacity
  rw [List.all_eq_true]
  intro y hy
  have hy8 : y < 8 := List.mem_range.mp hy
  by_cases hyrow : y ∈ rows.getD n ∅
  · rw [if_pos hyrow, decide_eq_true_eq,
      mu3KColumnCounts_getD (rows.take n) y hy8]
    apply mu3KColumnCount_take_lt_two_of_full_eq_two rows n y hn hyrow
    rw [← mu3KColumnCounts_getD rows y hy8, hfull]
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    simp [hy8]
  · rw [if_neg hyrow]

theorem mu3KRowSymmetryPrefix_of_indexed
    (H : Nat → Mu3KRow) (pre : Mu3KRows) (n : Nat) (row : Mu3KRow)
    (h : ∀ i, i < pre.length →
      (row ∩ H i).card = ((pre.getD i ∅) ∩ H n).card) :
    mu3KRowSymmetryPrefix H pre n row = true := by
  unfold mu3KRowSymmetryPrefix
  have hzip : pre.zip (List.range pre.length) = pre.zipIdx := by
    rw [List.zipIdx_eq_zip_range', List.range_eq_range']
  rw [hzip, List.all_eq_true]
  intro entry hentry
  obtain ⟨hi, hvalue⟩ := List.mem_zipIdx' hentry
  rw [decide_eq_true_eq]
  rw [hvalue]
  have hget : pre.getD entry.2 ∅ = pre[entry.2] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  rw [← hget]
  exact h entry.2 hi

/-- Search admissibility with the incremental capacity bookkeeping removed.
This is the convenient coordinate-adapter input: final column degree two is
enough to reconstruct every capacity gate. -/
def Mu3KSectorCapacityFreeAdmissible
    (H T : Nat → Mu3KRow) (rows : Mu3KRows) : Prop :=
  rows.length = 8 ∧
  (∀ n, n < 8 →
    let row := rows.getD n ∅
    row ∈ mu3KRowChoices ∧
    row ∩ H n = T n ∧
    mu3KRowSymmetryPrefix H (rows.take n) n row = true) ∧
  mu3KColumnCounts rows = List.replicate 8 2 ∧
  mu3KColumnSymmetry H rows = true

/-- A fully semantic version of sector admissibility: both symmetry laws are
stated by row/column indices and no DFS-prefix predicate remains. -/
def Mu3KSectorGlobalAdmissible
    (H T : Nat → Mu3KRow) (rows : Mu3KRows) : Prop :=
  rows.length = 8 ∧
  (∀ n, n < 8 →
    let row := rows.getD n ∅
    row ∈ mu3KRowChoices ∧ row ∩ H n = T n) ∧
  mu3KColumnCounts rows = List.replicate 8 2 ∧
  (∀ n i, n < 8 → i < n →
    ((rows.getD n ∅) ∩ H i).card =
      ((rows.getD i ∅) ∩ H n).card) ∧
  mu3KColumnSymmetry H rows = true

theorem mu3KSectorCapacityFreeAdmissible_of_global
    (H T : Nat → Mu3KRow) (rows : Mu3KRows)
    (h : Mu3KSectorGlobalAdmissible H T rows) :
    Mu3KSectorCapacityFreeAdmissible H T rows := by
  obtain ⟨hlen, hrows, hcounts, hrowSymm, hcolSymm⟩ := h
  refine ⟨hlen, ?_, hcounts, hcolSymm⟩
  intro n hn
  obtain ⟨hchoice, hinter⟩ := hrows n hn
  refine ⟨hchoice, hinter,
    mu3KRowSymmetryPrefix_of_indexed H (rows.take n) n
      (rows.getD n ∅) ?_⟩
  intro i hi
  have hnle : n ≤ rows.length := by omega
  have htakeLen : (rows.take n).length = n := List.length_take_of_le hnle
  have hin : i < n := by simpa [htakeLen] using hi
  have hget : (rows.take n).getD i ∅ = rows.getD i ∅ := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
    simp [hin]
  rw [hget]
  exact hrowSymm n i hn hin

theorem mu3KSectorSearchAdmissible_of_capacityFree
    (H T : Nat → Mu3KRow) (rows : Mu3KRows)
    (h : Mu3KSectorCapacityFreeAdmissible H T rows) :
    Mu3KSectorSearchAdmissible H T rows := by
  obtain ⟨hlen, hgates, hcounts, hcols⟩ := h
  refine ⟨hlen, ?_, hcounts, hcols⟩
  intro n hn
  obtain ⟨hchoice, hinter, hsymm⟩ := hgates n hn
  exact ⟨hchoice, hinter,
    mu3KColumnCapacity_of_full_counts rows n (by omega) hcounts, hsymm⟩

theorem mem_mu3KSectorEnumeration_of_capacityFree
    (H T : Nat → Mu3KRow) (rows : Mu3KRows)
    (h : Mu3KSectorCapacityFreeAdmissible H T rows) :
    rows ∈ mu3KSectorEnumeration H T :=
  mu3KSectorEnumeration_complete H T rows
    (mu3KSectorSearchAdmissible_of_capacityFree H T rows h)

theorem mem_mu3KSectorEnumeration_of_global
    (H T : Nat → Mu3KRow) (rows : Mu3KRows)
    (h : Mu3KSectorGlobalAdmissible H T rows) :
    rows ∈ mu3KSectorEnumeration H T :=
  mem_mu3KSectorEnumeration_of_capacityFree H T rows
    (mu3KSectorCapacityFreeAdmissible_of_global H T rows h)

end Erdos85

#print axioms Erdos85.mu3KColumnCapacity_of_full_counts
#print axioms Erdos85.mem_mu3KSectorEnumeration_of_capacityFree
#print axioms Erdos85.mem_mu3KSectorEnumeration_of_global

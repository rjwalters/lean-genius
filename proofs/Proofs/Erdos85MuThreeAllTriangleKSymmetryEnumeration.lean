import Mathlib

/-!
# Finite enumeration of the all-triangle exterior hole relation

This file gives an executable, pruned enumeration of the `8 × 8` two-regular
relations `K` which are disjoint from a fixed internal two-factor `H` and obey
the two transpose-symmetry laws

`K Hᵀ = H Kᵀ` and `Kᵀ H = Hᵀ K`.

Rows are represented as two-element finsets of natural numbers below `8`.
The search installs rows from `0` through `7`; column capacity and the row
symmetry law are checked incrementally, while exact column degree and the
column symmetry law are checked at the leaf.
-/

namespace Erdos85

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

abbrev Mu3KRow := Finset Nat
abbrev Mu3KRows := List Mu3KRow

def mu3KRowChoices : List Mu3KRow :=
  (List.range 8).flatMap fun a =>
    (List.range (7 - a)).map fun d => {a, a + d + 1}

def mu3H16Row (x : Nat) : Mu3KRow :=
  {x % 8, (x + 7) % 8}

def mu3H88Row (x : Nat) : Mu3KRow :=
  if x < 4 then {x, (x + 3) % 4}
  else {x, 4 + ((x - 4 + 3) % 4)}

def mu3H106Row (x : Nat) : Mu3KRow :=
  if x < 5 then {x, (x + 4) % 5}
  else {x, 5 + ((x - 5 + 2) % 3)}

def mu3KAddColumns (counts : List Nat) (row : Mu3KRow) : List Nat :=
  (List.range 8).map fun y => counts.getD y 0 + if y ∈ row then 1 else 0

def mu3KColumnCounts (rows : Mu3KRows) : List Nat :=
  rows.foldl mu3KAddColumns (List.replicate 8 0)

def mu3KColumnCapacity (counts : List Nat) (row : Mu3KRow) : Bool :=
  (List.range 8).all fun y =>
    if y ∈ row then decide (counts.getD y 0 < 2) else true

def mu3KRowSymmetryPrefix
    (H : Nat → Mu3KRow) (rows : Mu3KRows) (x : Nat)
    (row : Mu3KRow) : Bool :=
  rows.zip (List.range rows.length) |>.all fun entry =>
    decide ((row ∩ H entry.2).card =
      (entry.1 ∩ H x).card)

def mu3KColumn (rows : Mu3KRows) (y : Nat) : Finset Nat :=
  (Finset.range 8).filter fun x => y ∈ rows.getD x ∅

def mu3HColumn (H : Nat → Mu3KRow) (y : Nat) : Finset Nat :=
  (Finset.range 8).filter fun x => y ∈ H x

def mu3KColumnSymmetry (H : Nat → Mu3KRow) (rows : Mu3KRows) : Bool :=
  (List.range 8).all fun y =>
    (List.range 8).all fun y' =>
      decide (((mu3KColumn rows y) ∩ mu3HColumn H y').card =
        ((mu3KColumn rows y') ∩ mu3HColumn H y).card)

def mu3KEnumerationAux (H : Nat → Mu3KRow) :
    List Nat → Mu3KRows → List Nat → List Mu3KRows
  | [], rows, counts =>
      if counts = List.replicate 8 2 && mu3KColumnSymmetry H rows
      then [rows]
      else []
  | x :: xs, rows, counts =>
      mu3KRowChoices.flatMap fun row =>
        if Disjoint row (H x) &&
            mu3KColumnCapacity counts row &&
            mu3KRowSymmetryPrefix H rows x row
        then mu3KEnumerationAux H xs (rows ++ [row])
          (mu3KAddColumns counts row)
        else []

def mu3KEnumeration (H : Nat → Mu3KRow) : List Mu3KRows :=
  mu3KEnumerationAux H (List.range 8) [] (List.replicate 8 0)

/-- The exact, independently checkable conditions used by the pruned search.
Unlike membership in the output list, this predicate exposes every necessary
row choice, incremental capacity/symmetry gate, and final column gate. -/
def Mu3KSearchAdmissible (H : Nat → Mu3KRow) (rows : Mu3KRows) : Prop :=
  rows.length = 8 ∧
  (∀ n, n < 8 →
    let row := rows.getD n ∅
    row ∈ mu3KRowChoices ∧
    Disjoint row (H n) ∧
    mu3KColumnCapacity (mu3KColumnCounts (rows.take n)) row = true ∧
    mu3KRowSymmetryPrefix H (rows.take n) n row = true) ∧
  mu3KColumnCounts rows = List.replicate 8 2 ∧
  mu3KColumnSymmetry H rows = true

theorem mu3KColumnCounts_take_succ (rows : Mu3KRows) (n : Nat)
    (hn : n < rows.length) :
    mu3KColumnCounts (rows.take (n + 1)) =
      mu3KAddColumns (mu3KColumnCounts (rows.take n)) (rows.getD n ∅) := by
  have htake : rows.take (n + 1) = rows.take n ++ [rows[n]] := by
    simpa [Nat.add_comm] using List.take_succ_getElem hn
  have hget : rows.getD n ∅ = rows[n] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]
    rfl
  unfold mu3KColumnCounts
  rw [htake, hget, List.foldl_append]
  rfl

/-- Completeness of the pruned executable search: every row list passing the
displayed finite conditions occurs in the computed output. -/
theorem mu3KEnumeration_complete (H : Nat → Mu3KRow) (rows : Mu3KRows)
    (h : Mu3KSearchAdmissible H rows) :
    rows ∈ mu3KEnumeration H := by
  obtain ⟨hlen, hgates, hcounts, hcols⟩ := h
  let P : Nat → Prop := fun n =>
    rows ∈ mu3KEnumerationAux H ((List.range 8).drop n)
      (rows.take n) (mu3KColumnCounts (rows.take n))
  have hbase : P 8 := by
    unfold P
    have htake : rows.take 8 = rows := by simpa [hlen]
    have hdrop8 : (List.range 8).drop 8 = [] := by decide
    rw [hdrop8]
    unfold mu3KEnumerationAux
    rw [htake, if_pos]
    · simp
    · simp [hcounts, hcols]
  have hstep : ∀ n, n < 8 → P (n + 1) → P n := by
    intro n hn ih
    have hdrop : (List.range 8).drop n =
        n :: (List.range 8).drop (n + 1) := by
      interval_cases n <;> decide
    have hnrows : n < rows.length := by omega
    have htake : rows.take n ++ [rows.getD n ∅] =
        rows.take (n + 1) := by
      rw [show rows.getD n ∅ = rows[n] by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnrows]
        rfl]
      simpa [Nat.add_comm] using (List.take_succ_getElem hnrows).symm
    obtain ⟨hchoice, hdisj, hcap, hsymm⟩ := hgates n hn
    unfold P at ih ⊢
    rw [hdrop]
    unfold mu3KEnumerationAux
    rw [List.mem_flatMap]
    refine ⟨rows.getD n ∅, hchoice, ?_⟩
    rw [if_pos]
    · rw [htake, ← mu3KColumnCounts_take_succ rows n hnrows]
      exact ih
    · simpa only [Bool.and_eq_true, decide_eq_true_eq] using
        And.intro (And.intro hdisj hcap) hsymm
  have h7 := hstep 7 (by omega) hbase
  have h6 := hstep 6 (by omega) h7
  have h5 := hstep 5 (by omega) h6
  have h4 := hstep 4 (by omega) h5
  have h3 := hstep 3 (by omega) h4
  have h2 := hstep 2 (by omega) h3
  have h1 := hstep 1 (by omega) h2
  have h0 := hstep 0 (by omega) h1
  unfold P at h0
  simpa only [mu3KEnumeration, List.drop_zero, List.take_zero,
    mu3KColumnCounts, List.foldl_nil] using h0

theorem mu3KEnumeration_H16_count :
    (mu3KEnumeration mu3H16Row).length = 3 := by
  decide

theorem mu3KEnumeration_H88_count :
    (mu3KEnumeration mu3H88Row).length = 13 := by
  decide

theorem mu3KEnumeration_H106_count :
    (mu3KEnumeration mu3H106Row).length = 0 := by
  decide

/-- The C10+C6 internal shape has no all-triangle exterior two-factor
passing both K-symmetry laws. -/
theorem not_mu3KSearchAdmissible_H106 (rows : Mu3KRows) :
    ¬ Mu3KSearchAdmissible mu3H106Row rows := by
  intro h
  have hmem := mu3KEnumeration_complete mu3H106Row rows h
  have hcount := mu3KEnumeration_H106_count
  generalize heq : mu3KEnumeration mu3H106Row = output at hmem hcount
  cases output with
  | nil => simp at hmem
  | cons first rest => simp at hcount

/-! ## Uniform sector enumerator

`T x` is the part of the internal row `H x` belonging to triangle-free
components.  Thus the sector compatibility condition is exactly
`K(x) ∩ H(x) = T(x)`.  Taking `T = ∅` recovers the all-triangle search above;
taking `T = H` gives the all-triangle-free sector.
-/

def mu3KSectorEnumerationAux (H T : Nat → Mu3KRow) :
    List Nat → Mu3KRows → List Nat → List Mu3KRows
  | [], rows, counts =>
      if counts = List.replicate 8 2 && mu3KColumnSymmetry H rows
      then [rows]
      else []
  | x :: xs, rows, counts =>
      mu3KRowChoices.flatMap fun row =>
        if row ∩ H x = T x &&
            mu3KColumnCapacity counts row &&
            mu3KRowSymmetryPrefix H rows x row
        then mu3KSectorEnumerationAux H T xs (rows ++ [row])
          (mu3KAddColumns counts row)
        else []

def mu3KSectorEnumeration (H T : Nat → Mu3KRow) : List Mu3KRows :=
  mu3KSectorEnumerationAux H T (List.range 8) [] (List.replicate 8 0)

def Mu3KSectorSearchAdmissible
    (H T : Nat → Mu3KRow) (rows : Mu3KRows) : Prop :=
  rows.length = 8 ∧
  (∀ n, n < 8 →
    let row := rows.getD n ∅
    row ∈ mu3KRowChoices ∧
    row ∩ H n = T n ∧
    mu3KColumnCapacity (mu3KColumnCounts (rows.take n)) row = true ∧
    mu3KRowSymmetryPrefix H (rows.take n) n row = true) ∧
  mu3KColumnCounts rows = List.replicate 8 2 ∧
  mu3KColumnSymmetry H rows = true

theorem mu3KSectorEnumeration_complete (H T : Nat → Mu3KRow)
    (rows : Mu3KRows) (h : Mu3KSectorSearchAdmissible H T rows) :
    rows ∈ mu3KSectorEnumeration H T := by
  obtain ⟨hlen, hgates, hcounts, hcols⟩ := h
  let P : Nat → Prop := fun n =>
    rows ∈ mu3KSectorEnumerationAux H T ((List.range 8).drop n)
      (rows.take n) (mu3KColumnCounts (rows.take n))
  have hbase : P 8 := by
    unfold P
    have htake : rows.take 8 = rows := by simpa [hlen]
    have hdrop8 : (List.range 8).drop 8 = [] := by decide
    rw [hdrop8]
    unfold mu3KSectorEnumerationAux
    rw [htake, if_pos]
    · simp
    · simp [hcounts, hcols]
  have hstep : ∀ n, n < 8 → P (n + 1) → P n := by
    intro n hn ih
    have hdrop : (List.range 8).drop n =
        n :: (List.range 8).drop (n + 1) := by
      interval_cases n <;> decide
    have hnrows : n < rows.length := by omega
    have htake : rows.take n ++ [rows.getD n ∅] =
        rows.take (n + 1) := by
      rw [show rows.getD n ∅ = rows[n] by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hnrows]
        rfl]
      simpa [Nat.add_comm] using (List.take_succ_getElem hnrows).symm
    obtain ⟨hchoice, hinter, hcap, hsymm⟩ := hgates n hn
    unfold P at ih ⊢
    rw [hdrop]
    unfold mu3KSectorEnumerationAux
    rw [List.mem_flatMap]
    refine ⟨rows.getD n ∅, hchoice, ?_⟩
    rw [if_pos]
    · rw [htake, ← mu3KColumnCounts_take_succ rows n hnrows]
      exact ih
    · simpa only [Bool.and_eq_true, decide_eq_true_eq] using
        And.intro (And.intro hinter hcap) hsymm
  have h7 := hstep 7 (by omega) hbase
  have h6 := hstep 6 (by omega) h7
  have h5 := hstep 5 (by omega) h6
  have h4 := hstep 4 (by omega) h5
  have h3 := hstep 3 (by omega) h4
  have h2 := hstep 2 (by omega) h3
  have h1 := hstep 1 (by omega) h2
  have h0 := hstep 0 (by omega) h1
  unfold P at h0
  simpa only [mu3KSectorEnumeration, List.drop_zero, List.take_zero,
    mu3KColumnCounts, List.foldl_nil] using h0

def mu3EmptyRows (_ : Nat) : Mu3KRow := ∅

def mu3H88FirstTfRows (x : Nat) : Mu3KRow :=
  if x < 4 then mu3H88Row x else ∅

def mu3H88SecondTfRows (x : Nat) : Mu3KRow :=
  if x < 4 then ∅ else mu3H88Row x

def mu3H106TenTfRows (x : Nat) : Mu3KRow :=
  if x < 5 then mu3H106Row x else ∅

def mu3H106SixTfRows (x : Nat) : Mu3KRow :=
  if x < 5 then ∅ else mu3H106Row x

theorem mu3KSectorEnumeration_H16_allTf_count :
    (mu3KSectorEnumeration mu3H16Row mu3H16Row).length = 1 := by decide

theorem mu3KSectorEnumeration_H16_allTriangle_count :
    (mu3KSectorEnumeration mu3H16Row mu3EmptyRows).length = 3 := by decide

theorem mu3KSectorEnumeration_H88_allTf_count :
    (mu3KSectorEnumeration mu3H88Row mu3H88Row).length = 1 := by decide

theorem mu3KSectorEnumeration_H88_allTriangle_count :
    (mu3KSectorEnumeration mu3H88Row mu3EmptyRows).length = 13 := by decide

theorem mu3KSectorEnumeration_H88_firstTf_count :
    (mu3KSectorEnumeration mu3H88Row mu3H88FirstTfRows).length = 1 := by decide

theorem mu3KSectorEnumeration_H88_secondTf_count :
    (mu3KSectorEnumeration mu3H88Row mu3H88SecondTfRows).length = 1 := by decide

theorem mu3KSectorEnumeration_H106_allTf_count :
    (mu3KSectorEnumeration mu3H106Row mu3H106Row).length = 1 := by decide

theorem mu3KSectorEnumeration_H106_allTriangle_count :
    (mu3KSectorEnumeration mu3H106Row mu3EmptyRows).length = 0 := by decide

theorem mu3KSectorEnumeration_H106_tenTf_count :
    (mu3KSectorEnumeration mu3H106Row mu3H106TenTfRows).length = 0 := by decide

theorem mu3KSectorEnumeration_H106_sixTf_count :
    (mu3KSectorEnumeration mu3H106Row mu3H106SixTfRows).length = 1 := by decide

theorem not_mu3KSectorSearchAdmissible_of_count_zero
    (H T : Nat → Mu3KRow)
    (hzero : (mu3KSectorEnumeration H T).length = 0)
    (rows : Mu3KRows) : ¬ Mu3KSectorSearchAdmissible H T rows := by
  intro h
  have hmem := mu3KSectorEnumeration_complete H T rows h
  generalize heq : mu3KSectorEnumeration H T = output at hmem hzero
  cases output with
  | nil => simp at hmem
  | cons first rest => simp at hzero

theorem not_mu3KSectorSearchAdmissible_H106_allTriangle (rows : Mu3KRows) :
    ¬ Mu3KSectorSearchAdmissible mu3H106Row mu3EmptyRows rows :=
  not_mu3KSectorSearchAdmissible_of_count_zero _ _
    mu3KSectorEnumeration_H106_allTriangle_count rows

theorem not_mu3KSectorSearchAdmissible_H106_tenTf (rows : Mu3KRows) :
    ¬ Mu3KSectorSearchAdmissible mu3H106Row mu3H106TenTfRows rows :=
  not_mu3KSectorSearchAdmissible_of_count_zero _ _
    mu3KSectorEnumeration_H106_tenTf_count rows

/-! ## Explicit survivor lists

These are ordered exactly as the executable search returns them.  They are
also the row-support presentation used by the fixed-K certificate instances.
-/

def mu3KSurvivorsH16AllTriangle : List Mu3KRows := [
  [{1, 6}, {2, 7}, {0, 3}, {1, 4}, {2, 5}, {3, 6}, {4, 7}, {0, 5}],
  [{2, 5}, {3, 6}, {4, 7}, {0, 5}, {1, 6}, {2, 7}, {0, 3}, {1, 4}],
  [{3, 4}, {4, 5}, {5, 6}, {6, 7}, {0, 7}, {0, 1}, {1, 2}, {2, 3}]]

def mu3KSurvivorsH88AllTriangle : List Mu3KRows := [
  [{1, 2}, {2, 3}, {0, 3}, {0, 1}, {5, 6}, {6, 7}, {4, 7}, {4, 5}],
  [{4, 5}, {4, 7}, {6, 7}, {5, 6}, {0, 1}, {0, 3}, {2, 3}, {1, 2}],
  [{4, 5}, {5, 6}, {6, 7}, {4, 7}, {2, 3}, {0, 3}, {0, 1}, {1, 2}],
  [{4, 6}, {5, 7}, {4, 6}, {5, 7}, {0, 2}, {1, 3}, {0, 2}, {1, 3}],
  [{4, 6}, {5, 7}, {4, 6}, {5, 7}, {1, 3}, {0, 2}, {1, 3}, {0, 2}],
  [{4, 7}, {4, 5}, {5, 6}, {6, 7}, {0, 3}, {0, 1}, {1, 2}, {2, 3}],
  [{4, 7}, {6, 7}, {5, 6}, {4, 5}, {0, 3}, {2, 3}, {1, 2}, {0, 1}],
  [{5, 6}, {4, 5}, {4, 7}, {6, 7}, {1, 2}, {0, 1}, {0, 3}, {2, 3}],
  [{5, 6}, {6, 7}, {4, 7}, {4, 5}, {1, 2}, {2, 3}, {0, 3}, {0, 1}],
  [{5, 7}, {4, 6}, {5, 7}, {4, 6}, {0, 2}, {1, 3}, {0, 2}, {1, 3}],
  [{5, 7}, {4, 6}, {5, 7}, {4, 6}, {1, 3}, {0, 2}, {1, 3}, {0, 2}],
  [{6, 7}, {4, 7}, {4, 5}, {5, 6}, {0, 1}, {1, 2}, {2, 3}, {0, 3}],
  [{6, 7}, {5, 6}, {4, 5}, {4, 7}, {2, 3}, {1, 2}, {0, 1}, {0, 3}]]

def mu3KSurvivorH88FirstTf : Mu3KRows :=
  [{0, 3}, {0, 1}, {1, 2}, {2, 3}, {5, 6}, {6, 7}, {4, 7}, {4, 5}]

def mu3KSurvivorH88SecondTf : Mu3KRows :=
  [{1, 2}, {2, 3}, {0, 3}, {0, 1}, {4, 7}, {4, 5}, {5, 6}, {6, 7}]

def mu3KSurvivorH106SixTf : Mu3KRows :=
  [{1, 3}, {2, 4}, {0, 3}, {1, 4}, {0, 2}, {5, 7}, {5, 6}, {6, 7}]

theorem mu3KSectorEnumeration_H16_allTriangle_eq :
    mu3KSectorEnumeration mu3H16Row mu3EmptyRows =
      mu3KSurvivorsH16AllTriangle := by decide

theorem mu3KSectorEnumeration_H88_allTriangle_eq :
    mu3KSectorEnumeration mu3H88Row mu3EmptyRows =
      mu3KSurvivorsH88AllTriangle := by decide

theorem mu3KSectorEnumeration_H88_firstTf_eq :
    mu3KSectorEnumeration mu3H88Row mu3H88FirstTfRows =
      [mu3KSurvivorH88FirstTf] := by decide

theorem mu3KSectorEnumeration_H88_secondTf_eq :
    mu3KSectorEnumeration mu3H88Row mu3H88SecondTfRows =
      [mu3KSurvivorH88SecondTf] := by decide

theorem mu3KSectorEnumeration_H106_sixTf_eq :
    mu3KSectorEnumeration mu3H106Row mu3H106SixTfRows =
      [mu3KSurvivorH106SixTf] := by decide

end Erdos85

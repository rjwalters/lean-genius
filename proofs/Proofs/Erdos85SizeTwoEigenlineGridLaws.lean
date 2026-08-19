import Proofs.Erdos85SizeTwoEigenlineKLawClassification

/-!
# Grid hit laws imply the K-laws (general q)

Node: `SIZE-TWO-EIGENLINE(q)`, upstream half.  An abstract exterior grid for
the connected size-two eigenline block: cells are pairs `(x, y) : ZMod q ×
ZMod q` that are not holes, `C` is the unknown exterior adjacency, and the
only inputs are the row-hit law (`u` has exactly one `C`-neighbour in row
`x'` iff `u`'s column avoids the `H`-columns `{x', x'-1}` of that row) and
its column dual.  Double counting the `C`-edges between two rows (columns)
via `Finset.sum_comm` yields the two K-laws of
`Erdos85SizeTwoEigenlineKLawClassification`, so `klaw_classification` forces
the hole relation into the `(q-2)/2` reflection circulants — uniformly in
`q`.
-/

open Finset

namespace Erdos85

variable {q : ℕ} [NeZero q]

section GridLaws

variable (hole : ZMod q → ZMod q → Bool)
variable (C : ZMod q × ZMod q → ZMod q × ZMod q → Bool)

/-- Edge count between row `a` and row `b`, seen from row `a`. -/
theorem row_edge_count_comm (a b : ZMod q) :
    (∑ y : ZMod q, (univ.filter fun y' => C (a, y) (b, y')).card) =
      ∑ y' : ZMod q, (univ.filter fun y => C (a, y) (b, y')).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- From the row-hit law: the row-`a`-side edge count toward row `b` is the
number of cells of row `a` avoiding the two `H`-columns of row `b`. -/
theorem row_side_count (hsupp : ∀ u v, C u v = true → hole u.1 u.2 = false)
    (hrow_hit : ∀ u : ZMod q × ZMod q, hole u.1 u.2 = false → ∀ x' : ZMod q,
      (univ.filter fun y' => C u (x', y')).card =
        if u.2 = x' ∨ u.2 = x' - 1 then 0 else 1)
    (a b : ZMod q) :
    (∑ y : ZMod q, (univ.filter fun y' => C (a, y) (b, y')).card) =
      (univ.filter fun y : ZMod q =>
        hole a y = false ∧ ¬(y = b ∨ y = b - 1)).card := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : hole a y = false
  · rw [hrow_hit (a, y) hy b]
    by_cases hmem : y = b ∨ y = b - 1
    · simp [hmem]
    · simp [hmem, hy]
  · have hzero : (univ.filter fun y' => C (a, y) (b, y')).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro y' _ hC
      exact hy (hsupp _ _ (by simpa using hC))
    rw [hzero]
    have hy' : hole a y = true := by
      cases h : hole a y
      · exact absurd h hy
      · rfl
    simp [hy']

/-- Cardinality of the avoidance set, in `ℤ`:
`#{y | ¬hole a y ∧ y ∉ {b, b-1}} = q - 4 + |K(a) ∩ {b, b-1}|`. -/
theorem avoid_card (hq1 : (1 : ZMod q) ≠ 0)
    (hrow2 : ∀ x, (univ.filter fun y => hole x y).card = 2) (a b : ZMod q) :
    ((univ.filter fun y : ZMod q =>
        hole a y = false ∧ ¬(y = b ∨ y = b - 1)).card : ℤ) =
      (q : ℤ) - 4 + ((if hole a b then 1 else 0) + (if hole a (b - 1) then 1 else 0)) := by
  classical
  have hbne : b ≠ b - 1 := by
    intro h
    apply hq1
    have h0 : (0 : ZMod q) = -1 := by
      have := congrArg (fun z => z - b) h
      simpa using this
    have h1 := congrArg (fun z : ZMod q => -z) h0
    simpa using h1.symm
  have hcells : ((univ.filter fun y : ZMod q => hole a y = false).card : ℤ) +
      2 = (q : ℤ) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (ZMod q))) (fun y => hole a y = false)
    have hnot : ((univ : Finset (ZMod q)).filter fun y => ¬ hole a y = false) =
        univ.filter fun y : ZMod q => hole a y := by
      apply Finset.filter_congr
      intro y _
      simp
    rw [hnot, hrow2 a, Finset.card_univ, ZMod.card] at h
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (ZMod q)).filter fun y => hole a y = false)
    (fun y => y = b ∨ y = b - 1)
  have hin : (((univ : Finset (ZMod q)).filter fun y => hole a y = false).filter
      (fun y => y = b ∨ y = b - 1)).card =
      ((if hole a b then 0 else 1) + (if hole a (b - 1) then 0 else 1)) := by
    have hset : (((univ : Finset (ZMod q)).filter fun y => hole a y = false).filter
        (fun y => y = b ∨ y = b - 1)) =
        ({b, b - 1} : Finset (ZMod q)).filter fun y => hole a y = false := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      tauto
    rw [hset]
    rw [Finset.filter_insert, Finset.filter_singleton]
    by_cases hb : hole a b = false <;> by_cases hb' : hole a (b - 1) = false <;>
      simp [hb, hb', Finset.card_insert_of_notMem, hbne]
  have havoid : (((univ : Finset (ZMod q)).filter fun y => hole a y = false).filter
      (fun y => ¬(y = b ∨ y = b - 1))) =
      (univ.filter fun y : ZMod q => hole a y = false ∧ ¬(y = b ∨ y = b - 1)) := by
    rw [Finset.filter_filter]
  rw [havoid, hin] at hsplit
  have hz := congrArg (fun n : ℕ => (n : ℤ)) hsplit
  simp only [Nat.cast_add] at hz
  push_cast at hz
  by_cases hb : hole a b = true <;> by_cases hb' : hole a (b - 1) = true <;>
    simp [hb, hb'] at hz ⊢ <;> linarith [hcells]
/-- **Row K-law from the grid hit laws.** -/
theorem rowLaw_of_grid (hq1 : (1 : ZMod q) ≠ 0)
    (hsymm : ∀ u v, C u v = C v u)
    (hsupp : ∀ u v, C u v = true → hole u.1 u.2 = false)
    (hrow2 : ∀ x, (univ.filter fun y => hole x y).card = 2)
    (hrow_hit : ∀ u : ZMod q × ZMod q, hole u.1 u.2 = false → ∀ x' : ZMod q,
      (univ.filter fun y' => C u (x', y')).card =
        if u.2 = x' ∨ u.2 = x' - 1 then 0 else 1) :
    RowLaw hole := by
  intro a b
  have hab := row_side_count hole C hsupp hrow_hit a b
  have hba := row_side_count hole C (fun u v h => hsupp u v h) hrow_hit b a
  have hcomm := row_edge_count_comm C a b
  -- flip the inner adjacency in the (b,a)-side count using symmetry
  have hflip : (∑ y' : ZMod q, (univ.filter fun y => C (a, y) (b, y')).card) =
      ∑ y : ZMod q, (univ.filter fun y' => C (b, y) (a, y')).card := by
    apply Finset.sum_congr rfl
    intro y' _
    apply Finset.card_bij (fun y _ => y)
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hsymm]
      exact hy
    · intro y1 h1 y2 h2 h
      exact h
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      exact ⟨y, by rw [hsymm]; exact hy, rfl⟩
  have hcount : ((univ.filter fun y : ZMod q =>
      hole a y = false ∧ ¬(y = b ∨ y = b - 1)).card : ℤ) =
      ((univ.filter fun y : ZMod q =>
        hole b y = false ∧ ¬(y = a ∨ y = a - 1)).card : ℤ) := by
    have h1 : (∑ y : ZMod q, (univ.filter fun y' => C (a, y) (b, y')).card) =
        (univ.filter fun y : ZMod q =>
          hole b y = false ∧ ¬(y = a ∨ y = a - 1)).card := by
      rw [hcomm, hflip, hba]
    rw [← hab, h1]
  have hA := avoid_card hole hq1 hrow2 a b
  have hB := avoid_card hole hq1 hrow2 b a
  rw [hA, hB] at hcount
  linarith [hcount]

/-- Column-side edge count toward column `b` (mirror of `row_side_count`). -/
theorem col_side_count (hsupp : ∀ u v, C u v = true → hole u.1 u.2 = false)
    (hcol_hit : ∀ u : ZMod q × ZMod q, hole u.1 u.2 = false → ∀ y' : ZMod q,
      (univ.filter fun x' => C u (x', y')).card =
        if u.1 = y' ∨ u.1 = y' + 1 then 0 else 1)
    (a b : ZMod q) :
    (∑ x : ZMod q, (univ.filter fun x' => C (x, a) (x', b)).card) =
      (univ.filter fun x : ZMod q =>
        hole x a = false ∧ ¬(x = b ∨ x = b + 1)).card := by
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : hole x a = false
  · rw [hcol_hit (x, a) hx b]
    by_cases hmem : x = b ∨ x = b + 1
    · simp [hmem]
    · simp [hmem, hx]
  · have hzero : (univ.filter fun x' => C (x, a) (x', b)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x' _ hC
      exact hx (hsupp _ _ (by simpa using hC))
    rw [hzero]
    have hx' : hole x a = true := by
      cases h : hole x a
      · exact absurd h hx
      · rfl
    simp [hx']

/-- Column avoidance-set cardinality (mirror of `avoid_card`). -/
theorem avoid_card_col (hq1 : (1 : ZMod q) ≠ 0)
    (hcol2 : ∀ y, (univ.filter fun x => hole x y).card = 2) (a b : ZMod q) :
    ((univ.filter fun x : ZMod q =>
        hole x a = false ∧ ¬(x = b ∨ x = b + 1)).card : ℤ) =
      (q : ℤ) - 4 + ((if hole b a then 1 else 0) + (if hole (b + 1) a then 1 else 0)) := by
  classical
  have hbne : b ≠ b + 1 := by
    intro h
    apply hq1
    have := congrArg (fun z => z - b) h
    simpa using this.symm
  have hcells : ((univ.filter fun x : ZMod q => hole x a = false).card : ℤ) +
      2 = (q : ℤ) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (ZMod q))) (fun x => hole x a = false)
    have hnot : ((univ : Finset (ZMod q)).filter fun x => ¬ hole x a = false) =
        univ.filter fun x : ZMod q => hole x a := by
      apply Finset.filter_congr
      intro x _
      simp
    rw [hnot, hcol2 a, Finset.card_univ, ZMod.card] at h
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) h
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (ZMod q)).filter fun x => hole x a = false)
    (fun x => x = b ∨ x = b + 1)
  have hin : (((univ : Finset (ZMod q)).filter fun x => hole x a = false).filter
      (fun x => x = b ∨ x = b + 1)).card =
      ((if hole b a then 0 else 1) + (if hole (b + 1) a then 0 else 1)) := by
    have hset : (((univ : Finset (ZMod q)).filter fun x => hole x a = false).filter
        (fun x => x = b ∨ x = b + 1)) =
        ({b, b + 1} : Finset (ZMod q)).filter fun x => hole x a = false := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      tauto
    rw [hset, Finset.filter_insert, Finset.filter_singleton]
    by_cases hb : hole b a = false <;> by_cases hb' : hole (b + 1) a = false <;>
      simp [hb, hb', Finset.card_insert_of_notMem, hbne]
  have havoid : (((univ : Finset (ZMod q)).filter fun x => hole x a = false).filter
      (fun x => ¬(x = b ∨ x = b + 1))) =
      (univ.filter fun x : ZMod q => hole x a = false ∧ ¬(x = b ∨ x = b + 1)) := by
    rw [Finset.filter_filter]
  rw [havoid, hin] at hsplit
  have hz := congrArg (fun n : ℕ => (n : ℤ)) hsplit
  simp only [Nat.cast_add] at hz
  push_cast at hz
  by_cases hb : hole b a = true <;> by_cases hb' : hole (b + 1) a = true <;>
    simp [hb, hb'] at hz ⊢ <;> linarith [hcells]

/-- **Column K-law from the grid hit laws.** -/
theorem colLaw_of_grid (hq1 : (1 : ZMod q) ≠ 0)
    (hsymm : ∀ u v, C u v = C v u)
    (hsupp : ∀ u v, C u v = true → hole u.1 u.2 = false)
    (hcol2 : ∀ y, (univ.filter fun x => hole x y).card = 2)
    (hcol_hit : ∀ u : ZMod q × ZMod q, hole u.1 u.2 = false → ∀ y' : ZMod q,
      (univ.filter fun x' => C u (x', y')).card =
        if u.1 = y' ∨ u.1 = y' + 1 then 0 else 1) :
    ColLaw hole := by
  intro a b
  have hab := col_side_count hole C hsupp hcol_hit a b
  have hba := col_side_count hole C hsupp hcol_hit b a
  have hcomm : (∑ x : ZMod q, (univ.filter fun x' => C (x, a) (x', b)).card) =
      ∑ x' : ZMod q, (univ.filter fun x => C (x, a) (x', b)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hflip : (∑ x' : ZMod q, (univ.filter fun x => C (x, a) (x', b)).card) =
      ∑ x : ZMod q, (univ.filter fun x' => C (x, b) (x', a)).card := by
    apply Finset.sum_congr rfl
    intro x' _
    apply Finset.card_bij (fun x _ => x)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [hsymm]
      exact hx
    · intro x1 h1 x2 h2 h
      exact h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨x, by rw [hsymm]; exact hx, rfl⟩
  have hcount : ((univ.filter fun x : ZMod q =>
      hole x a = false ∧ ¬(x = b ∨ x = b + 1)).card : ℤ) =
      ((univ.filter fun x : ZMod q =>
        hole x b = false ∧ ¬(x = a ∨ x = a + 1)).card : ℤ) := by
    have h1 : (∑ x : ZMod q, (univ.filter fun x' => C (x, a) (x', b)).card) =
        (univ.filter fun x : ZMod q =>
          hole x b = false ∧ ¬(x = a ∨ x = a + 1)).card := by
      rw [hcomm, hflip, hba]
    rw [← hab, h1]
  have hA := avoid_card_col hole hq1 hcol2 a b
  have hB := avoid_card_col hole hq1 hcol2 b a
  rw [hA, hB] at hcount
  linarith [hcount]

/-- **Grid capstone (connected shape, uniform in q).**  A hole relation that
is 2-regular in rows and columns, avoids the internal `H`-shifts `{0, -1}`,
and admits ANY exterior adjacency `C` satisfying the row/column hit laws, is
one of the `(q-2)/2` reflection circulants.  This chains
`rowLaw_of_grid`/`colLaw_of_grid` into `klaw_classification`. -/
theorem gridCode_hole_reflectionCirculant (hq2 : 2 ∣ q)
    (hsymm : ∀ u v, C u v = C v u)
    (hsupp : ∀ u v, C u v = true → hole u.1 u.2 = false)
    (havoid : ∀ x, hole x x = false ∧ hole x (x - 1) = false)
    (hrow2 : ∀ x, (univ.filter fun y => hole x y).card = 2)
    (hcol2 : ∀ y, (univ.filter fun x => hole x y).card = 2)
    (hrow_hit : ∀ u : ZMod q × ZMod q, hole u.1 u.2 = false → ∀ x' : ZMod q,
      (univ.filter fun y' => C u (x', y')).card =
        if u.2 = x' ∨ u.2 = x' - 1 then 0 else 1)
    (hcol_hit : ∀ u : ZMod q × ZMod q, hole u.1 u.2 = false → ∀ y' : ZMod q,
      (univ.filter fun x' => C u (x', y')).card =
        if u.1 = y' ∨ u.1 = y' + 1 then 0 else 1) :
    ∃ s : ZMod q, s ≠ 0 ∧ s ≠ -1 ∧
      ∀ x y, hole x y = true ↔ y - x = s ∨ y - x = -1 - s := by
  have hq1 : (1 : ZMod q) ≠ 0 := by
    intro h
    have := congrArg (ZMod.castHom hq2 (ZMod 2)) h
    simp only [map_one, map_zero] at this
    exact absurd this (by decide)
  exact klaw_classification hq2 hole (hrow2 0)
    (fun x => (havoid x).1) (fun x => (havoid x).2)
    (rowLaw_of_grid hole C hq1 hsymm hsupp hrow2 hrow_hit)
    (colLaw_of_grid hole C hq1 hsymm hsupp hcol2 hcol_hit)

end GridLaws

end Erdos85

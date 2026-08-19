import Proofs.Erdos85ZModEightSameParitySingleIntertwiner

/-!
# Excluding a mixed-parity row-two self-intertwiner on C8

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The residual odd perfect matching left after removing a same-parity
half-turn cannot have either cyclic orientation: the forward orientation is
incompatible with symmetry, while every odd reverse matching contains a
cycle edge.
-/

namespace Erdos85

/-- A symmetric odd-parity perfect matching on `ZMod 8`, avoiding the two
cycle neighbors, cannot have either of the two cyclic orientations. -/
theorem zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
    (f : ZMod 8 → ZMod 8)
    (hinvol : ∀ x, f (f x) = x)
    (hodd : ∀ x, ¬ ZModEightEvenOffset (f x - x))
    (havoid : ∀ x, f x ≠ x - 1 ∧ f x ≠ x + 1)
    (horient : (∀ x, f (x + 1) = f x + 1) ∨
      (∀ x, f (x + 1) = f x - 1)) : False := by
  rcases horient with hfor | hrev
  · have hformula : ∀ y : ZMod 8, f y = f 0 + y := by
      intro y
      have hind : ∀ n : ℕ,
          f (n : ZMod 8) = f 0 + (n : ZMod 8) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Nat.cast_succ, hfor, ih]
            ring
      simpa only [ZMod.natCast_zmod_val] using hind y.val
    have hdouble : f 0 + f 0 = 0 := by
      have hi := hinvol 0
      rw [hformula] at hi
      simpa using hi
    have heven : ZModEightEvenOffset (f 0) := by
      have hfinite : ∀ z : ZMod 8,
          z + z = 0 → ZModEightEvenOffset z := by decide
      exact hfinite (f 0) hdouble
    exact (hodd 0) (by simpa using heven)
  · have hformula : ∀ y : ZMod 8, f y = f 0 - y := by
      intro y
      have hind : ∀ n : ℕ,
          f (n : ZMod 8) = f 0 - (n : ZMod 8) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Nat.cast_succ, hrev, ih]
            ring
      simpa only [ZMod.natCast_zmod_val] using hind y.val
    have hf0odd : ¬ ZModEightEvenOffset (f 0) := by
      simpa using hodd 0
    have hex : ∃ x : ZMod 8, f 0 - x = x - 1 ∨ f 0 - x = x + 1 := by
      have hfinite : ∀ z : ZMod 8, ¬ ZModEightEvenOffset z →
          ∃ x : ZMod 8, z - x = x - 1 ∨ z - x = x + 1 := by decide
      exact hfinite (f 0) hf0odd
    obtain ⟨x, hx | hx⟩ := hex
    · exact (havoid x).1 (by rw [hformula]; exact hx)
    · exact (havoid x).2 (by rw [hformula]; exact hx)

/-- The forward half-turn matching on `ZMod 8`. -/
def zmodEightHalfTurnMatrix : Matrix (ZMod 8) (ZMod 8) ℤ :=
  fun x y => if y - x = 4 then 1 else 0

theorem zmodEightHalfTurnMatrix_entry_intertwine (x y : ZMod 8) :
    zmodEightHalfTurnMatrix (x - 1) y +
        zmodEightHalfTurnMatrix (x + 1) y =
      zmodEightHalfTurnMatrix x (y + 1) +
        zmodEightHalfTurnMatrix x (y - 1) := by
  revert x y
  decide

theorem zmodEightHalfTurnMatrix_row_sum (x : ZMod 8) :
    ∑ y, zmodEightHalfTurnMatrix x y = 1 := by
  revert x
  decide

/-- A row-two binary symmetric C8 self-intertwiner with exactly one
same-parity entry in every row cannot avoid the ambient cycle edges.  The
same-parity entry is forced to be the half-turn; subtracting it produces the
forbidden oriented odd matching above. -/
theorem zmodEight_selfIntertwiner_sameParity_degreeOne_impossible
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hdiag : ∀ x, H x x = 0)
    (hsymm : ∀ x y, H x y = H y x)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    (hrow : ∀ x, ∑ y, H x y = 2)
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ZModEightEvenOffset (y - x) ∧ H x y = 1).card = 1)
    (havoid : ∀ x, H x (x - 1) = 0 ∧ H x (x + 1) = 0) : False := by
  classical
  have heven := zmodEight_selfIntertwiner_sameParity_degreeOne_offset_four
    H hdiag hsymm hinter hdegree
  let M := zmodEightHalfTurnMatrix
  let P : Matrix (ZMod 8) (ZMod 8) ℤ := H - M
  have hinterP : ∀ x y,
      P (x - 1) y + P (x + 1) y =
        P x (y + 1) + P x (y - 1) := by
    intro x y
    have hH := hinter x y
    have hM := zmodEightHalfTurnMatrix_entry_intertwine x y
    dsimp only [P, M]
    simp only [Matrix.sub_apply]
    linear_combination hH - hM
  have hbinaryP : ∀ x y, P x y = 0 ∨ P x y = 1 := by
    intro x y
    by_cases h4 : y - x = 4
    · have he : ZModEightEvenOffset (y - x) := by
        rw [h4]
        exact Or.inr (Or.inr (Or.inl rfl))
      have hH : H x y = 1 := (heven x y he).2 h4
      left
      simp [P, M, zmodEightHalfTurnMatrix, h4, hH]
    · have hM : M x y = 0 := by
        simp [M, zmodEightHalfTurnMatrix, h4]
      rcases hbinary x y with hH | hH
      · left
        simp [P, hM, hH]
      · right
        simp [P, hM, hH]
  have hrowP : ∀ x, ∑ y, P x y = 1 := by
    intro x
    calc
      ∑ y, P x y = (∑ y, H x y) - ∑ y, M x y := by
        simp only [P, Matrix.sub_apply, Finset.sum_sub_distrib]
      _ = 2 - 1 := by rw [hrow, zmodEightHalfTurnMatrix_row_sum]
      _ = 1 := by norm_num
  obtain ⟨f, hf, horient⟩ :=
    binary_rowOne_cycleIntertwiner_orientation (r := 8) (by omega)
      P hinterP hbinaryP hrowP
  have hP_one_iff_oddH (x y : ZMod 8)
      (ho : ¬ ZModEightEvenOffset (y - x)) :
      P x y = 1 ↔ H x y = 1 := by
    have h4 : y - x ≠ 4 := by
      intro h
      apply ho
      rw [h]
      exact Or.inr (Or.inr (Or.inl rfl))
    simp [P, M, zmodEightHalfTurnMatrix, h4]
  have hfOdd : ∀ x, ¬ ZModEightEvenOffset (f x - x) := by
    intro x he
    have hP : P x (f x) = 1 := (hf x (f x)).2 rfl
    have h4 := heven x (f x) he
    by_cases hoff : f x - x = 4
    · have hH := h4.mpr hoff
      simp [P, M, zmodEightHalfTurnMatrix, hoff, hH] at hP
    · have hH : H x (f x) = 0 := by
        rcases hbinary x (f x) with hz | ho
        · exact hz
        · exact (hoff (h4.mp ho)).elim
      simp [P, M, zmodEightHalfTurnMatrix, hoff, hH] at hP
  have hfAvoid : ∀ x, f x ≠ x - 1 ∧ f x ≠ x + 1 := by
    intro x
    constructor
    · intro h
      have hP : P x (f x) = 1 := (hf x (f x)).2 rfl
      have ho : ¬ ZModEightEvenOffset (f x - x) := hfOdd x
      have hH : H x (f x) = 1 := (hP_one_iff_oddH x (f x) ho).mp hP
      rw [h, (havoid x).1] at hH
      norm_num at hH
    · intro h
      have hP : P x (f x) = 1 := (hf x (f x)).2 rfl
      have ho : ¬ ZModEightEvenOffset (f x - x) := hfOdd x
      have hH : H x (f x) = 1 := (hP_one_iff_oddH x (f x) ho).mp hP
      rw [h, (havoid x).2] at hH
      norm_num at hH
  have hfInvol : ∀ x, f (f x) = x := by
    intro x
    have hP : P x (f x) = 1 := (hf x (f x)).2 rfl
    have ho : ¬ ZModEightEvenOffset (f x - x) := hfOdd x
    have hH : H x (f x) = 1 := (hP_one_iff_oddH x (f x) ho).mp hP
    have horev : ¬ ZModEightEvenOffset (x - f x) := by
      intro he
      apply ho
      rcases he with h0 | h2 | h4 | h6
      · left
        linear_combination -h0
      · right; right; right
        have : f x - x = -2 := by linear_combination -h2
        exact this.trans (by decide)
      · right; right; left
        have : f x - x = -4 := by linear_combination -h4
        exact this.trans (by decide)
      · right; left
        have : f x - x = -6 := by linear_combination -h6
        exact this.trans (by decide)
    have hP' : P (f x) x = 1 :=
      (hP_one_iff_oddH (f x) x horev).2 (by simpa [hsymm] using hH)
    exact ((hf (f x) x).1 hP').symm
  exact zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
    f hfInvol hfOdd hfAvoid horient

/-- A negation-invariant two-element support among the nonzero even offsets
of `ZMod 8` is exactly `{2,6}`. -/
theorem zmodEight_symmetric_even_degreeTwo_support
    (f : ZMod 8 → Bool)
    (_hzero : f 0 = false)
    (hneg : ∀ z, f (-z) = f z)
    (hcard : ((Finset.univ : Finset (ZMod 8)).filter fun z => f z).card = 2)
    (heven : ∀ z, f z = true → z = 2 ∨ z = 4 ∨ z = 6) :
    ∀ z, f z = true ↔ z = 2 ∨ z = 6 := by
  classical
  let S := (Finset.univ : Finset (ZMod 8)).filter fun z => f z
  have hmem (z : ZMod 8) : z ∈ S ↔ f z = true := by simp [S]
  have hScard : S.card = 2 := by simpa [S] using hcard
  have hnot4 : f 4 = false := by
    by_contra h
    have hf4 : f 4 = true := by simpa using h
    have hm4 : (4 : ZMod 8) ∈ S := (hmem 4).2 hf4
    have hone : 1 < S.card := by omega
    obtain ⟨z, hzS, hz4⟩ :=
      (Finset.one_lt_card_iff_nontrivial.mp hone).exists_ne 4
    have hfz : f z = true := (hmem z).1 hzS
    rcases heven z hfz with h2 | h4 | h6
    · subst z
      have hf6 : f 6 = true := by
        calc
          f 6 = f (-2) := congrArg f (by decide)
          _ = f 2 := hneg 2
          _ = true := hfz
      have hsub : ({2, 4, 6} : Finset (ZMod 8)) ⊆ S := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact hzS
        · exact hm4
        · exact (hmem 6).2 hf6
      have := Finset.card_le_card hsub
      have hthree : ({2, 4, 6} : Finset (ZMod 8)).card = 3 := by decide
      omega
    · exact (hz4 h4).elim
    · subst z
      have hf2 : f 2 = true := by
        calc
          f 2 = f (-6) := congrArg f (by decide)
          _ = f 6 := hneg 6
          _ = true := hfz
      have hsub : ({2, 4, 6} : Finset (ZMod 8)) ⊆ S := by
        intro w hw
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        · exact (hmem 2).2 hf2
        · exact hm4
        · exact hzS
      have := Finset.card_le_card hsub
      have hthree : ({2, 4, 6} : Finset (ZMod 8)).card = 3 := by decide
      omega
  have hsub : S ⊆ ({2, 6} : Finset (ZMod 8)) := by
    intro z hz
    have hfz := (hmem z).1 hz
    rcases heven z hfz with h2 | h4 | h6
    · simp [h2]
    · rw [h4, hnot4] at hfz
      contradiction
    · simp [h6]
  have heq : S = ({2, 6} : Finset (ZMod 8)) := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hScard]
    decide
  intro z
  rw [← hmem, heq]
  simp

/-- Recurrence-ready form: a symmetric C8 self-intertwiner with two
same-parity entries per row uses precisely offsets `±2`. -/
theorem zmodEight_selfIntertwiner_sameParity_degreeTwo_offset_two_six
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hsymm : ∀ x y, H x y = H y x)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ZModEightEvenOffset (y - x) ∧ H x y = 1).card = 2) :
    ∀ x y, ZModEightEvenOffset (y - x) →
      (H x y = 1 ↔ y - x = 2 ∨ y - x = 6) := by
  have hdiff : ∀ {x y x' y' : ZMod 8},
      ZModEightEvenOffset (y - x) → y - x = y' - x' → H x y = H x' y' := by
    intro x y x' y' he hsub
    apply selfIntertwiner_eq_of_sub_eq_of_mem_range_two H hdiag hinter ?_ hsub
    rcases he with h0 | h2 | h4 | h6
    · exact ⟨0, by rw [h0]; norm_num⟩
    · exact ⟨1, by rw [h2]; norm_num⟩
    · exact ⟨2, by rw [h4]; decide⟩
    · exact ⟨3, by rw [h6]; decide⟩
  let f : ZMod 8 → Bool := fun z =>
    decide (ZModEightEvenOffset z ∧ H 0 z = 1)
  have hzero : f 0 = false := by simp [f, ZModEightEvenOffset, hdiag]
  have hneg : ∀ z, f (-z) = f z := by
    intro z
    have heven_neg : ZModEightEvenOffset (-z) ↔ ZModEightEvenOffset z := by
      revert z
      decide
    apply Bool.eq_iff_iff.mpr
    simp only [f, decide_eq_true_eq]
    constructor
    · rintro ⟨he, hz⟩
      have he' : ZModEightEvenOffset z := heven_neg.mp he
      refine ⟨he', ?_⟩
      calc
        H 0 z = H (-z) 0 := by
          symm
          apply hdiff (x := -z) (y := 0) (x' := 0) (y' := z)
            (by simpa using he')
          ring
        _ = H 0 (-z) := hsymm _ _
        _ = 1 := hz
    · rintro ⟨he, hz⟩
      have he' : ZModEightEvenOffset (-z) := heven_neg.mpr he
      refine ⟨he', ?_⟩
      calc
        H 0 (-z) = H (-z) 0 := hsymm _ _
        _ = H 0 z := by
          apply hdiff (x := -z) (y := 0) (x' := 0) (y' := z)
            (by simpa using he)
          ring
        _ = 1 := hz
  have hcard : ((Finset.univ : Finset (ZMod 8)).filter fun z => f z).card = 2 := by
    simpa [f] using hdegree 0
  have heven : ∀ z, f z = true → z = 2 ∨ z = 4 ∨ z = 6 := by
    intro z hz
    have hz' : ZModEightEvenOffset z ∧ H 0 z = 1 := by simpa [f] using hz
    rcases hz'.1 with h0 | h2 | h4 | h6
    · subst z
      rw [hdiag] at hz'
      omega
    · exact Or.inl h2
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr h6)
  have hf := zmodEight_symmetric_even_degreeTwo_support f hzero hneg hcard heven
  intro x y he
  have hxy0 : H x y = H 0 (y - x) := by
    apply hdiff he
    ring
  have hf' := hf (y - x)
  simp only [f, decide_eq_true_eq] at hf'
  rw [hxy0]
  simpa [he] using hf'

/-- The number of same-parity entries is independent of the row in a C8
self-intertwiner. -/
theorem zmodEight_selfIntertwiner_sameParity_card_eq
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (x x' : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun y =>
      ZModEightEvenOffset (y - x) ∧ H x y = 1).card =
    ((Finset.univ : Finset (ZMod 8)).filter fun y =>
      ZModEightEvenOffset (y - x') ∧ H x' y = 1).card := by
  classical
  let S := (Finset.univ : Finset (ZMod 8)).filter fun y =>
    ZModEightEvenOffset (y - x) ∧ H x y = 1
  let T := (Finset.univ : Finset (ZMod 8)).filter fun y =>
    ZModEightEvenOffset (y - x') ∧ H x' y = 1
  change S.card = T.card
  apply Finset.card_bij (fun y _ => y - x + x')
  · intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [show (y - x + x') - x' = y - x by ring] using hy'.1
    · calc
        H x' (y - x + x') = H x y := by
          apply selfIntertwiner_eq_of_sub_eq_of_mem_range_two
            H hdiag hinter ?_ (by ring)
          rcases hy'.1 with h0 | h2 | h4 | h6
          · exact ⟨0, by rw [h0]; norm_num⟩
          · exact ⟨1, by rw [h2]; norm_num⟩
          · exact ⟨2, by rw [h4]; ring⟩
          · exact ⟨3, by rw [h6]; ring⟩
        _ = 1 := hy'.2
  · intro y₁ hy₁ y₂ hy₂ heq
    linear_combination heq
  · intro z hz
    refine ⟨z - x' + x, ?_, by ring⟩
    have hz' := (Finset.mem_filter.mp hz).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [show (z - x' + x) - x = z - x' by ring] using hz'.1
    · calc
        H x (z - x' + x) = H x' z := by
          apply selfIntertwiner_eq_of_sub_eq_of_mem_range_two
            H hdiag hinter ?_ (by ring)
          rcases hz'.1 with h0 | h2 | h4 | h6
          · exact ⟨0, by rw [h0]; norm_num⟩
          · exact ⟨1, by rw [h2]; norm_num⟩
          · exact ⟨2, by rw [h4]; ring⟩
          · exact ⟨3, by rw [h6]; ring⟩
        _ = 1 := hz'.2

end Erdos85

#print axioms Erdos85.zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
#print axioms Erdos85.zmodEight_selfIntertwiner_sameParity_degreeOne_impossible
#print axioms Erdos85.zmodEight_symmetric_even_degreeTwo_support
#print axioms Erdos85.zmodEight_selfIntertwiner_sameParity_degreeTwo_offset_two_six
#print axioms Erdos85.zmodEight_selfIntertwiner_sameParity_card_eq

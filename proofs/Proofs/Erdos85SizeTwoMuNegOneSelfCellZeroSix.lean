import Proofs.Erdos85SizeTwoMuNegOneEightEightDiagonalSameShape
import Proofs.Erdos85SizeTwoMuNegThreeEightEightParameterBounds

/-! # Eliminating the `mu=-1`, `(k,r)=(0,6)` self-switch cell -/

namespace Erdos85

noncomputable section

/-- A symmetric binary row-one C8 self-intertwiner cannot be supported only
on odd offsets while avoiding the two cycle offsets. -/
theorem zmodEight_selfIntertwiner_rowOne_odd_avoiding_cycle_impossible
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hsymm : ∀ x y, M x y = M y x)
    (hinter : ∀ x y,
      M (x - 1) y + M (x + 1) y =
        M x (y + 1) + M x (y - 1))
    (hbinary : ∀ x y, M x y = 0 ∨ M x y = 1)
    (hrow : ∀ x, ∑ y, M x y = 1)
    (hodd : ∀ x y, M x y = 1 → ¬ ZModEightEvenOffset (y - x))
    (havoid : ∀ x, M x (x - 1) = 0 ∧ M x (x + 1) = 0) : False := by
  classical
  obtain ⟨f, hf, horient⟩ :=
    binary_rowOne_cycleIntertwiner_orientation (r := 8) (by omega)
      M hinter hbinary hrow
  have hfOdd : ∀ x, ¬ ZModEightEvenOffset (f x - x) := by
    intro x
    exact hodd x (f x) ((hf x (f x)).2 rfl)
  have hfAvoid : ∀ x, f x ≠ x - 1 ∧ f x ≠ x + 1 := by
    intro x
    constructor
    · intro h
      have hM := (hf x (f x)).2 rfl
      rw [h, (havoid x).1] at hM
      norm_num at hM
    · intro h
      have hM := (hf x (f x)).2 rfl
      rw [h, (havoid x).2] at hM
      norm_num at hM
  have hfInvol : ∀ x, f (f x) = x := by
    intro x
    have hM : M x (f x) = 1 := (hf x (f x)).2 rfl
    have hM' : M (f x) x = 1 := by simpa [hsymm] using hM
    exact ((hf (f x) x).1 hM').symm
  exact zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
    f hfInvol hfOdd hfAvoid horient

/-- The normalized self-cell socket: an empty same-sign shape (`k=0`),
total diagonal degree one (`r=6`), and all-triangle cycle avoidance are
incompatible. -/
theorem zmodEight_sameSignShape_zero_rowOne_avoiding_cycle_impossible
    (M : Matrix (ZMod 8) (ZMod 8) ℤ) (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hshape : ZModEightSameSignShapeUpToThree M f 0)
    (hsymm : ∀ x y, M x y = M y x)
    (hinter : ∀ x y,
      M (x - 1) y + M (x + 1) y =
        M x (y + 1) + M x (y - 1))
    (hbinary : ∀ x y, M x y = 0 ∨ M x y = 1)
    (hrow : ∀ x, ∑ y, M x y = 1)
    (havoid : ∀ x, M x (x - 1) = 0 ∧ M x (x + 1) = 0) : False := by
  have heven := zmodEight_alternating_sign_eq_iff_evenOffset f hsign hflip
  have hempty : ∀ i j, f j = f i → M i j ≠ 1 := by
    rcases hshape with hshape | hthree
    · rcases hshape with hzero | hone | htwo
      · exact hzero.2
      · omega
      · omega
    · omega
  have hodd : ∀ x y, M x y = 1 →
      ¬ ZModEightEvenOffset (y - x) := by
    intro x y hM he
    exact (hempty x y ((heven x y).2 he)) hM
  exact zmodEight_selfIntertwiner_rowOne_odd_avoiding_cycle_impossible
    M hsymm hinter hbinary hrow hodd havoid

/-- Align an independently classified shape witness with an actual empty
same-sign row. -/
theorem zmodEight_sameSignShapeUpToThree_eq_zero_of_row_zero
    (M : Matrix (ZMod 8) (ZMod 8) ℤ) (f : ZMod 8 → ℤ) (k : ℕ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hshape : ZModEightSameSignShapeUpToThree M f k)
    (hzero : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f 0 ∧ M 0 j = 1).card = 0) :
    ZModEightSameSignShapeUpToThree M f 0 := by
  have heven := zmodEight_alternating_sign_eq_iff_evenOffset f hsign hflip
  have contradict_entry (j : ZMod 8) (he : ZModEightEvenOffset j)
      (hM : M 0 j = 1) : False := by
    have hsame : f j = f 0 := (heven 0 j).2 (by simpa using he)
    have hj : j ∈ (Finset.univ : Finset (ZMod 8)).filter fun z ↦
        f z = f 0 ∧ M 0 z = 1 := by simp [hsame, hM]
    have hp := Finset.card_pos.mpr ⟨j, hj⟩
    rw [hzero] at hp
    omega
  have hshape' := hshape
  have hk0 : k = 0 := by
    rcases hshape' with hshape | hthree
    · rcases hshape with h0 | h1 | h2
      · exact h0.1
      · exfalso
        have hM := (h1.2 0 4 ((heven 0 4).2 (by decide))).2 (by decide)
        exact contradict_entry 4 (by decide) hM
      · exfalso
        have hM := (h2.2 0 2 ((heven 0 2).2 (by decide))).2 (Or.inl (by decide))
        exact contradict_entry 2 (by decide) hM
    · exfalso
      have hM := (hthree.2 0 2 ((heven 0 2).2 (by decide))).2
        (Or.inl (by decide))
      exact contradict_entry 2 (by decide) hM
  simpa [hk0] using hshape

/-- Graph-facing normalized-shore wrapper.  A quotient-one diagonal block
with empty same-sign shape and no defect cycle edges is impossible. -/
theorem normalizedC8_quotientOne_sameSignZero_avoidingCycle_false
    {X : Type*} [Fintype X] [DecidableEq X]
    (H K : SimpleGraph X) [DecidableRel H.Adj] [DecidableRel K.Adj]
    [DecidableEq H.ConnectedComponent]
    (a : H.ConnectedComponent)
    (u : ZMod 8 → X) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdegree : ∀ x, H.degree x = 2)
    (hcommInt : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ)
    (hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ)
    (haa : componentQuotientMatrix K H a a = 1)
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hshape : ZModEightSameSignShapeUpToThree
      (fun i j ↦ K.adjMatrix ℤ (u i) (u j)) f 0)
    (havoid : ∀ i, ¬ K.Adj (u i) (u (i - 1)) ∧
      ¬ K.Adj (u i) (u (i + 1))) : False := by
  classical
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let A := (Finset.univ : Finset X).filter (fun x ↦ x ∈ a.supp)
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z ↦
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j =
        M i (j + 1) + M i (j - 1) := by
    simpa only [M] using entry_cycleIntertwine_of_adjMatrix_comm
      K H u u (1 : ZMod 8) (1 : ZMod 8) hcommInt hu hu hupair hupair
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    simp [M, SimpleGraph.adjMatrix_apply, K.adj_comm]
  have hbinary : ∀ i j, M i j = 0 ∨ M i j = 1 := by
    intro i j
    by_cases h : K.Adj (u i) (u j)
    · right
      simp [M, SimpleGraph.adjMatrix_apply, h]
    · left
      simp [M, SimpleGraph.adjMatrix_apply, h]
  have hrowCard : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M i j = 1).card = 1 := by
    intro i
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M i j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u i) (u j)) by
      ext j
      simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K A u huinj hurangeA (u i)]
    have hui : u i ∈ a.supp := by
      rw [← hurange]
      exact ⟨i, rfl⟩
    have heq : A.filter (fun y ↦ K.Adj (u i) y) =
        componentNeighborFinset K H a (u i) := by
      ext y
      simp [A, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq, ← componentQuotientMatrix_apply_eq K H 2 hdegree hcommReal
      a a hui]
    exact haa
  have hrow : ∀ i, ∑ j, M i j = 1 := by
    intro i
    calc
      ∑ j, M i j = ∑ j, if M i j = 1 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rcases hbinary i j with h0 | h1
        · simp [h0]
        · simp [h1]
      _ = (((Finset.univ : Finset (ZMod 8)).filter
          fun j ↦ M i j = 1).card : ℤ) := by
        simpa only using (Finset.sum_boole (R := ℤ)
          (fun j : ZMod 8 ↦ M i j = 1) Finset.univ)
      _ = 1 := by exact_mod_cast hrowCard i
  have havoidM : ∀ i, M i (i - 1) = 0 ∧ M i (i + 1) = 0 := by
    intro i
    constructor
    · simp [M, SimpleGraph.adjMatrix_apply, (havoid i).1]
    · simp [M, SimpleGraph.adjMatrix_apply, (havoid i).2]
  exact zmodEight_sameSignShape_zero_rowOne_avoiding_cycle_impossible
    M f hsign hflip (by simpa [M] using hshape)
      hsymm hinter hbinary hrow havoidM

/-- Final normalized router socket for the `(-1,0,6)` cell.  It accepts the
actual zero same-sign degree instead of a pre-aligned shape witness. -/
theorem graph_zmodEight_selfCell_zeroSix_false
    {X : Type*} [Fintype X] [DecidableEq X]
    (H K : SimpleGraph X) [DecidableRel H.Adj] [DecidableRel K.Adj]
    [DecidableEq H.ConnectedComponent]
    (a : H.ConnectedComponent)
    (u : ZMod 8 → X) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdegree : ∀ x, H.degree x = 2)
    (hcommInt : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ)
    (hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ)
    (haa : componentQuotientMatrix K H a a = 1)
    (s : X → ℤ)
    (hsign : ∀ i, s (u i) = -1 ∨ s (u i) = 1)
    (hflip : ∀ i, s (u (i + 1)) = -s (u i))
    (hsame : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j) = s (u i) ∧ K.Adj (u i) (u j)).card = 0)
    (havoid : ∀ i, ¬ K.Adj (u i) (u (i - 1)) ∧
      ¬ K.Adj (u i) (u (i + 1))) : False := by
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z ↦
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j =
        M i (j + 1) + M i (j - 1) := by
    simpa only [M] using entry_cycleIntertwine_of_adjMatrix_comm
      K H u u (1 : ZMod 8) (1 : ZMod 8) hcommInt hu hu hupair hupair
  have hdiag : ∀ i, M i i = 0 := by
    intro i
    simp [M, SimpleGraph.adjMatrix_apply]
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    simp [M, SimpleGraph.adjMatrix_apply, K.adj_comm]
  have hdegreeM : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j) = s (u i) ∧ M i j = 1).card = 0 := by
    intro i
    calc
      _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (u j) = s (u i) ∧ K.Adj (u i) (u j)).card := by
        congr 1
        ext j
        simp [M, SimpleGraph.adjMatrix_apply]
      _ = 0 := hsame i
  have hshape := zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_three
    M (fun i ↦ s (u i)) 0 (by omega) hsign hflip hdiag hsymm hinter hdegreeM
  exact normalizedC8_quotientOne_sameSignZero_avoidingCycle_false
    H K a u huinj hurange hu hdegree hcommInt hcommReal haa
      (fun i ↦ s (u i)) hsign hflip (by simpa [M] using hshape) havoid

end

end Erdos85

#print axioms Erdos85.zmodEight_selfIntertwiner_rowOne_odd_avoiding_cycle_impossible
#print axioms Erdos85.zmodEight_sameSignShape_zero_rowOne_avoiding_cycle_impossible
#print axioms Erdos85.normalizedC8_quotientOne_sameSignZero_avoidingCycle_false
#print axioms Erdos85.zmodEight_sameSignShapeUpToThree_eq_zero_of_row_zero
#print axioms Erdos85.graph_zmodEight_selfCell_zeroSix_false

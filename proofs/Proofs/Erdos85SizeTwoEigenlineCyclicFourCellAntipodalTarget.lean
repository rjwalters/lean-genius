import Proofs.Erdos85SizeTwoEigenlineCyclicFiveCellSubsystem
import Proofs.Erdos85SizeTwoEigenlineCyclicSelectedFiberGraph

/-!
# Four short cells force the middle antipodal collision

The fiber-resolved `q = 8` core factors more sharply than the five-cell
interface suggests.  After removing the middle antipodal cap, the remaining
four short-shift caps force two agreements between antipodal sources in the
middle fiber.  Reinstating the fifth cap immediately contradicts that forced
collision.

This file packages the q-generic form of that factorization.  It proves the
consumer, not the forcing statement: the latter is the remaining mathematical
leaf suggested by the exact core.
-/

namespace Erdos85

noncomputable section

/-- The five-cell subsystem with its middle antipodal cap removed. -/
structure SizeTwoCyclicLooplessFourCellCode
    (q : ℕ) [NeZero q] (a : ZMod q)
    (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ : ZMod q) where
  code : SizeTwoCyclicReciprocalPermutationCode q a
  loopless : code.Loopless
  left_d₁ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₁ left left) ≤ 1
  left_d₂ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₂ left left) ≤ 1
  middle_d₁ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₁ middle middle) ≤ 1
  right_d₂ : ∀ x, Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a code.toPermutationCode.perm x d₂ right right) ≤ 1

/-- Forget the fifth, middle-`m` cap. -/
def SizeTwoCyclicLooplessFiveCellCode.toFourCellCode
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ m : ZMod q}
    (five : SizeTwoCyclicLooplessFiveCellCode q a
      left middle right d₁ d₂ m) :
    SizeTwoCyclicLooplessFourCellCode q a
      left middle right d₁ d₂ where
  code := five.code
  loopless := five.loopless
  left_d₁ := five.left_d₁
  left_d₂ := five.left_d₂
  middle_d₁ := five.middle_d₁
  right_d₂ := five.right_d₂

/-- Two common targets for a pair of middle-fiber sources separated by `m`.
Under the selected-fiber graph interpretation this is an antipodal rectangle. -/
def SizeTwoCyclicLooplessFourCellCode.HasMiddleAntipodalCollision
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ : ZMod q}
    (four : SizeTwoCyclicLooplessFourCellCode q a
      left middle right d₁ d₂)
    (m : ZMod q) : Prop :=
  ∃ x : ZMod q,
    2 ≤ Fintype.card (SizeTwoCrossShiftedPermutationAgreement
      q a four.code.toPermutationCode.perm x m middle middle)

/-- A nonempty propagated order-four step cycle in the selected middle graph
produces the required antipodal collision.  This is the graph-theoretic
consumer for the structural pattern seen in the exact `q = 8` core. -/
theorem SizeTwoCyclicLooplessFourCellCode.hasMiddleAntipodalCollision_of_stepCycle
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ : ZMod q}
    (four : SizeTwoCyclicLooplessFourCellCode q a
      left middle right d₁ d₂)
    (d : ZMod q) (hdouble : d + d ≠ 0)
    (hfour : d + d + d + d = 0)
    (hedge : ∃ x : ZMod q,
      (sizeTwoCyclicSelectedFiberGraph four.code middle).Adj x (x + d))
    (hpropagate : ∀ x : ZMod q,
      (sizeTwoCyclicSelectedFiberGraph four.code middle).Adj x (x + d) →
      (sizeTwoCyclicSelectedFiberGraph four.code middle).Adj
        (x + d) (x + d + d)) :
    four.HasMiddleAntipodalCollision (d + d) := by
  classical
  let G := sizeTwoCyclicSelectedFiberGraph four.code middle
  letI : DecidableRel G.Adj := Classical.decRel _
  obtain ⟨x, hx₁⟩ := hedge
  have hx₂ : G.Adj (x + d) (x + d + d) := hpropagate x hx₁
  have hx₃ : G.Adj (x + d + d) (x + d + d + d) :=
    hpropagate (x + d) hx₂
  have hx₄raw : G.Adj (x + d + d + d) (x + d + d + d + d) :=
    hpropagate (x + d + d) hx₃
  have hx₄ : G.Adj x (x + d + d + d) := by
    have hclose : x + d + d + d + d = x := by
      rw [show x + d + d + d + d = x + (d + d + d + d) by abel,
        hfour, add_zero]
    rw [hclose] at hx₄raw
    exact hx₄raw.symm
  have hneighbors₁ : x + d ∈
      G.neighborFinset x ∩ G.neighborFinset (x + (d + d)) := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (G.mem_neighborFinset x (x + d)).mpr hx₁
    · apply (G.mem_neighborFinset (x + (d + d)) (x + d)).mpr
      convert hx₂.symm using 1 <;> abel
  have hneighbors₂ : x + d + d + d ∈
      G.neighborFinset x ∩ G.neighborFinset (x + (d + d)) := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (G.mem_neighborFinset x (x + d + d + d)).mpr hx₄
    · apply (G.mem_neighborFinset (x + (d + d))
        (x + d + d + d)).mpr
      convert hx₃ using 1 <;> abel
  have hdistinct : x + d ≠ x + d + d + d := by
    intro h
    apply hdouble
    have h' : (x + d) + (d + d) = (x + d) + 0 := by
      calc
        (x + d) + (d + d) = x + d + d + d := by abel
        _ = x + d := h.symm
        _ = (x + d) + 0 := (add_zero _).symm
    exact add_left_cancel h'
  refine ⟨x, ?_⟩
  calc
    2 = ({x + d, x + d + d + d} : Finset (ZMod q)).card := by
      rw [Finset.card_pair hdistinct]
    _ ≤ (G.neighborFinset x ∩
          G.neighborFinset (x + (d + d))).card := by
      apply Finset.card_le_card
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact hneighbors₁
      · exact hneighbors₂
    _ = Fintype.card {y : ZMod q // y ∈
          G.neighborFinset x ∩ G.neighborFinset (x + (d + d))} :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card {e : SizeTwoCyclicAbsoluteGridEdge q //
          e ∈ sizeTwoCyclicRawSourceMatching
              four.code.toPermutationCode.perm (x, middle) ∩
            sizeTwoCyclicRawSourceMatching
              four.code.toPermutationCode.perm (x + (d + d), middle)} :=
      Fintype.card_le_of_injective
        (sizeTwoCyclicSelectedFiberCommonNeighborToIntersection
          four.code four.loopless middle x (x + (d + d)))
        (sizeTwoCyclicSelectedFiberCommonNeighborToIntersection_injective
          four.code four.loopless middle x (x + (d + d)))
    _ = Fintype.card (SizeTwoCrossShiftedPermutationAgreement
          q a four.code.toPermutationCode.perm x (d + d) middle middle) := by
      rw [Fintype.card_coe]
      simpa using
        (sizeTwoCyclicRawSourceMatching_inter_card_eq_agreement
          four.code.toPermutationCode.perm (x, middle)
            (x + (d + d), middle))

/-- The exact new leaf: every four-cell code has a middle antipodal
collision. -/
def SizeTwoCyclicLooplessFourCellAntipodalForcing
    (q : ℕ) [NeZero q] (a : ZMod q)
    (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ m : ZMod q) : Prop :=
  ∀ four : SizeTwoCyclicLooplessFourCellCode q a
      left middle right d₁ d₂,
    four.HasMiddleAntipodalCollision m

/-- Four-cell antipodal forcing contradicts the fifth cap. -/
theorem isEmpty_sizeTwoCyclicLooplessFiveCellCode_of_fourCellAntipodalForcing
    {q : ℕ} [NeZero q] {a : ZMod q}
    {left middle right : sizeTwoAllowedDifference q a}
    {d₁ d₂ m : ZMod q}
    (hforce : SizeTwoCyclicLooplessFourCellAntipodalForcing q a
      left middle right d₁ d₂ m) :
    IsEmpty (SizeTwoCyclicLooplessFiveCellCode q a
      left middle right d₁ d₂ m) := by
  constructor
  intro five
  obtain ⟨x, htwo⟩ := hforce five.toFourCellCode
  change 2 ≤ Fintype.card (SizeTwoCrossShiftedPermutationAgreement
    q a five.code.toPermutationCode.perm x m middle middle) at htwo
  have hone := five.middle_m x
  omega

/-- A selected four-cell forcing statement supplies the previously packaged
five-cell exclusion. -/
theorem sizeTwoCyclicLooplessFiveCellExclusion_of_fourCellAntipodalForcing
    {q : ℕ} [NeZero q] {a : ZMod q}
    (left middle right : sizeTwoAllowedDifference q a)
    (d₁ d₂ m : ZMod q)
    (hlm : left ≠ middle) (hmr : middle ≠ right)
    (hlr : left ≠ right)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (hm : m ≠ 0)
    (hm2 : m + m = 0)
    (hforce : SizeTwoCyclicLooplessFourCellAntipodalForcing q a
      left middle right d₁ d₂ m) :
    SizeTwoCyclicLooplessFiveCellExclusion q a := by
  exact ⟨left, middle, right, d₁, d₂, m,
    hlm, hmr, hlr, hd₁, hd₂, hm, hm2,
    isEmpty_sizeTwoCyclicLooplessFiveCellCode_of_fourCellAntipodalForcing
      hforce⟩

end

end Erdos85

#print axioms
  Erdos85.isEmpty_sizeTwoCyclicLooplessFiveCellCode_of_fourCellAntipodalForcing
#print axioms
  Erdos85.sizeTwoCyclicLooplessFiveCellExclusion_of_fourCellAntipodalForcing

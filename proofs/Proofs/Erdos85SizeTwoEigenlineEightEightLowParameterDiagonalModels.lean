import Proofs.Erdos85ZModEightMixedSelfIntertwinerExclusion

/-!
# Diagonal kernels for the low `8+8` quotient parameters

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

For an all-triangle-free C8 shore, the two cycle edges are the two
opposite-sign defect edges.  The remaining diagonal defect entries therefore
have even offset.  At quotient parameters three and two their row degrees
are respectively two and three.  Degree two was classified previously as
offsets `±2`; this file supplies the degree-three endpoint: every nonzero
even offset occurs.
-/

namespace Erdos85

/-- A loopless binary matrix on `ZMod 8` with three even-offset entries in
each row contains precisely the three nonzero even offsets `2,4,6`.

No intertwining hypothesis is needed at this maximal even-offset degree;
there are only three available nonzero even differences. -/
theorem zmodEight_sameParity_degreeThree_offset_two_four_six
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ZModEightEvenOffset (y - x) ∧ H x y = 1).card = 3) :
    ∀ x y, ZModEightEvenOffset (y - x) →
      (H x y = 1 ↔ y - x = 2 ∨ y - x = 4 ∨ y - x = 6) := by
  classical
  intro x y heven
  let S := (Finset.univ : Finset (ZMod 8)).filter fun z =>
    ZModEightEvenOffset (z - x) ∧ H x z = 1
  let T : Finset (ZMod 8) := {x + 2, x + 4, x + 6}
  have hSsub : S ⊆ T := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    rcases hz'.1 with h0 | h2 | h4 | h6
    · have hzEq : z = x := by linear_combination h0
      subst z
      rw [hdiag] at hz'
      omega
    · have hzEq : z = x + 2 := by linear_combination h2
      simp [T, hzEq]
    · have hzEq : z = x + 4 := by linear_combination h4
      simp [T, hzEq]
    · have hzEq : z = x + 6 := by linear_combination h6
      simp [T, hzEq]
  have hScard : S.card = 3 := by simpa [S] using hdegree x
  have hTcard : T.card = 3 := by
    dsimp only [T]
    have h24 : x + (2 : ZMod 8) ≠ x + 4 := by
      intro h
      have : (2 : ZMod 8) = 4 := add_left_cancel h
      contradiction
    have h26 : x + (2 : ZMod 8) ≠ x + 6 := by
      intro h
      have : (2 : ZMod 8) = 6 := add_left_cancel h
      contradiction
    have h46 : x + (4 : ZMod 8) ≠ x + 6 := by
      intro h
      have : (4 : ZMod 8) = 6 := add_left_cancel h
      contradiction
    simp [h24, h26, h46]
  have hST : S = T := Finset.eq_of_subset_of_card_le hSsub (by omega)
  have hyMem : y ∈ S ↔ H x y = 1 := by simp [S, heven]
  rw [← hyMem, hST]
  simp only [T, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h | h
    · left; linear_combination h
    · right; left; linear_combination h
    · right; right; linear_combination h
  · intro h
    rcases h with h | h | h
    · left; linear_combination h
    · right; left; linear_combination h
    · right; right; linear_combination h

end Erdos85

#print axioms Erdos85.zmodEight_sameParity_degreeThree_offset_two_four_six

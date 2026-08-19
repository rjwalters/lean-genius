import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingDesign
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationInvolution

/-!
# Reciprocity of the absolute matching design

Permutation reciprocity says more geometrically that incidence in the
absolute matching design is symmetric.  A routed edge from source cell
`(x,x+t)` to target cell `(x+r,x+r+s)` becomes, on reversal, the routed edge
from that target cell back to the original source cell.
-/

namespace Erdos85

noncomputable section

/-- Absolute-grid coordinate of a cyclic matching source. -/
def sizeTwoCyclicMatchingSourceCell
    {q : ℕ} {a : ZMod q}
    (source : SizeTwoCyclicMatchingSource q a) :
    SizeTwoCyclicAbsoluteGridEdge q :=
  (source.1, source.1 + source.2.1)

/-- The reverse route sends a matching edge back to its source cell. -/
theorem sizeTwoCyclicMatchingEdge_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let reciprocal := code.toReciprocalCode
    let s := reciprocal.targetDifference x t r
    let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
      ⟨-r.1, reciprocal.reverse_admissible x t r⟩
    sizeTwoCyclicMatchingEdge code (x + r.1, s) reverseRow =
      (x, x + t.1) := by
  dsimp only
  let reciprocal := code.toReciprocalCode
  let s := reciprocal.targetDifference x t r
  let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
    ⟨-r.1, reciprocal.reverse_admissible x t r⟩
  apply Prod.ext
  · simp [sizeTwoCyclicMatchingEdge]
  · change (x + r.1) +
        (reciprocal.toPermutationCode.perm (x + r.1) s reverseRow).1 =
      x + t.1
    rw [reciprocal.reciprocity x t r]
    dsimp [reverseRow]
    abel

/-- Every forward matching incidence produces the reverse incidence of the
source cell in the target cell's matching. -/
theorem sizeTwoCyclicSourceCell_mem_reverseMatching
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let reciprocal := code.toReciprocalCode
    let s := reciprocal.targetDifference x t r
    (x, x + t.1) ∈
      sizeTwoCyclicSourceMatching code (x + r.1, s) := by
  dsimp only
  let reciprocal := code.toReciprocalCode
  let s := reciprocal.targetDifference x t r
  let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
    ⟨-r.1, reciprocal.reverse_admissible x t r⟩
  apply (sizeTwoCyclicSourceMatching_mem_iff code (x + r.1, s) _).mpr
  exact ⟨reverseRow, sizeTwoCyclicMatchingEdge_reverse code x t r⟩

/-- Coordinate-free incidence transpose: if an absolute cell lies in a
source matching, then the source cell lies in the matching based at that
absolute cell (with the uniquely routed target difference). -/
theorem sizeTwoCyclicSourceMatching_mem_reverse_exists
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (e : SizeTwoCyclicAbsoluteGridEdge q)
    (he : e ∈ sizeTwoCyclicSourceMatching code (x, t)) :
    ∃ s : sizeTwoAllowedDifference q a,
      (x, x + t.1) ∈ sizeTwoCyclicSourceMatching code (e.1, s) := by
  obtain ⟨r, hr⟩ :=
    (sizeTwoCyclicSourceMatching_mem_iff code (x, t) e).mp he
  let s := code.toReciprocalCode.targetDifference x t r
  refine ⟨s, ?_⟩
  have hreverse := sizeTwoCyclicSourceCell_mem_reverseMatching code x t r
  have hfirst := congrArg Prod.fst hr
  change x + r.1 = e.1 at hfirst
  simpa only [hfirst] using hreverse

/-- The reverse matching's fiber is exactly the absolute difference of the
target cell. -/
theorem sizeTwoCyclicSourceMatching_mem_reverse_exists_eq_difference
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (e : SizeTwoCyclicAbsoluteGridEdge q)
    (he : e ∈ sizeTwoCyclicSourceMatching code (x, t)) :
    ∃ s : sizeTwoAllowedDifference q a,
      s.1 = e.2 - e.1 ∧
      (x, x + t.1) ∈ sizeTwoCyclicSourceMatching code (e.1, s) := by
  obtain ⟨r, hr⟩ :=
    (sizeTwoCyclicSourceMatching_mem_iff code (x, t) e).mp he
  let s := code.toReciprocalCode.targetDifference x t r
  refine ⟨s, ?_, ?_⟩
  · have hfirst := congrArg Prod.fst hr
    have hsecond := congrArg Prod.snd hr
    have hcolumn := code.toReciprocalCode.target_column_eq x t r
    dsimp [sizeTwoCyclicMatchingEdge] at hfirst hsecond
    change r.1 + s.1 =
      (code.toReciprocalCode.toPermutationCode.perm x t r).1 at hcolumn
    rw [← hsecond, ← hfirst]
    rw [← hcolumn]
    abel
  · have hreverse := sizeTwoCyclicSourceCell_mem_reverseMatching code x t r
    have hfirst := congrArg Prod.fst hr
    change x + r.1 = e.1 at hfirst
    simpa only [hfirst] using hreverse

/-- Reciprocity in its intrinsic matching-design form: after identifying
sources with their absolute cells, matching incidence is symmetric. -/
theorem sizeTwoCyclicSourceMatching_sourceCell_mem_comm
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (source target : SizeTwoCyclicMatchingSource q a) :
    sizeTwoCyclicMatchingSourceCell target ∈
        sizeTwoCyclicSourceMatching code source ↔
      sizeTwoCyclicMatchingSourceCell source ∈
        sizeTwoCyclicSourceMatching code target := by
  constructor
  · intro h
    obtain ⟨s, hs, hmem⟩ :=
      sizeTwoCyclicSourceMatching_mem_reverse_exists_eq_difference
        code source.1 source.2 (sizeTwoCyclicMatchingSourceCell target) h
    have hst : s = target.2 := by
      apply Subtype.ext
      simpa [sizeTwoCyclicMatchingSourceCell] using hs
    simpa [sizeTwoCyclicMatchingSourceCell, hst] using hmem
  · intro h
    obtain ⟨s, hs, hmem⟩ :=
      sizeTwoCyclicSourceMatching_mem_reverse_exists_eq_difference
        code target.1 target.2 (sizeTwoCyclicMatchingSourceCell source) h
    have hss : s = source.2 := by
      apply Subtype.ext
      simpa [sizeTwoCyclicMatchingSourceCell] using hs
    simpa [sizeTwoCyclicMatchingSourceCell, hss] using hmem

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicMatchingEdge_reverse
#print axioms Erdos85.sizeTwoCyclicSourceCell_mem_reverseMatching
#print axioms Erdos85.sizeTwoCyclicSourceMatching_mem_reverse_exists
#print axioms Erdos85.sizeTwoCyclicSourceMatching_mem_reverse_exists_eq_difference
#print axioms Erdos85.sizeTwoCyclicSourceMatching_sourceCell_mem_comm

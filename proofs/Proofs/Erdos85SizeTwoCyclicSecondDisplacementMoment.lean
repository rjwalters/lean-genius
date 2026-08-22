import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationInvolution

/-!
# The second displacement moment of a punctured routing permutation

Node: `BinarySizeTwoCyclicPackingBound` beneath `GAP A-REG-NONBIP`.

The first displacement moment remembers only target-fiber multiplicities.
The quadratic moment below retains the correlation between the relative row
and its target difference, and in particular sees the row-zero resolver
involution.
-/

namespace Erdos85

noncomputable section

private noncomputable instance admissibleTargetRowFintype
    {q : ℕ} [NeZero q] (t : ZMod q) :
    Fintype (SizeTwoAdmissibleTargetRow q t) := by
  unfold SizeTwoAdmissibleTargetRow
  infer_instance

private noncomputable instance admissibleTargetColumnFintype
    {q : ℕ} [NeZero q] : Fintype (SizeTwoAdmissibleTargetColumn q) := by
  unfold SizeTwoAdmissibleTargetColumn
  infer_instance

private theorem one_ne_zero_zmod
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) : (1 : ZMod q) ≠ 0 := by
  letI : Fact (1 < q) := ⟨by omega⟩
  exact one_ne_zero

private theorem admissibleTargetRow_sq_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (t : ZMod q) :
    (∑ r : SizeTwoAdmissibleTargetRow q t, r.1 ^ 2) =
      (∑ z : ZMod q, z ^ 2) - t ^ 2 - (t + 1) ^ 2 := by
  classical
  let s := ((Finset.univ : Finset (ZMod q)).erase t).erase (t + 1)
  have hmem : ∀ z : ZMod q,
      z ∈ s ↔ t ≠ z ∧ t ≠ z - 1 := by
    intro z
    simp only [s, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨hz₂, hz₁⟩
      refine ⟨Ne.symm hz₁, ?_⟩
      intro htz
      apply hz₂
      have := congrArg (fun w : ZMod q => w + 1) htz
      simpa [sub_eq_add_neg, add_assoc] using this.symm
    · rintro ⟨hz₁, hz₂⟩
      refine ⟨?_, Ne.symm hz₁⟩
      intro hz
      apply hz₂
      rw [hz]
      simp
  change (∑ r : {r : ZMod q // t ≠ r ∧ t ≠ r - 1}, r.1 ^ 2) = _
  let rowFintype : Fintype {r : ZMod q // t ≠ r ∧ t ≠ r - 1} := by
    infer_instance
  have hs := @Finset.sum_subtype (ZMod q) (ZMod q) _
    (fun r => t ≠ r ∧ t ≠ r - 1) rowFintype
    s hmem (fun z : ZMod q => z ^ 2)
  rw [← hs]
  have hne : t + 1 ≠ t := by
    intro h
    apply one_ne_zero_zmod hq
    have h' : t + 1 = t + 0 := by simpa using h
    exact add_left_cancel h'
  have houter := Finset.sum_erase_add
    (Finset.univ.erase t) (fun z : ZMod q => z ^ 2) (by simpa [hne])
  have hinner := Finset.sum_erase_add
    (Finset.univ : Finset (ZMod q)) (fun z : ZMod q => z ^ 2)
      (Finset.mem_univ t)
  have hinnerEq : (∑ z ∈ Finset.univ.erase t, z ^ 2) =
      (∑ z : ZMod q, z ^ 2) - t ^ 2 := by
    rw [eq_sub_iff_add_eq]
    exact hinner
  calc
    ∑ z ∈ s, z ^ 2 = (∑ z ∈ Finset.univ.erase t, z ^ 2) - (t + 1) ^ 2 := by
      rw [eq_sub_iff_add_eq]
      exact houter
    _ = (∑ z : ZMod q, z ^ 2) - t ^ 2 - (t + 1) ^ 2 := by
      rw [hinnerEq]

private theorem admissibleTargetColumn_sq_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) :
    (∑ c : SizeTwoAdmissibleTargetColumn q, c.1 ^ 2) =
      (∑ z : ZMod q, z ^ 2) - 0 ^ 2 - (-1) ^ 2 := by
  classical
  let s := ((Finset.univ : Finset (ZMod q)).erase 0).erase (-1)
  have hmem : ∀ z : ZMod q, z ∈ s ↔ z ≠ 0 ∧ z ≠ -1 := by
    intro z
    simp [s, and_comm]
  change (∑ c : {c : ZMod q // c ≠ 0 ∧ c ≠ -1}, c.1 ^ 2) = _
  let columnFintype : Fintype {c : ZMod q // c ≠ 0 ∧ c ≠ -1} := by
    infer_instance
  have hs := @Finset.sum_subtype (ZMod q) (ZMod q) _
    (fun c => c ≠ 0 ∧ c ≠ -1) columnFintype
    s hmem (fun z : ZMod q => z ^ 2)
  rw [← hs]
  have hne : (-1 : ZMod q) ≠ 0 := neg_ne_zero.mpr (one_ne_zero_zmod hq)
  have houter := Finset.sum_erase_add
    (Finset.univ.erase (0 : ZMod q)) (fun z : ZMod q => z ^ 2)
      (by simpa [hne])
  have hinner := Finset.sum_erase_add
    (Finset.univ : Finset (ZMod q)) (fun z : ZMod q => z ^ 2)
      (Finset.mem_univ (0 : ZMod q))
  have hinnerEq : (∑ z ∈ Finset.univ.erase (0 : ZMod q), z ^ 2) =
      (∑ z : ZMod q, z ^ 2) - 0 ^ 2 := by
    rw [eq_sub_iff_add_eq]
    exact hinner
  calc
    ∑ z ∈ s, z ^ 2 =
        (∑ z ∈ Finset.univ.erase (0 : ZMod q), z ^ 2) - (-1) ^ 2 := by
      rw [eq_sub_iff_add_eq]
      exact houter
    _ = (∑ z : ZMod q, z ^ 2) - 0 ^ 2 - (-1) ^ 2 := by
      rw [hinnerEq]

/-- Exact quadratic displacement identity.  If `u_r` is the target
difference of relative row `r`, then
`sum_r (2*r*u_r + u_r^2) = 2*t*(t+1)`. -/
theorem sizeTwoCyclicPermutation_targetDifference_secondMoment
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ r : SizeTwoAdmissibleTargetRow q t.1, (
      2 * r.1 * (code.targetDifference x t r).1 +
        ((code.targetDifference x t r).1 : ZMod q) ^ 2)) =
      2 * t.1 * (t.1 + 1) := by
  classical
  calc
    (∑ r : SizeTwoAdmissibleTargetRow q t.1, (
        2 * r.1 * (code.targetDifference x t r).1 +
          ((code.targetDifference x t r).1 : ZMod q) ^ 2)) =
        ∑ r : SizeTwoAdmissibleTargetRow q t.1, (
          (code.toPermutationCode.perm x t r).1 ^ 2 - r.1 ^ 2) := by
      apply Finset.sum_congr rfl
      intro r _
      have h := code.target_column_eq x t r
      rw [← h]
      ring
    _ = (∑ c : SizeTwoAdmissibleTargetColumn q, c.1 ^ 2) -
        ∑ r : SizeTwoAdmissibleTargetRow q t.1, r.1 ^ 2 := by
      rw [Finset.sum_sub_distrib]
      congr 1
      exact Equiv.sum_comp (code.toPermutationCode.perm x t)
        (fun c : SizeTwoAdmissibleTargetColumn q => c.1 ^ 2)
    _ = 2 * t.1 * (t.1 + 1) := by
      rw [admissibleTargetColumn_sq_sum hq, admissibleTargetRow_sq_sum hq]
      ring

/-- Binary mod-four shadow of the quadratic displacement identity.  The
right-hand side vanishes because the product of two consecutive residues is
even. -/
theorem sizeTwoCyclicPermutation_targetDifference_secondMoment_modFour
    {q : ℕ} [NeZero q] (h4q : 4 ∣ q) {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ r : SizeTwoAdmissibleTargetRow q t.1, (
      2 * ZMod.castHom h4q (ZMod 4) r.1 *
          ZMod.castHom h4q (ZMod 4) (code.targetDifference x t r).1 +
        (ZMod.castHom h4q (ZMod 4)
          (code.targetDifference x t r).1) ^ 2)) = 0 := by
  have hq : 2 ≤ q := by
    obtain ⟨k, rfl⟩ := h4q
    have hk : k ≠ 0 := by
      intro hk
      subst k
      exact NeZero.ne 0 rfl
    omega
  have h := congrArg (ZMod.castHom h4q (ZMod 4))
    (sizeTwoCyclicPermutation_targetDifference_secondMoment hq code x t)
  rw [map_sum] at h
  simp only [map_add, map_mul, map_pow, map_ofNat, map_one] at h
  have hconsecutive : ∀ z : ZMod 4, 2 * z * (z + 1) = 0 := by decide
  simpa only [hconsecutive] using h

/-!
The mod-four shadow is recorded as a normalization lemma, not as an
obstruction.  Indeed the admissible domain rows and target columns each have
equally many even and odd elements.  If `B` routes go from odd rows to even
columns, the opposite mismatch count is also `B`; the number `O` of odd
target differences is therefore `2B`, and the displayed congruence reads
`4B=0`.  Any new pressure from the quadratic identity must retain higher
2-adic information (or the actual row labels), rather than reduce immediately
to parity.
-/

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicPermutation_targetDifference_secondMoment
#print axioms Erdos85.sizeTwoCyclicPermutation_targetDifference_secondMoment_modFour

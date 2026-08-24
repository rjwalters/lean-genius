import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationCode
import Proofs.Erdos85SizeTwoEigenlineCyclicEvenReflection

/-!
# The punctured-permutation displacement sum

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

Every routing permutation omits the two rows `t,t+1` and the two columns
`0,-1`.  Consequently the sum of its target-difference labels is forced,
independently of the permutation itself.  This retains a first additive
constraint that is invisible in the aggregate orbit multiplicities.
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

private theorem admissibleTargetRow_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (t : ZMod q) :
    (∑ r : SizeTwoAdmissibleTargetRow q t, r.1) =
      (∑ z : ZMod q, z) - t - (t + 1) := by
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
  change (∑ r : {r : ZMod q // t ≠ r ∧ t ≠ r - 1}, r.1) = _
  let rowFintype : Fintype {r : ZMod q // t ≠ r ∧ t ≠ r - 1} := by
    infer_instance
  have hs := @Finset.sum_subtype (ZMod q) (ZMod q) _
    (fun r => t ≠ r ∧ t ≠ r - 1) rowFintype
    s hmem (fun z : ZMod q => z)
  rw [← hs]
  have hne : t + 1 ≠ t := by
    intro h
    apply one_ne_zero_zmod hq
    have h' : t + 1 = t + 0 := by simpa using h
    exact add_left_cancel h'
  have houter := Finset.sum_erase_add
    (Finset.univ.erase t) (fun z : ZMod q => z) (by simpa [hne])
  have hinner := Finset.sum_erase_add
    (Finset.univ : Finset (ZMod q)) (fun z : ZMod q => z)
      (Finset.mem_univ t)
  have hinnerEq : (∑ z ∈ Finset.univ.erase t, z) =
      (∑ z : ZMod q, z) - t := by
    rw [eq_sub_iff_add_eq]
    exact hinner
  calc
    ∑ z ∈ s, z = (∑ z ∈ Finset.univ.erase t, z) - (t + 1) := by
      rw [eq_sub_iff_add_eq]
      exact houter
    _ = (∑ z : ZMod q, z) - t - (t + 1) := by
      rw [hinnerEq]

private theorem admissibleTargetColumn_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) :
    (∑ c : SizeTwoAdmissibleTargetColumn q, c.1) =
      (∑ z : ZMod q, z) - 0 - (-1) := by
  classical
  let s := ((Finset.univ : Finset (ZMod q)).erase 0).erase (-1)
  have hmem : ∀ z : ZMod q, z ∈ s ↔ z ≠ 0 ∧ z ≠ -1 := by
    intro z
    simp [s, and_comm]
  change (∑ c : {c : ZMod q // c ≠ 0 ∧ c ≠ -1}, c.1) = _
  let columnFintype : Fintype {c : ZMod q // c ≠ 0 ∧ c ≠ -1} := by
    infer_instance
  have hs := @Finset.sum_subtype (ZMod q) (ZMod q) _
    (fun c => c ≠ 0 ∧ c ≠ -1) columnFintype
    s hmem (fun z : ZMod q => z)
  rw [← hs]
  have hne : (-1 : ZMod q) ≠ 0 := neg_ne_zero.mpr (one_ne_zero_zmod hq)
  have houter := Finset.sum_erase_add
    (Finset.univ.erase (0 : ZMod q)) (fun z : ZMod q => z) (by simpa [hne])
  have hinner := Finset.sum_erase_add
    (Finset.univ : Finset (ZMod q)) (fun z : ZMod q => z)
      (Finset.mem_univ (0 : ZMod q))
  have hinnerEq : (∑ z ∈ Finset.univ.erase (0 : ZMod q), z) =
      (∑ z : ZMod q, z) - 0 := by
    rw [eq_sub_iff_add_eq]
    exact hinner
  calc
    ∑ z ∈ s, z = (∑ z ∈ Finset.univ.erase (0 : ZMod q), z) - (-1) := by
      rw [eq_sub_iff_add_eq]
      exact houter
    _ = (∑ z : ZMod q, z) - 0 - (-1) := by
      rw [hinnerEq]

/-- The total target-difference label of a punctured routing permutation is
forced by its two omitted rows and columns. -/
theorem sizeTwoCyclicPermutation_targetDifference_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ r : SizeTwoAdmissibleTargetRow q t.1,
        ((P x t r : SizeTwoAdmissibleTargetColumn q).1 -
          (r : SizeTwoAdmissibleTargetRow q t.1).1)) =
      2 * (t.1 + 1) := by
  classical
  rw [Finset.sum_sub_distrib]
  rw [Equiv.sum_comp (P x t)]
  rw [admissibleTargetColumn_sum hq, admissibleTargetRow_sum hq]
  ring

/-- The two routing lines in a reflected allowed-fibre pair carry constant
total displacement charge `2`, independently of the fibre and routing
permutations. -/
theorem sizeTwoCyclicPermutation_reflectionPair_targetDifference_sum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ r : SizeTwoAdmissibleTargetRow q t.1,
        ((P x t r : SizeTwoAdmissibleTargetColumn q).1 - r.1)) +
      (∑ r : SizeTwoAdmissibleTargetRow q
          (sizeTwoAllowedDifferenceReflection q a t).1,
        ((P x (sizeTwoAllowedDifferenceReflection q a t) r :
            SizeTwoAdmissibleTargetColumn q).1 - r.1)) = 2 := by
  rw [sizeTwoCyclicPermutation_targetDifference_sum hq,
    sizeTwoCyclicPermutation_targetDifference_sum hq,
    sizeTwoAllowedDifferenceReflection_val]
  ring

/-- For even `q`, every routing permutation contains an even total parity of
target-difference labels.  This is the characteristic-two shadow of the exact
displacement-sum identity. -/
theorem sizeTwoCyclicPermutation_targetDifference_parity_sum
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) {a : ZMod q}
    (P : SizeTwoCyclicPermutationFamily q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (∑ r : SizeTwoAdmissibleTargetRow q t.1,
      ZMod.castHom h2q (ZMod 2)
        ((P x t r : SizeTwoAdmissibleTargetColumn q).1 -
          (r : SizeTwoAdmissibleTargetRow q t.1).1)) = 0 := by
  classical
  have hq : 2 ≤ q := by
    obtain ⟨k, rfl⟩ := h2q
    have hk : k ≠ 0 := by
      intro hk
      subst hk
      exact NeZero.ne 0 rfl
    omega
  have h := congrArg (ZMod.castHom h2q (ZMod 2))
    (sizeTwoCyclicPermutation_targetDifference_sum hq P x t)
  rw [map_sum] at h
  have htwo : ZMod.castHom h2q (ZMod 2) (2 : ZMod q) = 0 := by
    simpa only [map_ofNat] using (show (2 : ZMod 2) = 0 by decide)
  rw [map_mul, htwo, zero_mul] at h
  exact h

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicPermutation_targetDifference_sum
#print axioms Erdos85.sizeTwoCyclicPermutation_reflectionPair_targetDifference_sum
#print axioms Erdos85.sizeTwoCyclicPermutation_targetDifference_parity_sum

import Proofs.Erdos85SizeTwoEigenlineCyclicUniformOrbitObstruction

/-!
# No orthomorphism inside a binary cyclic routing fiber

Node: `BinarySizeTwoCyclicPackingBound`, beneath `SIZE-TWO-EIGENLINE(q)`.

For a fixed source `(x,t)`, the routing column is a permutation of a
two-punctured cyclic group and the target-difference labels avoid the two
reflection holes.  If those difference labels were also injective, the fiber
would be a two-punctured analogue of an orthomorphism.  When `4 ∣ q`, the
two requirements have incompatible mod-two sums.  Thus every fiber has a
repeated target difference.

This records the exact hypothesis missing from classical orthomorphism and
Costas-array nonexistence theorems: their within-permutation difference
injectivity is false here, not merely unavailable.
-/

namespace Erdos85

noncomputable section

/-- Injectivity of the target-difference map would identify the punctured
row set with the allowed difference set, forcing its sum to be the affine
displacement sum of the routing permutation. -/
theorem targetDifference_fiberSum_of_injective
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (ha : a ≠ -1 - a)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (hinj : Function.Injective (code.targetDifference x t)) :
    (∑ u : sizeTwoAllowedDifference q a, u.1) = 2 * (t.1 + 1) := by
  have hq1 : (1 : ZMod q) ≠ 0 := by
    letI : Fact (1 < q) := ⟨hq⟩
    exact one_ne_zero
  have hcard : Fintype.card (SizeTwoAdmissibleTargetRow q t.1) =
      Fintype.card (sizeTwoAllowedDifference q a) := by
    rw [sizeTwoAdmissibleTargetRow_card q t.1 hq1,
      sizeTwoAllowedDifference_card q a ha]
  let targetEquiv :
      SizeTwoAdmissibleTargetRow q t.1 ≃ sizeTwoAllowedDifference q a :=
    Equiv.ofBijective (code.targetDifference x t)
      ((Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, hcard⟩)
  calc
    (∑ u : sizeTwoAllowedDifference q a, u.1) =
        ∑ r : SizeTwoAdmissibleTargetRow q t.1,
          (code.targetDifference x t r).1 := by
      exact (Equiv.sum_comp targetEquiv Subtype.val).symm
    _ = ∑ r : SizeTwoAdmissibleTargetRow q t.1,
        ((code.toPermutationCode.perm x t r).1 - r.1) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact eq_sub_of_add_eq (by
        simpa [add_comm] using code.target_column_eq x t r)
    _ = 2 * (t.1 + 1) :=
      sizeTwoCyclicPermutation_targetDifference_sum hq
        code.toPermutationCode.perm x t

/-- At every binary-relevant modulus, every routing fiber repeats a target
difference.  Hence it is not a partial orthomorphism or a Costas map. -/
theorem SizeTwoCyclicReciprocalPermutationCode.not_injective_targetDifference_of_four_dvd
    {q : ℕ} [NeZero q] (h4q : 4 ∣ q) {a : ZMod q}
    (ha : a ≠ -1 - a)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    ¬ Function.Injective (code.targetDifference x t) := by
  intro hinj
  have hq : 2 ≤ q := by
    obtain ⟨k, hk⟩ := h4q
    have hk0 : k ≠ 0 := by
      intro hkzero
      subst k
      simp at hk
      exact NeZero.ne q hk
    omega
  have h2q : 2 ∣ q := dvd_trans (by norm_num : 2 ∣ 4) h4q
  let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
  have hsum := targetDifference_fiberSum_of_injective
    hq ha code x t hinj
  rw [sizeTwoAllowedDifference_sum q a ha] at hsum
  have heven : Even (q * (q - 1) / 2) := by
    obtain ⟨k, rfl⟩ := h4q
    refine ⟨k * (4 * k - 1), ?_⟩
    calc
      4 * k * (4 * k - 1) / 2 =
          (2 * (2 * k * (4 * k - 1))) / 2 := by congr 1 <;> ring
      _ = 2 * k * (4 * k - 1) :=
        Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)
      _ = k * (4 * k - 1) + k * (4 * k - 1) := by ring
  have hmapN : φ (((q * (q - 1) / 2 : ℕ) : ZMod q)) = 0 := by
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    rw [Nat.cast_add, map_add]
    rw [← two_mul]
    have htwoZ : (2 : ZMod 2) = 0 := by decide
    rw [htwoZ, zero_mul]
  have hmapped := congrArg φ hsum
  rw [map_add, hmapN, zero_add, map_one, map_mul] at hmapped
  have htwo : φ (2 : ZMod q) = 0 := by
    simpa only [map_ofNat] using (show (2 : ZMod 2) = 0 by decide)
  rw [htwo, zero_mul] at hmapped
  exact one_ne_zero hmapped

end

end Erdos85

#print axioms Erdos85.targetDifference_fiberSum_of_injective
#print axioms Erdos85.SizeTwoCyclicReciprocalPermutationCode.not_injective_targetDifference_of_four_dvd

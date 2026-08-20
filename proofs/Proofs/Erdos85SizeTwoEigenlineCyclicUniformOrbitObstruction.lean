import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationDisplacementSum
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingSecondMomentCensus
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingReciprocity
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingCounts

/-!
# Reciprocity obstructs uniform orbit multiplicity

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The aggregate packing ledger admits the formal model in which every
difference orbit has multiplicity one at every allowed absolute cell.  That
model does not lift to a reciprocal routing code.  Reciprocity would make
every source matching hit every allowed target-difference fiber exactly
once, while the punctured-permutation displacement sum depends on the source
fiber.  Comparing the allowed source fibers `0` and `-1` gives `2 = 0`.
-/

namespace Erdos85

noncomputable section

private theorem allowedDifference_ne_reflection
    {q : ℕ} [NeZero q] (h2q : 2 ∣ q) (a : ZMod q) :
    a ≠ -1 - a := by
  intro ha
  have h := congrArg (ZMod.castHom h2q (ZMod 2)) ha
  have hone : ZMod.castHom h2q (ZMod 2) (1 : ZMod q) = 1 := map_one _
  have htwo : ZMod.castHom h2q (ZMod 2) (2 : ZMod q) = 0 := by
    simpa only [map_ofNat] using (show (2 : ZMod 2) = 0 by decide)
  rw [map_sub, map_neg, hone] at h
  have : ZMod.castHom h2q (ZMod 2) (2 * a) = 1 := by
    rw [map_mul, htwo, zero_mul]
    have := congrArg (fun z : ZMod 2 => z +
      ZMod.castHom h2q (ZMod 2) a) h
    simpa [sub_eq_add_neg, add_assoc] using this.symm
  rw [map_mul, htwo, zero_mul] at this
  exact zero_ne_one this

private theorem targetDifference_surjective_of_uniform
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicFullPermutationCode q a)
    (huniform : ∀ (t : sizeTwoAllowedDifference q a)
      (e : SizeTwoCyclicAbsoluteGridEdge q),
      sizeTwoCyclicMatchingOrbitMultiplicity code t e = 1)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Function.Surjective
      (code.toReciprocalCode.targetDifference x t) := by
  intro u
  have hcard := huniform u (sizeTwoCyclicMatchingSourceCell (x, t))
  unfold sizeTwoCyclicMatchingOrbitMultiplicity at hcard
  have hpos : 0 < ((Finset.univ : Finset (ZMod q)).filter fun y =>
      sizeTwoCyclicMatchingSourceCell (x, t) ∈
        sizeTwoCyclicSourceMatching code (y, u)).card := by
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
  have hy' := (Finset.mem_filter.mp hy).2
  have hreverse : sizeTwoCyclicMatchingSourceCell (y, u) ∈
      sizeTwoCyclicSourceMatching code (x, t) :=
    (sizeTwoCyclicSourceMatching_sourceCell_mem_comm code (x, t) (y, u)).mpr hy'
  obtain ⟨r, hr⟩ :=
    (sizeTwoCyclicSourceMatching_mem_iff code (x, t)
      (sizeTwoCyclicMatchingSourceCell (y, u))).mp hreverse
  refine ⟨r, ?_⟩
  apply Subtype.ext
  have hfirst := congrArg Prod.fst hr
  have hsecond := congrArg Prod.snd hr
  have hcolumn := code.toReciprocalCode.target_column_eq x t r
  dsimp [sizeTwoCyclicMatchingEdge,
    sizeTwoCyclicMatchingSourceCell] at hfirst hsecond
  change r.1 + (code.toReciprocalCode.targetDifference x t r).1 =
    (code.toReciprocalCode.toPermutationCode.perm x t r).1 at hcolumn
  calc
    (code.toReciprocalCode.targetDifference x t r).1 =
        (x + (code.toReciprocalCode.toPermutationCode.perm x t r).1) -
          (x + r.1) := by rw [← hcolumn]; abel
    _ = (y + u.1) - y := by rw [hfirst, hsecond]
    _ = u.1 := by abel

private theorem targetDifference_bijective_of_uniform
    {q : ℕ} [NeZero q] {a : ZMod q}
    (ha : a ≠ -1 - a) (hq1 : (1 : ZMod q) ≠ 0)
    (code : SizeTwoCyclicFullPermutationCode q a)
    (huniform : ∀ (t : sizeTwoAllowedDifference q a)
      (e : SizeTwoCyclicAbsoluteGridEdge q),
      sizeTwoCyclicMatchingOrbitMultiplicity code t e = 1)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Function.Bijective
      (code.toReciprocalCode.targetDifference x t) := by
  apply (Fintype.bijective_iff_surjective_and_card _).2
  refine ⟨targetDifference_surjective_of_uniform code huniform x t, ?_⟩
  rw [sizeTwoAdmissibleTargetRow_card q t.1 hq1,
    sizeTwoAllowedDifference_card q a ha]

/-- A reciprocal full code cannot realize the aggregate uniform model in
which every difference-orbit multiplicity is one at every absolute cell. -/
theorem not_binary_sizeTwoCyclic_uniformOrbitMultiplicity
    {q : ℕ} [NeZero q] (hq : 4 ≤ q) (h2q : 2 ∣ q)
    {a : ZMod q} (ha0 : a ≠ 0) (ha1 : a ≠ -1)
    (code : SizeTwoCyclicFullPermutationCode q a) :
    ¬(∀ (t : sizeTwoAllowedDifference q a)
      (e : SizeTwoCyclicAbsoluteGridEdge q),
      sizeTwoCyclicMatchingOrbitMultiplicity code t e = 1) := by
  intro huniform
  have hq1 : (1 : ZMod q) ≠ 0 := by
    letI : Fact (1 < q) := ⟨by omega⟩
    exact one_ne_zero
  have hq2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hv' : 2 % q = 0 := by
      simpa [ZMod.val_ofNat] using hv
    rw [Nat.mod_eq_of_lt (by omega)] at hv'
    omega
  have harefl : a ≠ -1 - a := allowedDifference_ne_reflection h2q a
  let zeroFiber : sizeTwoAllowedDifference q a :=
    ⟨0, ha0.symm, by
      intro h
      apply ha1
      have := congrArg (fun z : ZMod q => -1 - z) h
      simpa [sub_eq_add_neg, add_assoc] using this.symm⟩
  let negOneFiber : sizeTwoAllowedDifference q a :=
    ⟨-1, ha1.symm, by
      intro h
      apply ha0
      have := congrArg (fun z : ZMod q => z + 1) h
      simpa [sub_eq_add_neg, add_assoc] using this.symm⟩
  let targetEquiv (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
      SizeTwoAdmissibleTargetRow q t.1 ≃ sizeTwoAllowedDifference q a :=
    Equiv.ofBijective (code.toReciprocalCode.targetDifference x t)
      (targetDifference_bijective_of_uniform
        harefl hq1 code huniform x t)
  have fiberSum (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
      (∑ u : sizeTwoAllowedDifference q a, u.1) = 2 * (t.1 + 1) := by
    calc
      (∑ u : sizeTwoAllowedDifference q a, u.1) =
          ∑ r : SizeTwoAdmissibleTargetRow q t.1,
            (code.toReciprocalCode.targetDifference x t r).1 := by
        exact (Equiv.sum_comp (targetEquiv x t) Subtype.val).symm
      _ = ∑ r : SizeTwoAdmissibleTargetRow q t.1,
          ((code.toReciprocalCode.toPermutationCode.perm x t r).1 - r.1) := by
        apply Finset.sum_congr rfl
        intro r hr
        have hcolumn := code.toReciprocalCode.target_column_eq x t r
        exact eq_sub_of_add_eq (by simpa [add_comm] using hcolumn)
      _ = 2 * (t.1 + 1) :=
        sizeTwoCyclicPermutation_targetDifference_sum (by omega)
          code.toReciprocalCode.toPermutationCode.perm x t
  have hz := fiberSum 0 zeroFiber
  have hn := fiberSum 0 negOneFiber
  apply hq2
  calc
    (2 : ZMod q) = 2 * (zeroFiber.1 + 1) := by simp [zeroFiber]
    _ = ∑ u : sizeTwoAllowedDifference q a, u.1 := hz.symm
    _ = 2 * (negOneFiber.1 + 1) := hn
    _ = 0 := by simp [negOneFiber]

end

end Erdos85

#print axioms Erdos85.not_binary_sizeTwoCyclic_uniformOrbitMultiplicity

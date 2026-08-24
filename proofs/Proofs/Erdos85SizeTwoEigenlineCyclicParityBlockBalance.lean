import Proofs.Erdos85SizeTwoAllowedDifferenceParityCard
import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementMultiplicityMoment
import Proofs.Erdos85SizeTwoEigenlineCyclicTargetFiberReciprocity

/-!
# Balanced parity blocks of the cyclic route matrix

Reciprocity makes the aggregate source/target-difference route matrix
symmetric.  Its row sum is constant, since every source cell has exactly
`q-2` routes.  Consequently any equipartition of the allowed differences has
equal total route mass in its two diagonal blocks.  In particular this holds
for the two mod-two classes at binary parameters.
-/

namespace Erdos85

noncomputable section

/-- A symmetric nonnegative matrix with constant row sum has equally massive
diagonal blocks across any equipartition of its index set. -/
theorem symmetric_constantRowSum_equipartition_diagonalBlock_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (W : α → α → ℕ) (R : ℕ)
    (hsymm : ∀ i j, W i j = W j i)
    (hrow : ∀ i, ∑ j : α, W i j = R)
    (S T : Finset α) (hdisj : Disjoint S T)
    (hcover : S ∪ T = Finset.univ) (hcard : S.card = T.card) :
    (∑ i ∈ S, ∑ j ∈ S, W i j) =
      ∑ i ∈ T, ∑ j ∈ T, W i j := by
  have hsplit (i : α) :
      (∑ j : α, W i j) =
        (∑ j ∈ S, W i j) + ∑ j ∈ T, W i j := by
    rw [← Finset.sum_union hdisj, hcover]
  have hcross :
      (∑ i ∈ S, ∑ j ∈ T, W i j) =
        ∑ i ∈ T, ∑ j ∈ S, W i j := by
    calc
      (∑ i ∈ S, ∑ j ∈ T, W i j) =
          ∑ i ∈ S, ∑ j ∈ T, W j i := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hsymm i j
      _ = ∑ i ∈ T, ∑ j ∈ S, W i j := by
        rw [Finset.sum_comm]
  have hS :
      (∑ i ∈ S, ∑ j ∈ S, W i j) +
          (∑ i ∈ S, ∑ j ∈ T, W i j) = S.card * R := by
    calc
      _ = ∑ i ∈ S, ((∑ j ∈ S, W i j) + ∑ j ∈ T, W i j) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ _i ∈ S, R := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hsplit i, hrow i]
      _ = S.card * R := by simp
  have hT :
      (∑ i ∈ T, ∑ j ∈ T, W i j) +
          (∑ i ∈ T, ∑ j ∈ S, W i j) = T.card * R := by
    calc
      _ = ∑ i ∈ T, ((∑ j ∈ T, W i j) + ∑ j ∈ S, W i j) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ _i ∈ T, R := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_comm, ← hsplit i, hrow i]
      _ = T.card * R := by simp
  rw [hcard, hcross] at hS
  exact Nat.add_right_cancel (hS.trans hT.symm)

/-- The aggregate route-multiplicity matrix has constant row sum
`q * (q-2)`. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_totalRowSum
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    (∑ u : sizeTwoAllowedDifference q a,
      ∑ x : ZMod q,
        sizeTwoCyclicTargetDifferenceMultiplicity code x t u) =
      q * (q - 2) := by
  rw [Finset.sum_comm]
  calc
    (∑ x : ZMod q, ∑ u : sizeTwoAllowedDifference q a,
        sizeTwoCyclicTargetDifferenceMultiplicity code x t u) =
      ∑ _x : ZMod q, Fintype.card (SizeTwoAdmissibleTargetRow q t.1) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact sizeTwoCyclicTargetDifferenceMultiplicity_sum code x t
    _ = q * (q - 2) := by
      have hq1 : (1 : ZMod q) ≠ 0 := by
        letI : Fact (1 < q) := ⟨by omega⟩
        exact one_ne_zero
      rw [sizeTwoAdmissibleTargetRow_card q t.1 hq1]
      simp

/-- At binary parameters, the total route mass staying inside the even
allowed-difference class equals the mass staying inside the odd class. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_binaryParityBlocks_eq
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) (h2q : 2 ∣ q) {a : ZMod q}
    (hholes :
      ZMod.castHom h2q (ZMod 2) a ≠
        ZMod.castHom h2q (ZMod 2) (-1 - a))
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
    let E := (Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
      fun t => φ t.1 = 0
    let O := (Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
      fun t => φ t.1 ≠ 0
    (∑ t ∈ E, ∑ u ∈ E, ∑ x : ZMod q,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u) =
    ∑ t ∈ O, ∑ u ∈ O, ∑ x : ZMod q,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u := by
  classical
  dsimp only
  let φ : ZMod q →+* ZMod 2 := ZMod.castHom h2q (ZMod 2)
  let E := (Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
    fun t => φ t.1 = 0
  let O := (Finset.univ : Finset (sizeTwoAllowedDifference q a)).filter
    fun t => φ t.1 ≠ 0
  apply symmetric_constantRowSum_equipartition_diagonalBlock_eq
    (fun t u => ∑ x : ZMod q,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u)
    (q * (q - 2))
  · exact sizeTwoCyclicTargetDifferenceMultiplicity_sum_symm code
  · exact sizeTwoCyclicTargetDifferenceMultiplicity_totalRowSum hq code
  · apply Finset.disjoint_left.mpr
    intro t htE htO
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at htE
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at htO
    exact htO htE
  · ext t
    simp only [E, O, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      trivial
    · intro _
      exact Classical.em _
  · simpa [E, O, φ] using
      (sizeTwoAllowedDifference_binaryParity_cards h2q a hholes).1.trans
        (sizeTwoAllowedDifference_binaryParity_cards h2q a hholes).2.symm

end

end Erdos85

#print axioms Erdos85.symmetric_constantRowSum_equipartition_diagonalBlock_eq
#print axioms Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_totalRowSum
#print axioms
  Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_binaryParityBlocks_eq

import Proofs.Erdos85ProjectedMultiplicityParity
import Proofs.Erdos85DifferenceArray
import Mathlib.Data.Finset.Sigma

/-!
# Equality in the diagonal difference-array bound

When the diagonal incidence count equals the size of the allowed set, the
covering obtained from the odd-involution argument is exact: every allowed
difference belongs to one and only one diagonal block.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

variable {I Z : Type*} [Fintype I] [DecidableEq I]
  [Fintype Z] [DecidableEq Z]

/-- A finite family covering `R` with exactly `|R|` total incidences is an
exact one-fold cover. -/
theorem existsUnique_mem_of_subset_biUnion_of_sum_card_eq
    (R : Finset Z) (D : I → Finset Z)
    (hcover : R ⊆ Finset.univ.biUnion D)
    (hcard : ∑ i, (D i).card = R.card) :
    ∀ t ∈ R, ∃! i, t ∈ D i := by
  let incidences : Finset (Σ _i : I, Z) := Finset.univ.sigma D
  let value : (Σ _i : I, Z) → Z := fun z ↦ z.2
  have himage : incidences.image value = Finset.univ.biUnion D := by
    ext t
    simp [incidences, value]
  have hincCard : incidences.card = ∑ i, (D i).card := by
    simp [incidences]
  have hcardImage : (incidences.image value).card = incidences.card := by
    have hlo : R.card ≤ (incidences.image value).card := by
      rw [himage]
      exact Finset.card_le_card hcover
    have hhi : (incidences.image value).card ≤ incidences.card :=
      Finset.card_image_le
    omega
  have hinj : Set.InjOn value incidences :=
    Finset.card_image_iff.mp hcardImage
  intro t ht
  have htUnion := hcover ht
  rw [← himage] at htUnion
  obtain ⟨z, hzInc, hzVal⟩ := Finset.mem_image.mp htUnion
  refine ⟨z.1, ?_, ?_⟩
  · have hz := Finset.mem_sigma.mp hzInc
    simpa [value, hzVal] using hz.2
  · intro j hj
    let w : Σ _i : I, Z := ⟨j, t⟩
    have hwInc : w ∈ incidences := by
      simp [w, incidences, hj]
    have hwVal : value w = t := by rfl
    have hzw : z = w := hinj hzInc hwInc (by simpa [hwVal] using hzVal)
    exact (congrArg Sigma.fst hzw).symm

/-- Equality case of the symmetric odd difference-array theorem. -/
theorem existsUnique_mem_diagonal_of_symmetric_unique_rows_of_odd
    (R : Finset Z) (D : I → I → Finset Z)
    (hsymm : ∀ i j, D i j = D j i)
    (hrows : ∀ t ∈ R, ∀ i, ∃! j, t ∈ D i j)
    (hodd : Odd (Fintype.card I))
    (hcard : ∑ i, (D i i).card = R.card) :
    ∀ t ∈ R, ∃! i, t ∈ D i i := by
  have hcover := subset_diagonal_biUnion_of_symmetric_unique_rows
    R D hsymm hrows (everyInvolutionHasFixedPoint_of_odd hodd)
  exact existsUnique_mem_of_subset_biUnion_of_sum_card_eq
    R (fun i ↦ D i i) hcover hcard

/-- Exact diagonal coverage in the boundary case `sum |Dᵢᵢ| = r-3`. -/
theorem existsUnique_mem_diagonal_orderedDifferenceSet_of_boundary
    {r : ℕ} [NeZero r] (hr3 : 3 ≤ r)
    (A : I → I → Finset (ZMod r))
    (hsymm : ∀ i j,
      orderedDifferenceSet (A i j) = orderedDifferenceSet (A j i))
    (hleave : ∀ i, unusedOrderedDifferences (A i) = {1, -1})
    (hdisj : ∀ i, ∀ {j k : I}, j ≠ k →
      Disjoint (orderedDifferenceSet (A i j))
        (orderedDifferenceSet (A i k)))
    (hodd : Odd (Fintype.card I))
    (hcard : ∑ i, (orderedDifferenceSet (A i i)).card = r - 3) :
    ∀ t ∈ allowedCycleDifferences r,
      ∃! i, t ∈ orderedDifferenceSet (A i i) := by
  let D : I → I → Finset (ZMod r) :=
    fun i j ↦ orderedDifferenceSet (A i j)
  have hrows : ∀ t ∈ allowedCycleDifferences r, ∀ i,
      ∃! j, t ∈ D i j := by
    intro t ht i
    have htNot := (Finset.mem_sdiff.mp ht).2
    have ht0 : t ≠ 0 := by
      intro h
      exact htNot (by simp [h])
    have ht1 : t ≠ 1 := by
      intro h
      exact htNot (by simp [h])
    have htm1 : t ≠ -1 := by
      intro h
      exact htNot (by simp [h])
    exact existsUnique_mem_orderedDifferenceSet_of_leave
      hr3 (A i) (hleave i) (hdisj i) ht0 ht1 htm1
  have hcardR : (allowedCycleDifferences r).card = r - 3 :=
    card_allowedCycleDifferences hr3
  apply existsUnique_mem_diagonal_of_symmetric_unique_rows_of_odd
    (allowedCycleDifferences r) D
  · exact hsymm
  · exact hrows
  · exact hodd
  · simpa [D, hcardR] using hcard

end

end Erdos85

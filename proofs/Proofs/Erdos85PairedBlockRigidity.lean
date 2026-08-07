import Proofs.Erdos85OrderFortyNineOuterDefect

/-!
# Equality closure for paired branch defect bounds

The order-49 outer-graph argument produces six far-block inequalities and one
paired-block inequality.  Their upper bounds add to the already-known exact
cross-defect degree.  Consequently every inequality is an equality.  This file
isolates that arithmetic closure, so the graph-facing path count need only
provide the local inequalities and row-sum identities.
-/

namespace Erdos85

noncomputable section

/-- Six local bounds of the form `dᵢ + aᵢ + bᵢ ≤ 5`, together with the paired
bound and the exact total `25`, are all sharp.  In the graph application, `dᵢ`
is a far defect-block cardinality and `aᵢ,bᵢ` are the two crossed miss counts. -/
theorem six_far_bounds_rigid_of_cross_total
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (d a b : ι → ℕ) (paired M N : ℕ)
    (hIcard : I.card = 6)
    (ha : ∑ i ∈ I, a i = M)
    (hb : ∑ i ∈ I, b i = N)
    (hfar : ∀ i ∈ I, d i + a i + b i ≤ 5)
    (hpaired : paired + 5 ≤ M + N)
    (htotal : paired + ∑ i ∈ I, d i = 25) :
    paired + 5 = M + N ∧ ∀ i ∈ I, d i + a i + b i = 5 := by
  have hsumLe :
      (∑ i ∈ I, (d i + a i + b i)) ≤ ∑ _i ∈ I, 5 :=
    Finset.sum_le_sum fun i hi => hfar i hi
  have hconst : (∑ _i ∈ I, 5) = 30 := by
    simp [hIcard]
  have hsplit :
      (∑ i ∈ I, (d i + a i + b i)) =
        (∑ i ∈ I, d i) + (∑ i ∈ I, a i) + (∑ i ∈ I, b i) := by
    simp only [Finset.sum_add_distrib]
  have hreverse : M + N ≤ paired + 5 := by
    rw [hsplit, ha, hb, hconst] at hsumLe
    omega
  have hpairedEq : paired + 5 = M + N := by omega
  have hsumEq :
      (∑ i ∈ I, (d i + a i + b i)) = ∑ _i ∈ I, 5 := by
    rw [hsplit, ha, hb, hconst]
    omega
  refine ⟨hpairedEq, ?_⟩
  exact (Finset.sum_eq_sum_iff_of_le hfar).mp hsumEq

/-- Path-count form of `six_far_bounds_rigid_of_cross_total`.  Every pair of
five-point branches splits into `common` and `defect` endpoint pairs.  Four
intermediate branches and the two endpoint branches give the far lower bound
`20 + aᵢ + bᵢ`; the six intermediate branches give the paired lower bound.
If the cross-defect total is 25, all these path lower bounds are exact. -/
theorem six_branch_path_counts_rigid
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι)
    (defect common a b : ι → ℕ) (pairedDefect pairedCommon M N : ℕ)
    (hIcard : I.card = 6)
    (ha : ∑ i ∈ I, a i = M)
    (hb : ∑ i ∈ I, b i = N)
    (hfarPartition : ∀ i ∈ I, defect i + common i = 25)
    (hfarPaths : ∀ i ∈ I, 20 + a i + b i ≤ common i)
    (hpairedPartition : pairedDefect + pairedCommon = 25)
    (hpairedPaths : 30 ≤ pairedCommon + M + N)
    (htotal : pairedDefect + ∑ i ∈ I, defect i = 25) :
    pairedDefect + 5 = M + N ∧
      pairedCommon + M + N = 30 ∧
      ∀ i ∈ I,
        defect i + a i + b i = 5 ∧ common i = 20 + a i + b i := by
  have hfar : ∀ i ∈ I, defect i + a i + b i ≤ 5 := by
    intro i hi
    have hp := hfarPartition i hi
    have hl := hfarPaths i hi
    omega
  have hpaired : pairedDefect + 5 ≤ M + N := by omega
  obtain ⟨hpairedEq, hfarEq⟩ := six_far_bounds_rigid_of_cross_total
    I defect a b pairedDefect M N hIcard ha hb hfar hpaired htotal
  refine ⟨hpairedEq, ?_, ?_⟩
  · omega
  · intro i hi
    refine ⟨hfarEq i hi, ?_⟩
    have hp := hfarPartition i hi
    have he := hfarEq i hi
    omega

end

end Erdos85

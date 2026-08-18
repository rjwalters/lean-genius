import Proofs.Erdos85BinarySquareSignedEigenvectorSupport

/-!
# Minimum degree inside the extreme support of a three-level eigenvector

If `w` takes values in `{-2,0,2}` and satisfies `Aw = 2w` wherever it is
nonzero, then each extreme level set induces minimum degree at least two.
This is the local engine shared by all signed size-two joint-eigenvalue cases.
-/

open SimpleGraph

namespace Erdos85

/-- Both extreme fibres of a three-level adjacency eigenvector have induced
minimum degree at least two. -/
theorem threeLevel_eigenvalue_two_extreme_support_minDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℤ)
    (hlevels : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (heig : ∀ x, w x ≠ 0 →
      ∑ y ∈ G.neighborFinset x, w y = 2 * w x) :
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card) := by
  dsimp only
  let Sp := Finset.univ.filter fun x => w x = 2
  let Sm := Finset.univ.filter fun x => w x = -2
  have hSp : ∀ x, x ∈ Sp ↔ w x = 2 := by
    intro x
    simp [Sp]
  have hSm : ∀ x, x ∈ Sm ↔ w x = -2 := by
    intro x
    simp [Sm]
  constructor
  · intro u hu
    have hwu : w u = 2 := (hSp u).mp hu
    have hsum := heig u (by omega)
    rw [hwu] at hsum
    have hle : ∑ y ∈ G.neighborFinset u, w y ≤
        ∑ y ∈ G.neighborFinset u, (if y ∈ Sp then (2 : ℤ) else 0) := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ Sp
      · rw [if_pos hy, (hSp y).mp hy]
      · rw [if_neg hy]
        have hne : w y ≠ 2 := fun h => hy ((hSp y).mpr h)
        rcases hlevels y with h | h | h <;> rw [h] <;> norm_num
        exact absurd h hne
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hsum] at hle
    change 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card
    omega

  · intro u hu
    have hwu : w u = -2 := (hSm u).mp hu
    have hsum := heig u (by omega)
    rw [hwu] at hsum
    have hle : ∑ y ∈ G.neighborFinset u, (if y ∈ Sm then (-2 : ℤ) else 0) ≤
        ∑ y ∈ G.neighborFinset u, w y := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ Sm
      · rw [if_pos hy, (hSm y).mp hy]
      · rw [if_neg hy]
        have hne : w y ≠ -2 := fun h => hy ((hSm y).mpr h)
        rcases hlevels y with h | h | h <;> rw [h] <;> norm_num
        exact absurd h hne
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hsum] at hle
    change 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card
    omega

/-- Graph-facing form for a signed size-two joint eigenvector at order 64.
The conclusion is independent of the defect eigenvalue `mu`. -/
theorem orderSixtyFour_sizeTwo_jointEigenvector_extremeSupport_minDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = mu * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2) :
    let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    (∀ u ∈ Sp, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sp).card) ∧
    (∀ u ∈ Sm, 2 ≤ ((G.neighborFinset u).filter fun y => y ∈ Sm).card) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let a : V → ℤ := A.mulVec s
  let w : V → ℤ := fun x => a x + 2 * s x
  have hA2 : ∀ x, A.mulVec a x = (7 - mu) * s x := by
    intro x
    change A.mulVec (A.mulVec s) x = _
    rw [Matrix.mulVec_mulVec s A A]
    change (((G.adjMatrix ℤ) * (G.adjMatrix ℤ)).mulVec s) x = _
    rw [binarySquare_regular_adjMatrix_sq_mulVec_apply G hfree hreg s x,
      hsum, hDs x]
    ring
  have hw_in : ∀ x, x ∈ c.supp → w x = 0 := by
    intro x hx
    simp only [w, a]
    rw [hA_in x hx]
    ring
  have hw_out : ∀ x, x ∉ c.supp → w x = a x := by
    intro x hx
    simp only [w]
    rw [hs_out x hx]
    ring
  have hlevels : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2 := by
    intro x
    by_cases hx : x ∈ c.supp
    · exact Or.inr (Or.inl (hw_in x hx))
    · rw [hw_out x hx]
      exact hA_out x hx
  have hAw : ∀ x, ∑ y ∈ G.neighborFinset x, w y =
      (3 - mu) * s x + 2 * w x := by
    intro x
    simp only [w]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have ha : A.mulVec a x = ∑ y ∈ G.neighborFinset x, a y := by
      simp only [A]
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have hs : A.mulVec s x = ∑ y ∈ G.neighborFinset x, s y := by
      simp only [A]
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [← ha, ← hs, hA2 x]
    simp only [a]
    ring
  have heig : ∀ x, w x ≠ 0 →
      ∑ y ∈ G.neighborFinset x, w y = 2 * w x := by
    intro x hx
    have hxout : x ∉ c.supp := fun hxin => hx (hw_in x hxin)
    rw [hAw x, hs_out x hxout]
    ring
  simpa only [w, a, A] using
    (threeLevel_eigenvalue_two_extreme_support_minDegree G w hlevels heig)

end Erdos85

#print axioms Erdos85.threeLevel_eigenvalue_two_extreme_support_minDegree
#print axioms Erdos85.orderSixtyFour_sizeTwo_jointEigenvector_extremeSupport_minDegree

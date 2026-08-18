import Proofs.Erdos85ThreeLevelEigenSupportMinDegree
import Proofs.Erdos85BinarySquareSizeTwoSignedJointPackage

/-!
# Exact degree balance between extreme fibres

For a `{-2,0,2}`-valued vector satisfying `Aw = 2w` on its support, the
minimum-degree conclusion sharpens to an exact local identity: a positive
vertex has two more positive than negative neighbours, and conversely.
-/

open SimpleGraph

namespace Erdos85

/-- Sum a three-level function by counting its two extreme fibres. -/
theorem threeLevel_sum_eq_two_mul_pos_sub_neg
    {α : Type*} [DecidableEq α]
    (S : Finset α) (w : α → ℤ)
    (hlevels : ∀ x ∈ S, w x = -2 ∨ w x = 0 ∨ w x = 2) :
    ∑ x ∈ S, w x =
      2 * ((S.filter fun x => w x = 2).card : ℤ) -
      2 * ((S.filter fun x => w x = -2).card : ℤ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hwa := hlevels a (by simp)
      have hwS : ∀ x ∈ S, w x = -2 ∨ w x = 0 ∨ w x = 2 := by
        intro x hx
        exact hlevels x (by simp [hx])
      rw [Finset.sum_insert ha, ih hwS]
      rcases hwa with hwa | hwa | hwa <;>
        simp [Finset.filter_insert, ha, hwa] <;> ring

/-- Exact same-sign/opposite-sign degree balance on both extreme fibres. -/
theorem threeLevel_eigenvalue_two_extreme_degreeBalance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℤ)
    (hlevels : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (heig : ∀ x, w x ≠ 0 →
      ∑ y ∈ G.neighborFinset x, w y = 2 * w x) :
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2) := by
  dsimp only
  let Sp := Finset.univ.filter fun x => w x = 2
  let Sm := Finset.univ.filter fun x => w x = -2
  have hSp : ∀ x, x ∈ Sp ↔ w x = 2 := by
    intro x
    simp [Sp]
  have hSm : ∀ x, x ∈ Sm ↔ w x = -2 := by
    intro x
    simp [Sm]
  have key : ∀ u,
      ∑ y ∈ G.neighborFinset u, w y =
        2 * (((G.neighborFinset u).filter fun y => y ∈ Sp).card : ℤ) -
        2 * (((G.neighborFinset u).filter fun y => y ∈ Sm).card : ℤ) := by
    intro u
    have h := threeLevel_sum_eq_two_mul_pos_sub_neg
      (G.neighborFinset u) w (fun x _ => hlevels x)
    have hp : (G.neighborFinset u).filter (fun y => w y = 2) =
        (G.neighborFinset u).filter (fun y => y ∈ Sp) := by
      ext y
      simp [Sp]
    have hm : (G.neighborFinset u).filter (fun y => w y = -2) =
        (G.neighborFinset u).filter (fun y => y ∈ Sm) := by
      ext y
      simp [Sm]
    rw [hp, hm] at h
    exact h
  constructor
  · intro u hu
    have hsum := heig u (by rw [(hSp u).mp hu]; norm_num)
    rw [key u, (hSp u).mp hu] at hsum
    change ((G.neighborFinset u).filter fun y => y ∈ Sp).card =
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2
    omega
  · intro u hu
    have hsum := heig u (by rw [(hSm u).mp hu]; norm_num)
    rw [key u, (hSm u).mp hu] at hsum
    change ((G.neighborFinset u).filter fun y => y ∈ Sm).card =
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2
    omega

/-- Campaign-facing exact degree balance from the standard local size-two
joint-line interface. -/
theorem orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x => w x = 2
    let Sm := Finset.univ.filter fun x => w x = -2
    (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y => y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y => y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y => y ∈ Sp).card + 2) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let a : V → ℤ := A.mulVec s
  let w : V → ℤ := fun x => a x + 2 * s x
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  have hA2 : ∀ x, A.mulVec a x = (7 - mu) * s x := by
    intro x
    change A.mulVec (A.mulVec s) x = _
    rw [Matrix.mulVec_mulVec s A A]
    change (((G.adjMatrix ℤ) * (G.adjMatrix ℤ)).mulVec s) x = _
    rw [binarySquare_regular_adjMatrix_sq_mulVec_apply G hfree hreg s x,
      P.sum_eq_zero, P.defectAction x]
    ring
  have hw_in : ∀ x, x ∈ c.supp → w x = 0 := by
    intro x hx
    simp only [w, a]
    rw [P.ambientAction_in x hx]
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
      exact P.ambientAction_out x hx
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
    (threeLevel_eigenvalue_two_extreme_degreeBalance G w hlevels heig)

end Erdos85

#print axioms Erdos85.threeLevel_sum_eq_two_mul_pos_sub_neg
#print axioms Erdos85.threeLevel_eigenvalue_two_extreme_degreeBalance
#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local

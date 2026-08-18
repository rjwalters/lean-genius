import Proofs.Erdos85NegativeSizeTwoThreeLevelAction

/-! # Per-row extreme-cell balance for negative joint lines -/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- On every component row, the number of same-sign extreme exterior cells
exceeds the opposite-sign count by `2`, `3`, or `4` for
`μ = -1`, `-3`, or `-5`, respectively. -/
theorem orderSixtyFour_sizeTwo_negative_extreme_rowBalance_of_local
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
    (hmu : mu = -1 ∨ mu = -3 ∨ mu = -5)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let p := fun x ↦ (((G.neighborFinset x).filter
      (fun y ↦ y ∉ c.supp)).filter fun y ↦ w y = 2).card
    let n := fun x ↦ (((G.neighborFinset x).filter
      (fun y ↦ y ∉ c.supp)).filter fun y ↦ w y = -2).card
    ∀ x, x ∈ c.supp →
      (s x = 1 ∧
        ((mu = -1 ∧ p x = n x + 2) ∨
         (mu = -3 ∧ p x = n x + 3) ∨
         (mu = -5 ∧ p x = n x + 4))) ∨
      (s x = -1 ∧
        ((mu = -1 ∧ n x = p x + 2) ∨
         (mu = -3 ∧ n x = p x + 3) ∨
         (mu = -5 ∧ n x = p x + 4))) := by
  dsimp only
  let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let T := fun x ↦ (G.neighborFinset x).filter fun y ↦ y ∉ c.supp
  let p := fun x ↦ ((T x).filter fun y ↦ w y = 2).card
  let n := fun x ↦ ((T x).filter fun y ↦ w y = -2).card
  have P := orderSixtyFour_sizeTwo_signedJoint_threeLevelAction_of_local
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  intro x hx
  change
    (s x = 1 ∧
      ((mu = -1 ∧ p x = n x + 2) ∨
       (mu = -3 ∧ p x = n x + 3) ∨
       (mu = -5 ∧ p x = n x + 4))) ∨
    (s x = -1 ∧
      ((mu = -1 ∧ n x = p x + 2) ∨
       (mu = -3 ∧ n x = p x + 3) ∨
       (mu = -5 ∧ n x = p x + 4)))
  have hcount := threeLevel_sum_eq_two_mul_pos_sub_neg
    (T x) w (fun y _hy ↦ P.2.1 y)
  change ∑ y ∈ T x, w y =
    2 * (p x : ℤ) - 2 * (n x : ℤ) at hcount
  have hsum := P.2.2.1 x hx
  change ∑ y ∈ T x, w y = (3 - mu) * s x at hsum
  rw [hsum] at hcount
  rcases hs_in x hx with hs | hs <;>
    rcases hmu with hmu | hmu | hmu <;>
      subst mu <;> rw [hs] at hcount ⊢ <;> norm_num at hcount ⊢ <;> omega

#print axioms Erdos85.orderSixtyFour_sizeTwo_negative_extreme_rowBalance_of_local

end

end Erdos85

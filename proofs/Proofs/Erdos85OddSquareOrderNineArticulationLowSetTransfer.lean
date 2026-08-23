import Proofs.Erdos85OddSquareOrderNineArticulationCapstone
import Proofs.Erdos85SecondOrderDefectSetTransfer

/-!
# Low-set transfer for the order-nine articulation equality branches

An explicit two-level partition on the 78 ordinary centers, together with
the matching upper level at all three high centers, gives a global formula
`A 1_R = (a+1) 1 - 1_Z`.  Applying the pointwise nonregular defect transfer
then gives the exact integer form of the audit's equations (20) and (23).
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The ordinary centers attaining the lower level of an explicit
order-nine incidence partition. -/
def orderNineOrdinaryLowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (R : Finset V) (a : ℕ) : Finset V :=
  let O := (Finset.univ : Finset V) \ {h₁, h₂, h₃}
  O.filter fun x ↦ (G.neighborFinset x ∩ R).card = a

theorem orderNineOrdinaryLowSet_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (R : Finset V) (a : ℕ) :
    orderNineOrdinaryLowSet G h₁ h₂ h₃ R a ⊆
      (Finset.univ : Finset V) \ {h₁, h₂, h₃} := by
  exact Finset.filter_subset _ _

/-- The two ordinary levels and matching high-root values combine into the
global incidence identity `A 1_R = (a+1)1 - 1_Z`. -/
theorem orderNineOrdinaryExplicitPartition_global_lowSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h₁ h₂ h₃ : V) (R : Finset V) (a r : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a r)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = a + 1)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = a + 1)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = a + 1) :
    ∀ x : V,
      ((G.neighborFinset x ∩ R).card : ℤ) =
        (a + 1 : ℕ) -
          (if x ∈ orderNineOrdinaryLowSet G h₁ h₂ h₃ R a then 1 else 0) := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O := (Finset.univ : Finset V) \ H
  let f := fun x : ↥(↑O : Set V) ↦ (G.neighborFinset x.1 ∩ R).card
  change (∀ x, f x = a ∨ f x = a + 1) ∧ _ at hpart
  intro x
  by_cases hx₁ : x = h₁
  · subst x
    simp [orderNineOrdinaryLowSet, hhigh₁]
  by_cases hx₂ : x = h₂
  · subst x
    simp [orderNineOrdinaryLowSet, hhigh₂]
  by_cases hx₃ : x = h₃
  · subst x
    simp [orderNineOrdinaryLowSet, hhigh₃]
  have hxO : x ∈ O := by simp [O, H, hx₁, hx₂, hx₃]
  have hlevels := hpart.1 ⟨x, hxO⟩
  change (G.neighborFinset x ∩ R).card = a ∨
    (G.neighborFinset x ∩ R).card = a + 1 at hlevels
  rcases hlevels with hlow | hupp
  · simp [orderNineOrdinaryLowSet, O, H, hxO, hlow]
  · simp [orderNineOrdinaryLowSet, O, H, hxO, hupp]

/-- **Order-nine low-set defect equation.**  This is the pointwise cardinal
form of

`D 1_R = diag(deg-1) 1_R + |R| 1 - (a+1) deg + A 1_Z`.

At `(a,|R|)=(5,50)` and `(3,34)` it is exactly the arithmetic content of
audit equations (20) and (23), before substituting degrees 9 and 10. -/
theorem orderNineOrdinaryExplicitPartition_defect_lowSet_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ : V) (R : Finset V) (a r : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a r)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = a + 1)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = a + 1)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = a + 1) :
    ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ R).card : ℤ) =
        ((G.degree x : ℤ) - 1) * (if x ∈ R then 1 else 0) + (R.card : ℤ) -
          (G.degree x : ℤ) * (a + 1 : ℕ) +
            ((G.neighborFinset x ∩
              orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card : ℤ) := by
  classical
  intro x
  have htransfer :=
    c4Free_secondOrderDefect_neighbor_inter_card_eq G hfree R x
  have hglobal := orderNineOrdinaryExplicitPartition_global_lowSet
    G h₁ h₂ h₃ R a r hpart hhigh₁ hhigh₂ hhigh₃
  rw [htransfer]
  have hsum :
      (∑ y ∈ G.neighborFinset x,
        ((G.neighborFinset y ∩ R).card : ℤ)) =
      (G.degree x : ℤ) * (a + 1 : ℕ) -
        ((G.neighborFinset x ∩
          orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card : ℤ) := by
    simp_rw [hglobal]
    simp [G.card_neighborFinset_eq_degree, Finset.sum_sub_distrib, mul_comm]
  rw [hsum]
  ring

/-- In the order-nine three-high degree profile, the low-set equation takes
the uniform vector form

`D 1_R = 8 1_R + (|R|-9(a+1))1 - (a+1)1_H + A 1_Z`.

Thus `(a,|R|)=(5,50)` gives audit equation (20), while `(3,34)` gives (23). -/
theorem orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (h₁ h₂ h₃ : V) (R : Finset V) (a r : ℕ)
    (hpart : orderNineOrdinaryExplicitPartition G h₁ h₂ h₃ R a r)
    (hhigh₁ : (G.neighborFinset h₁ ∩ R).card = a + 1)
    (hhigh₂ : (G.neighborFinset h₂ ∩ R).card = a + 1)
    (hhigh₃ : (G.neighborFinset h₃ ∩ R).card = a + 1)
    (hRH : Disjoint R {h₁, h₂, h₃})
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ x ∈ ({h₁, h₂, h₃} : Finset V), G.degree x = 10) :
    ∀ x : V,
      (((secondOrderDefectGraph G).neighborFinset x ∩ R).card : ℤ) =
        8 * (if x ∈ R then 1 else 0) + (R.card : ℤ) -
          9 * (a + 1 : ℕ) -
          (a + 1 : ℕ) *
            (if x ∈ ({h₁, h₂, h₃} : Finset V) then 1 else 0) +
          ((G.neighborFinset x ∩
            orderNineOrdinaryLowSet G h₁ h₂ h₃ R a).card : ℤ) := by
  classical
  intro x
  rw [orderNineOrdinaryExplicitPartition_defect_lowSet_eq G hfree
    h₁ h₂ h₃ R a r hpart hhigh₁ hhigh₂ hhigh₃ x]
  by_cases hxH : x ∈ ({h₁, h₂, h₃} : Finset V)
  · have hxR : x ∉ R := by
      intro hxR
      exact (Finset.disjoint_left.mp hRH) hxR hxH
    rw [hdegHigh x hxH]
    simp [hxH, hxR]
    ring
  · rw [hdegOrd x hxH]
    simp [hxH]

end

end Erdos85

#print axioms Erdos85.orderNineOrdinaryExplicitPartition_defect_lowSet_eq_nearRegular

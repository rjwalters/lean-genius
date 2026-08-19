import Proofs.Erdos85SizeTwoShoreSwitchCardinality
import Proofs.Erdos85SecondOrderQuotient

/-! # Generic aligned shore-switch matrix socket -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Matrix form of the generic two-shore cardinality switch. -/
theorem bipartition_signSwitch_adjMatrix_eigen_sub_of_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : SimpleGraph X) [DecidableRel D.Adj]
    (A B : Finset X) (hAB : Disjoint A B)
    (hpartition : A ∪ B = Finset.univ)
    (s : X → ℤ) (diagCard diagSame crossCard crossSame : ℕ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hAAcard : ∀ x ∈ A,
      ((D.neighborFinset x).filter (· ∈ A)).card = diagCard)
    (hAAsame : ∀ x ∈ A,
      (((D.neighborFinset x).filter (· ∈ A)).filter
        (fun y ↦ s y = s x)).card = diagSame)
    (hABcard : ∀ x ∈ A,
      ((D.neighborFinset x).filter (· ∈ B)).card = crossCard)
    (hABsame : ∀ x ∈ A,
      (((D.neighborFinset x).filter (· ∈ B)).filter
        (fun y ↦ s y = s x)).card = crossSame)
    (hBBcard : ∀ x ∈ B,
      ((D.neighborFinset x).filter (· ∈ B)).card = diagCard)
    (hBBsame : ∀ x ∈ B,
      (((D.neighborFinset x).filter (· ∈ B)).filter
        (fun y ↦ s y = s x)).card = diagSame)
    (hBAcard : ∀ x ∈ B,
      ((D.neighborFinset x).filter (· ∈ A)).card = crossCard)
    (hBAsame : ∀ x ∈ B,
      (((D.neighborFinset x).filter (· ∈ A)).filter
        (fun y ↦ s y = s x)).card = crossSame) :
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    (D.adjMatrix ℤ).mulVec t =
      ((2 * (diagSame : ℤ) - diagCard) -
        (2 * (crossSame : ℤ) - crossCard)) • t := by
  classical
  dsimp only
  have hrows := bipartition_signSwitch_eigen_sub_of_card D A B hAB
    (fun _x y _hy ↦ by rw [hpartition]; exact Finset.mem_univ y)
    s diagCard diagSame crossCard crossSame
    (fun x _hx ↦ hsign x) hAAcard hAAsame hABcard hABsame
      hBBcard hBBsame hBAcard hBAsame
  funext x
  rw [D.adjMatrix_mulVec_apply]
  simpa [hpartition] using hrows x (by rw [hpartition]; exact Finset.mem_univ x)

/-- Connected-component row form of the generic shore switch. -/
theorem twoComponent_signSwitch_adjMatrix_eigen_sub_of_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (D H : SimpleGraph X) [DecidableRel D.Adj] [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (a b : H.ConnectedComponent) (hab : a ≠ b)
    (hpartition : ∀ x, x ∈ a.supp ∨ x ∈ b.supp)
    (s : X → ℤ) (diagCard diagSame crossCard crossSame : ℕ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hAAcard : ∀ x, x ∈ a.supp →
      (componentNeighborFinset D H a x).card = diagCard)
    (hAAsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset D H a x).filter
        (fun y ↦ s y = s x)).card = diagSame)
    (hABcard : ∀ x, x ∈ a.supp →
      (componentNeighborFinset D H b x).card = crossCard)
    (hABsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset D H b x).filter
        (fun y ↦ s y = s x)).card = crossSame)
    (hBBcard : ∀ x, x ∈ b.supp →
      (componentNeighborFinset D H b x).card = diagCard)
    (hBBsame : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset D H b x).filter
        (fun y ↦ s y = s x)).card = diagSame)
    (hBAcard : ∀ x, x ∈ b.supp →
      (componentNeighborFinset D H a x).card = crossCard)
    (hBAsame : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset D H a x).filter
        (fun y ↦ s y = s x)).card = crossSame) :
    let B := (Finset.univ : Finset X).filter
      (fun x ↦ H.connectedComponentMk x = b)
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    (D.adjMatrix ℤ).mulVec t =
      ((2 * (diagSame : ℤ) - diagCard) -
        (2 * (crossSame : ℤ) - crossCard)) • t := by
  classical
  dsimp only
  let A := (Finset.univ : Finset X).filter
    (fun x ↦ H.connectedComponentMk x = a)
  let B := (Finset.univ : Finset X).filter
    (fun x ↦ H.connectedComponentMk x = b)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hab ((Finset.mem_filter.mp hxA).2.symm.trans
      (Finset.mem_filter.mp hxB).2)
  have hpart : A ∪ B = Finset.univ := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    rcases hpartition x with hxa | hxb
    · exact Or.inl ((ConnectedComponent.mem_supp_iff a x).mp hxa)
    · exact Or.inr ((ConnectedComponent.mem_supp_iff b x).mp hxb)
  have hrow (d : H.ConnectedComponent) (x : X) :
      (D.neighborFinset x).filter (fun y ↦ y ∈
        (Finset.univ : Finset X).filter
          (fun z ↦ H.connectedComponentMk z = d)) =
      componentNeighborFinset D H d x := by
    ext y
    simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset]
  apply bipartition_signSwitch_adjMatrix_eigen_sub_of_card D A B hAB hpart s
    diagCard diagSame crossCard crossSame hsign
  · intro x hx
    rw [hrow a x]
    exact hAAcard x ((ConnectedComponent.mem_supp_iff a x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow a x]
    exact hAAsame x ((ConnectedComponent.mem_supp_iff a x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow b x]
    exact hABcard x ((ConnectedComponent.mem_supp_iff a x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow b x]
    exact hABsame x ((ConnectedComponent.mem_supp_iff a x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow b x]
    exact hBBcard x ((ConnectedComponent.mem_supp_iff b x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow b x]
    exact hBBsame x ((ConnectedComponent.mem_supp_iff b x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow a x]
    exact hBAcard x ((ConnectedComponent.mem_supp_iff b x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow a x]
    exact hBAsame x ((ConnectedComponent.mem_supp_iff b x).mpr
      (Finset.mem_filter.mp hx).2)

/-- Quotient-level generic shore switch.  Quotient entries provide the four
total block degrees; the remaining hypotheses are exactly the signed-row
counts retained by aligned ledgers. -/
theorem twoComponent_quotient_signSwitch_adjMatrix_eigen_sub_of_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (D H : SimpleGraph X) [DecidableRel D.Adj] [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (a b : H.ConnectedComponent) (hab : a ≠ b)
    (hdegree : ∀ x, H.degree x = 2)
    (hcomm : D.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * D.adjMatrix ℝ)
    (hpartition : ∀ x, x ∈ a.supp ∨ x ∈ b.supp)
    (s : X → ℤ) (diagCard diagSame crossCard crossSame : ℕ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (haa : componentQuotientMatrix D H a a = diagCard)
    (habq : componentQuotientMatrix D H a b = crossCard)
    (hbaq : componentQuotientMatrix D H b a = crossCard)
    (hbb : componentQuotientMatrix D H b b = diagCard)
    (hAAsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset D H a x).filter
        (fun y ↦ s y = s x)).card = diagSame)
    (hABsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset D H b x).filter
        (fun y ↦ s y = s x)).card = crossSame)
    (hBBsame : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset D H b x).filter
        (fun y ↦ s y = s x)).card = diagSame)
    (hBAsame : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset D H a x).filter
        (fun y ↦ s y = s x)).card = crossSame) :
    let B := (Finset.univ : Finset X).filter
      (fun x ↦ H.connectedComponentMk x = b)
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    (D.adjMatrix ℤ).mulVec t =
      ((2 * (diagSame : ℤ) - diagCard) -
        (2 * (crossSame : ℤ) - crossCard)) • t := by
  apply twoComponent_signSwitch_adjMatrix_eigen_sub_of_card
    D H a b hab hpartition s diagCard diagSame crossCard crossSame hsign
  · intro x hx
    rw [← componentQuotientMatrix_apply_eq D H 2 hdegree hcomm a a hx]
    exact haa
  · exact hAAsame
  · intro x hx
    rw [← componentQuotientMatrix_apply_eq D H 2 hdegree hcomm a b hx]
    exact habq
  · exact hABsame
  · intro x hx
    rw [← componentQuotientMatrix_apply_eq D H 2 hdegree hcomm b b hx]
    exact hbb
  · exact hBBsame
  · intro x hx
    rw [← componentQuotientMatrix_apply_eq D H 2 hdegree hcomm b a hx]
    exact hbaq
  · exact hBAsame

end


end Erdos85

#print axioms Erdos85.bipartition_signSwitch_adjMatrix_eigen_sub_of_card
#print axioms Erdos85.twoComponent_signSwitch_adjMatrix_eigen_sub_of_card
#print axioms Erdos85.twoComponent_quotient_signSwitch_adjMatrix_eigen_sub_of_card

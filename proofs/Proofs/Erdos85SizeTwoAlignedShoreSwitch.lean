import Proofs.Erdos85SizeTwoShoreSwitchCardinality

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

end


end Erdos85

#print axioms Erdos85.bipartition_signSwitch_adjMatrix_eigen_sub_of_card

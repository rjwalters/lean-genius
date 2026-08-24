import Proofs.Erdos85C4FreeCommonNeighborUnique
import Proofs.Erdos85ThreeSeparatorExceptionalPointYFlow

/-!
# Overlap of the two Y-located fiber systems

For `c ∈ Y`, a two-point fiber centered in `N_A(c)` and a residual
two-point fiber centered in `R` can represent the same edge only when their
centers coincide.  Such a center lies in `N_A(c) ∩ R`, which has size at
most one by B32.  This is B32'.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Pointwise center identification behind B32': a shared pair of distinct
endpoints cannot have two different centers in a C4-free graph. -/
theorem shared_twoFiber_centers_eq_of_c4Free
    {V : Type*} {A : SimpleGraph V}
    (hfree : ¬ containsC4 V A)
    {x y z r : V} (hxy : x ≠ y)
    (hxz : A.Adj x z) (hyz : A.Adj y z)
    (hxr : A.Adj x r) (hyr : A.Adj y r) :
    z = r := by
  exact commonNeighbor_unique_of_c4Free hfree hxy hxz hyz hxr hyr

/-- An indexed family of shared two-point fibers injects into the possible
common-center set `N_A(c) ∩ R`.  Injectivity of `r` expresses that one
residual center determines only one two-point fiber. -/
theorem shared_twoFiber_index_card_le_commonCenters
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (O : Finset E) (c : V) (R : Finset V)
    (x y z r : E → V)
    (hxy : ∀ e ∈ O, x e ≠ y e)
    (hxz : ∀ e ∈ O, A.Adj (x e) (z e))
    (hyz : ∀ e ∈ O, A.Adj (y e) (z e))
    (hxr : ∀ e ∈ O, A.Adj (x e) (r e))
    (hyr : ∀ e ∈ O, A.Adj (y e) (r e))
    (hzc : ∀ e ∈ O, A.Adj c (z e))
    (hrR : ∀ e ∈ O, r e ∈ R)
    (hrinj : Set.InjOn r O) :
    O.card ≤ (A.neighborFinset c ∩ R).card := by
  apply Finset.card_le_card_of_injOn r
  · intro e he
    have hzr : z e = r e := shared_twoFiber_centers_eq_of_c4Free hfree
      (hxy e he) (hxz e he) (hyz e he) (hxr e he) (hyr e he)
    exact Finset.mem_inter.mpr ⟨
      (A.mem_neighborFinset c (r e)).mpr (hzr ▸ hzc e he), hrR e he⟩
  · exact hrinj

/-- B32' in cardinal form: under the Y-point flow equation, the two fiber
systems have at most one common two-point fiber. -/
theorem shared_twoFiber_index_card_le_one_of_Y_flow
    {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
    (A D : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V A)
    (O : Finset E) (c : V) (W R : Finset V)
    (x y z r : E → V)
    (hxy : ∀ e ∈ O, x e ≠ y e)
    (hxz : ∀ e ∈ O, A.Adj (x e) (z e))
    (hyz : ∀ e ∈ O, A.Adj (y e) (z e))
    (hxr : ∀ e ∈ O, A.Adj (x e) (r e))
    (hyr : ∀ e ∈ O, A.Adj (y e) (r e))
    (hzc : ∀ e ∈ O, A.Adj c (z e))
    (hrR : ∀ e ∈ O, r e ∈ R)
    (hrinj : Set.InjOn r O)
    (hflow : (D.neighborFinset c ∩ W).card +
      (A.neighborFinset c ∩ R).card = 1) :
    O.card ≤ 1 := by
  exact (shared_twoFiber_index_card_le_commonCenters A hfree O c R
    x y z r hxy hxz hyz hxr hyr hzc hrR hrinj).trans
      (exceptionalPoint_Y_R_neighbor_card_le_one A D c W R hflow)

end


end Erdos85


#print axioms Erdos85.shared_twoFiber_centers_eq_of_c4Free
#print axioms Erdos85.shared_twoFiber_index_card_le_commonCenters
#print axioms Erdos85.shared_twoFiber_index_card_le_one_of_Y_flow

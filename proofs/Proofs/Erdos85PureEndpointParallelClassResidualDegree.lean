import Proofs.Erdos85PureEndpointParallelClassDefectBoundary
import Proofs.Erdos85PureEndpointShoreCoordinateBijection

/-!
# Residual defect degree outside a forced parallel class

The owner label is a genuine coordinate on the shore.  We first record its
injectivity; this is the rigidity needed to see that a pair outside a perfect
matching crosses two distinct matching blocks.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At the pure endpoint, two shore points with the same full-center owner
set are equal. -/
theorem c4Free_binarySquare_pureEndpoint_shore_owner_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    Set.InjOn (fun z => G.neighborFinset z ∩ fullLineCenters G S q) S := by
  classical
  let F := fullLineCenters G S q
  let C := {i : V // i ∈ F}
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  let coord : Sum C I → Finset V :=
    Sum.elim (fun i => {i.1}) (fun e => e.1)
  obtain ⟨ψ, hψBij, hcoord⟩ :=
    c4Free_binarySquare_pureEndpoint_shore_coordinate_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hcoordInj : Function.Injective coord := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact singleton_inj.mp (by simpa [coord, C] using hab)
      | inr e =>
        exfalso
        have heCard : e.1.card = 2 := (mem_powersetCard.mp e.2).2
        have hc := congrArg Finset.card hab
        simp [coord, C, I, heCard] at hc
    | inr e =>
      cases b with
      | inl i =>
        exfalso
        have heCard : e.1.card = 2 := (mem_powersetCard.mp e.2).2
        have hc := congrArg Finset.card hab
        simp [coord, C, I, heCard] at hc
      | inr f =>
        apply congrArg Sum.inr
        apply Subtype.ext
        simpa [coord, I] using hab
  intro x hxS y hyS hxy
  obtain ⟨a, ha⟩ := hψBij.2 ⟨x, hxS⟩
  obtain ⟨b, hb⟩ := hψBij.2 ⟨y, hyS⟩
  have habCoord : coord a = coord b := by
    change Sum.elim (fun i : C => {i.1}) (fun e : I => e.1) a =
      Sum.elim (fun i : C => {i.1}) (fun e : I => e.1) b
    rw [← hcoord a, ← hcoord b, ha, hb]
    exact hxy
  have hab : a = b := hcoordInj habCoord
  have hψ : ψ a = ψ b := congrArg ψ hab
  rw [ha, hb] at hψ
  exact congrArg Subtype.val hψ

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_shore_owner_injective

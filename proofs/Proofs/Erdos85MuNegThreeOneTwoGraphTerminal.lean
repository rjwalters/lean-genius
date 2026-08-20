import Proofs.Erdos85MuNegThreeOneTwoGraphService

/-!
# Graph terminal for the `mu=-3`, `(k,r)=(1,2)` endpoint

This is the no-callback consumer of the explicit ledgers and diagonal-five
shore geometry.  The service/algebra adapter builds the finite residual and
the checked owner certificate discharges it.

Node: outline F.3, canonical negative switch endpoint `(-3,1,2)`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

/-- Explicit `(1,2)` ledger data with diagonal-five shores is inconsistent
with an order-64 eight-regular C4-free graph. -/
theorem muNegThree_graph_false_of_ledgers_diagonalFive
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hsize : c.supp.ncard = 8 * 2)
    (ca cb : (G.induce c.supp).ConnectedComponent) (hcab : ca ≠ cb)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = ca.supp) (hvrange : Set.range v = cb.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (haa5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) ca ca = 5)
    (hbb5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) cb cb = 5)
    {N₁ M₁ N₂ M₂ : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L₁ : MuNegThreeExplicitParameterLedger N₁ M₁ f g 1 2)
    (L₂ : MuNegThreeExplicitParameterLedger N₂ M₂ g f 1 2)
    (hD₁ : ∀ i j, i < 8 → j < 8 →
      muNegThreeCrossDefectRel G c u v i j =
        decide (M₁ (i : ZMod 8) (j : ZMod 8) = 1))
    (hD₂ : ∀ i j, i < 8 → j < 8 →
      muNegThreeCrossDefectRel G c u v i j =
        decide (M₂ (j : ZMod 8) (i : ZMod 8) = 1))
    (hpar : ∀ i j : Nat, i < 8 → j < 8 →
      (g (j : ZMod 8) = f (i : ZMod 8) ↔ i % 2 = j % 2))
    (horient : ∃ t : ZMod 8,
      (∀ i j, (g j = f i ∧ M₁ i j = 1) ↔ j = t + i) ∨
      (∀ i j, (g j = f i ∧ M₁ i j = 1) ↔ j = t - i)) : False := by
  obtain ⟨fwd, phase, hphase, hres⟩ :=
    muNegThree_graphResidual_of_ledgers_diagonalFive G c hfree hreg hcard
      hsize ca cb hcab u v huinj hvinj hurange hvrange hu hv haa5 hbb5
      L₁ L₂ hD₁ hD₂ hpar horient
  exact muNegThreeGraph_false_of_residual G c hfree hreg hcard hsize ca cb
    hcab u v huinj hvinj hurange hvrange hu hv hphase hres

end

end Erdos85

#print axioms Erdos85.muNegThree_graph_false_of_ledgers_diagonalFive

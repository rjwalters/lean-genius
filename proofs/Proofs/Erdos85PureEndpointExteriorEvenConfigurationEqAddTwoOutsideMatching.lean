import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddTwoPairMultiplicity
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationOutsideMatching

/-!
# Outside-row matchings for an `m+2` circuit

Exact point multiplicity two makes every exterior row outside the circuit
induce a matching on the circuit rows, just as in the minimum `m+1` stratum.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
/-- Every exterior row outside an endpoint `m+2` even configuration meets
twice as many circuit rows as the number of used circuit points it contains.
In particular, its circuit meeting degree is even. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_outsideMatching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
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
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 2 →
      ∀ u : W, u ∉ T →
        (T.filter fun w => (row u ∩ row w).Nonempty).card =
          2 * ((row u).filter fun y =>
            (T.filter fun w => y ∈ row w).Nonempty).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard u huT
  have hpointOnRow :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_pointMultiplicity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hpoint : ∀ y, (T.filter fun w => y ∈ row w).Nonempty →
      (T.filter fun w => y ∈ row w).card = 2 := by
    intro y hy
    obtain ⟨w, hw⟩ := hy
    have hwData := Finset.mem_filter.mp hw
    exact hpointOnRow w hwData.1 y hwData.2
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hlinearU : ∀ w ∈ T, ((row u) ∩ (row w)).card ≤ 1 := by
    intro w hw
    have huw : u.1 ≠ w.1 := by
      intro h
      apply huT
      simpa [Subtype.ext h] using hw
    exact hdesign.2.1 u.1 (by simpa [F] using (Finset.mem_compl.mp u.2))
      w.1 (by simpa [F] using (Finset.mem_compl.mp w.2)) huw
  exact linear_degree_two_configuration_outside_meeting_eq
    row T u hpoint hlinearU

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_outsideMatching

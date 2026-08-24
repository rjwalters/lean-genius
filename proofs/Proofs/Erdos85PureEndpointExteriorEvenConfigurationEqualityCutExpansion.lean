import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqualityCutDegree
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationCenterHoleParity

/-! # Global cut expansion of a minimum exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- A minimum even exterior configuration in the dyadic endpoint has a
quadratically large row-intersection boundary. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutExpansion
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
      T.card = m + 1 →
      (m + 1) * (m * (q - 4)) + q ≤
        ∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
          (row w ∩ row u).Nonempty).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard
  let hole : W → ℕ := fun w =>
    ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card
  let cut : W → ℕ := fun w =>
    (((Fᶜ.attach : Finset W) \ T).filter fun u =>
      (row w ∩ row u).Nonempty).card
  have hpoint :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutDegree
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  have hmass :=
    (c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_centerHoleParity
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard).2
  have hsum : (∑ w ∈ T, cut w) =
      T.card * (m * (q - 4)) + ∑ w ∈ T, hole w := by
    calc
      (∑ w ∈ T, cut w) = ∑ w ∈ T, (m * (q - 4) + hole w) := by
        apply Finset.sum_congr rfl
        intro w hw
        simpa [cut, hole, row, F] using hpoint w hw
      _ = (∑ _w ∈ T, m * (q - 4)) + ∑ w ∈ T, hole w := by
        rw [Finset.sum_add_distrib]
      _ = T.card * (m * (q - 4)) + ∑ w ∈ T, hole w := by
        simp
  change (m + 1) * (m * (q - 4)) + q ≤ ∑ w ∈ T, cut w
  rw [hsum, hTcard]
  exact Nat.add_le_add_left (by simpa [hole, F] using hmass) _

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutExpansion

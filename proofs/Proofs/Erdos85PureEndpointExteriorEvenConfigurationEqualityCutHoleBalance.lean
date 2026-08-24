import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqualityCutDegree

/-! # Exact cut/hole balance of a minimum exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Globally, the equality circuit cut mass is its uniform base contribution
plus its total full-center defect-hole mass. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutHoleBalance
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
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      (∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
        (row w ∩ row u).Nonempty).card) =
      (m + 1) * (m * (q - 4)) +
        ∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard
  have hpoint :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutDegree
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  calc
    (∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
        (row w ∩ row u).Nonempty).card) =
        ∑ w ∈ T, (m * (q - 4) +
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card) := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hpoint w hw
    _ = (∑ _w ∈ T, m * (q - 4)) +
        ∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card := by
      rw [Finset.sum_add_distrib]
    _ = (m + 1) * (m * (q - 4)) +
        ∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card := by
      simp [hTcard]

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutHoleBalance

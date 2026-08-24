import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqualityCutHoleBalance
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationHoleMassDichotomy

/-! # Cut-mass dichotomy for a minimum exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- The hole-mass minimum/strict-gain dichotomy transferred exactly to the
row-intersection cut. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutMassDichotomy
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
    let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
    let R₁ := S.filter fun y => (owner y).card = 1
    let K : W → Finset V := fun w =>
      (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 1 →
      let C := ∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
        (row w ∩ row u).Nonempty).card
      let U := R₁.filter fun y => (T.filter fun w => G.Adj w.1 y).Nonempty
      (C = (m + 1) * (m * (q - 4)) + q ∧
        (∀ i ∈ F, (T.filter fun w => i ∈ K w).card = 1) ∧
        U.card = m ∧
        ∀ i ∈ F,
          let Uᵢ := S.filter fun y =>
            i ∈ owner y ∧ (T.filter fun w => G.Adj w.1 y).Nonempty
          2 * Uᵢ.card = m) ∨
      (m + 1) * (m * (q - 4)) + q + 2 ≤ C := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let R₁ := S.filter fun y => (owner y).card = 1
  let K : W → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w.1 ∩ F
  intro T heven hTcard
  let H := ∑ w ∈ T, (K w).card
  let U := R₁.filter fun y => (T.filter fun w => G.Adj w.1 y).Nonempty
  have hbalance : (∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
      (row w ∩ row u).Nonempty).card) =
      (m + 1) * (m * (q - 4)) + H := by
    have hb :=
      c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutHoleBalance
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri
        T heven hTcard
    change (∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
      ((G.neighborFinset w.1 ∩ S) ∩
        (G.neighborFinset u.1 ∩ S)).Nonempty).card) =
      (m + 1) * (m * (q - 4)) +
        ∑ w ∈ T,
          ((secondOrderDefectGraph G).neighborFinset w.1 ∩
            fullLineCenters G S q).card
    exact hb
  have hdich :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_holeMassDichotomy
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  rcases hdich with hmin | hstrict
  · left
    change (∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
      (row w ∩ row u).Nonempty).card) =
        (m + 1) * (m * (q - 4)) + q ∧ _
    refine ⟨by
      have hH : H = q := by simpa [H, K, F] using hmin.1
      omega, ?_⟩
    simpa [U, R₁, owner, K, F] using hmin.2
  · right
    change (m + 1) * (m * (q - 4)) + q + 2 ≤
      ∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
        (row w ∩ row u).Nonempty).card
    have hH : q + 2 ≤ H := by simpa [H, K, F] using hstrict
    omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_succ_cutMassDichotomy

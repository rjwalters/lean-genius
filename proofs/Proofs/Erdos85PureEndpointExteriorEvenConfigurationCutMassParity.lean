import Proofs.Erdos85PureEndpointExteriorEvenConfigurationCutParity
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationHoleParity

/-!
# Global cut parity of an even exterior configuration
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Pointwise equality of two parities and even total first mass force even
total second mass. -/
theorem even_sum_right_of_pointwise_even_add_of_even_sum_left
    {α : Type*} [DecidableEq α] (s : Finset α) (a b : α → ℕ)
    (hpoint : ∀ x ∈ s, Even (a x + b x))
    (ha : Even (∑ x ∈ s, a x)) :
    Even (∑ x ∈ s, b x) := by
  have hab : Even (∑ x ∈ s, (a x + b x)) :=
    Finset.even_sum _ hpoint
  have hsplit : (∑ x ∈ s, (a x + b x)) =
      (∑ x ∈ s, a x) + ∑ x ∈ s, b x := by
    rw [sum_add_distrib]
  rw [hsplit] at hab
  exact (Nat.even_add.mp hab).mp ha

/-- The extracted exterior circuit has even row-intersection cut mass. -/
theorem c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_cutMassEven
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
    ∃ T : Finset W, T.Nonempty ∧ m + 1 ≤ T.card ∧
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) ∧
      Even (∑ w ∈ T, (((univ : Finset W) \ T).filter fun u =>
        (row w ∩ row u).Nonempty).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let hole : W → ℕ := fun w =>
    ((secondOrderDefectGraph G).neighborFinset w.1 ∩ F).card
  obtain ⟨T, hT, hlarge, heven, hpoint⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_cutParity
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  let cut : W → ℕ := fun w =>
    (((Fᶜ.attach : Finset W) \ T).filter fun u =>
      (row w ∩ row u).Nonempty).card
  have hholes : Even (∑ w ∈ T, hole w) := by
    simpa [hole, F] using
      c4Free_binarySquare_pureEndpoint_even_exteriorRowConfiguration_holeParity
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri T heven
  have hcuts : Even (∑ w ∈ T, cut w) :=
    even_sum_right_of_pointwise_even_add_of_even_sum_left T hole cut
      (by
        intro w hwT
        simpa [hole, cut, row, F] using hpoint w hwT)
      hholes
  exact ⟨T, hT, hlarge, heven, by simpa [cut, row] using hcuts⟩

end

end Erdos85

#print axioms Erdos85.even_sum_right_of_pointwise_even_add_of_even_sum_left
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_large_even_configuration_cutMassEven

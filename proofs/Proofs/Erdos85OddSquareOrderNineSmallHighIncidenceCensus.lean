import Proofs.Erdos85OddSquareOrderNineIncidenceHistogram

/-! # Exact q=9 incidence histograms for the smallest high sectors

Node: B.3 / GAP B-CLASSIFY.  The five-bin moment ledger collapses completely
at one high vertex and leaves only two profiles at three high vertices.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The unique five-bin incidence histogram when q=9 has one high vertex. -/
theorem squareOrderNine_highIncidence_profile_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 1) :
    let c := squareOrderNineHighIncidenceHistogram G
    c 0 = 71 ∧ c 1 = 10 ∧ c 2 = 0 ∧ c 3 = 0 ∧ c 4 = 0 := by
  dsimp only
  let c := squareOrderNineHighIncidenceHistogram G
  have hledger := squareOrderNine_highIncidenceHistogram_ledger G hcard hp
  dsimp only at hledger
  rw [hhigh] at hledger
  change c 0 = 71 ∧ c 1 = 10 ∧ c 2 = 0 ∧ c 3 = 0 ∧ c 4 = 0
  change
    (∑ t ∈ Finset.range 5, c t) = 81 ∧
    (∑ t ∈ Finset.range 5, t * c t) = 10 * 1 ∧
    (∑ t ∈ Finset.range 5, t ^ 2 * c t) = 1 * (1 + 9) ∧
    1 ≤ c 0 at hledger
  norm_num [Finset.sum_range_succ] at hledger
  omega

/-- At three high vertices, the moment equations allow precisely the empty
triple system or its unique full triple. -/
theorem squareOrderNine_highIncidence_profile_of_three_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3) :
    let c := squareOrderNineHighIncidenceHistogram G
    (c 0 = 54 ∧ c 1 = 24 ∧ c 2 = 3 ∧ c 3 = 0 ∧ c 4 = 0) ∨
      (c 0 = 53 ∧ c 1 = 27 ∧ c 2 = 0 ∧ c 3 = 1 ∧ c 4 = 0) := by
  dsimp only
  let c := squareOrderNineHighIncidenceHistogram G
  have hledger := squareOrderNine_highIncidenceHistogram_ledger G hcard hp
  dsimp only at hledger
  rw [hhigh] at hledger
  change
    (c 0 = 54 ∧ c 1 = 24 ∧ c 2 = 3 ∧ c 3 = 0 ∧ c 4 = 0) ∨
    (c 0 = 53 ∧ c 1 = 27 ∧ c 2 = 0 ∧ c 3 = 1 ∧ c 4 = 0)
  change
    (∑ t ∈ Finset.range 5, c t) = 81 ∧
    (∑ t ∈ Finset.range 5, t * c t) = 10 * 3 ∧
    (∑ t ∈ Finset.range 5, t ^ 2 * c t) = 3 * (3 + 9) ∧
    3 ≤ c 0 at hledger
  norm_num [Finset.sum_range_succ] at hledger
  have hc4 : c 4 = 0 := by omega
  rw [hc4] at hledger ⊢
  have hc3le : c 3 ≤ 1 := by omega
  interval_cases hc3 : c 3 <;> omega

end

end Erdos85

#print axioms Erdos85.squareOrderNine_highIncidence_profile_of_one_high
#print axioms Erdos85.squareOrderNine_highIncidence_profile_of_three_high

import Proofs.Erdos85OddSquareOrderNineIncidenceHistogram

/-! # Exact q=9 incidence histograms at the endpoint h = 15

Node: B.3 / GAP B-CLASSIFY.  The largest surviving high count has only five
integer incidence histograms, making it a bounded structural endpoint.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At fifteen high vertices, exactly five five-bin histograms satisfy the
square-order incidence moments and high-zero-bin constraint. -/
theorem squareOrderNine_highIncidence_profile_of_fifteen_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 15) :
    let c := squareOrderNineHighIncidenceHistogram G
    (c 0 = 16 ∧ c 1 = 0 ∧ c 2 = 45 ∧ c 3 = 20 ∧ c 4 = 0) ∨
    (c 0 = 15 ∧ c 1 = 3 ∧ c 2 = 42 ∧ c 3 = 21 ∧ c 4 = 0) ∨
    (c 0 = 15 ∧ c 1 = 2 ∧ c 2 = 45 ∧ c 3 = 18 ∧ c 4 = 1) ∨
    (c 0 = 15 ∧ c 1 = 1 ∧ c 2 = 48 ∧ c 3 = 15 ∧ c 4 = 2) ∨
    (c 0 = 15 ∧ c 1 = 0 ∧ c 2 = 51 ∧ c 3 = 12 ∧ c 4 = 3) := by
  dsimp only
  let c := squareOrderNineHighIncidenceHistogram G
  have hledger := squareOrderNine_highIncidenceHistogram_ledger G hcard hp
  dsimp only at hledger
  rw [hhigh] at hledger
  change
    (c 0 = 16 ∧ c 1 = 0 ∧ c 2 = 45 ∧ c 3 = 20 ∧ c 4 = 0) ∨
    (c 0 = 15 ∧ c 1 = 3 ∧ c 2 = 42 ∧ c 3 = 21 ∧ c 4 = 0) ∨
    (c 0 = 15 ∧ c 1 = 2 ∧ c 2 = 45 ∧ c 3 = 18 ∧ c 4 = 1) ∨
    (c 0 = 15 ∧ c 1 = 1 ∧ c 2 = 48 ∧ c 3 = 15 ∧ c 4 = 2) ∨
    (c 0 = 15 ∧ c 1 = 0 ∧ c 2 = 51 ∧ c 3 = 12 ∧ c 4 = 3)
  change
    (∑ t ∈ Finset.range 5, c t) = 81 ∧
    (∑ t ∈ Finset.range 5, t * c t) = 10 * 15 ∧
    (∑ t ∈ Finset.range 5, t ^ 2 * c t) = 15 * (15 + 9) ∧
    15 ≤ c 0 at hledger
  norm_num [Finset.sum_range_succ] at hledger
  have hc4le : c 4 ≤ 3 := by omega
  have hc3le : c 3 ≤ 21 := by omega
  interval_cases hc4 : c 4 <;>
    interval_cases hc3 : c 3 <;> omega

end

end Erdos85

#print axioms
  Erdos85.squareOrderNine_highIncidence_profile_of_fifteen_high

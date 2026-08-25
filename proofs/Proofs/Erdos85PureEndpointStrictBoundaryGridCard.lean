import Proofs.Erdos85PureEndpointStrictPrivateCutGap
import Proofs.Erdos85LinearTradeEqualityGridCard

/-!
# The strict-boundary equality grid

At equality in the pure-endpoint private-cut gap, the points of the two
disjoint shores used by both zero and heavy rows form a `(q - 2)` square.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
theorem c4Free_binarySquare_pureEndpoint_privateCut_boundary_usedGrid_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V) (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v, (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (hcut : finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun p =>
        (G.neighborFinset p ∩ fullLineCenters G S q).card = 1) = 2 * q - 4) :
    let F := fullLineCenters G S q
    let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
    let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
    let U := Sᶜ
    let B := Fᶜ
    let r := fun b => (G.neighborFinset b ∩ P).card
    let Z := B.filter fun b => r b = 0
    let H := B.filter fun b => 1 < r b
    ((U ∪ X).filter fun y =>
      0 < (Z.filter fun z => G.Adj z y).card ∧
      0 < (H.filter fun b => G.Adj b y).card).card = (q - 2) * (q - 2) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
  let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
  let U := Sᶜ
  let B := Fᶜ
  let r := fun b => (G.neighborFinset b ∩ P).card
  let Z := B.filter fun b => r b = 0
  let H := B.filter fun b => 1 < r b
  let weight := fun b => r b - 1
  have hs :=
    (c4Free_binarySquare_pureEndpoint_privateCut_gap_boundary_rowProfile_and_saturation
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri).2 hcut
  have hweightCard : ∀ y,
      (∑ b ∈ H.filter (fun b => G.Adj b y), weight b) =
        (H.filter fun b => G.Adj b y).card := by
    intro y
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro b hb
    have hbH : b ∈ H := (Finset.mem_filter.mp hb).1
    have hr : r b = 2 := by
      simpa [F, P, r, H] using hs.2.2.1 b hbH
    simp [weight, hr]
  have hUX : Disjoint U X := by
    apply Finset.disjoint_left.mpr
    intro y hyU hyX
    have hyNotS : y ∉ S := by simpa [U] using hyU
    exact hyNotS ((Finset.mem_filter.mp hyX).1)
  have hpair : ∀ z ∈ Z, ∀ b ∈ H,
      ((U ∪ X).filter fun y => G.Adj z y ∧ G.Adj b y).card = 1 := by
    intro z hz b hb
    rw [Finset.filter_union, Finset.card_union_of_disjoint]
    · simpa [hs.2.2.1 b hb] using
        hs.2.2.2.2.2.2 z hz b hb (by simp [hs.2.2.1 b hb])
    · exact hUX.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hgrid := equalityGrid_used_card_eq_mul_of_used_degree
    G.Adj (U ∪ X) Z H hpair
  apply (hgrid ?_ ?_).trans
  · rw [hs.1, hs.2.1]
  · intro y hy hyZ hyH
    rcases Finset.mem_union.mp hy with hyU | hyX
    · exact hs.2.2.2.1 y hyU
    · have hload : 0 < ∑ b ∈ H.filter (fun b => G.Adj b y), weight b := by
        rw [hweightCard]
        exact hyH
      exact (hs.2.2.2.2.2.1 y hyX hload).1.le
  · intro y hy hyZ hyH
    rcases Finset.mem_union.mp hy with hyU | hyX
    · rw [← hweightCard]
      rw [← hs.2.2.2.2.1 y hyU]
      exact hs.2.2.2.1 y hyU
    · have hload : 0 < ∑ b ∈ H.filter (fun b => G.Adj b y), weight b := by
        rw [hweightCard]
        exact hyH
      rw [← hweightCard, (hs.2.2.2.2.2.1 y hyX hload).2]

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_privateCut_boundary_usedGrid_card

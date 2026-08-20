import Proofs.Erdos85OddSquareOrderNineIncidenceHistogram
import Proofs.Erdos85SquareOrderIncidenceDirichlet

/-! # Defect-quotient equations for the q = 9 incidence bins

Node: B.3 / GAP B-CLASSIFY.  The five-bin moment census is refined by the
pointwise defect equations: on low incidence level `i`, defect degree is
`8-i` and total neighboring incidence is `h-i`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Low vertices with exactly `i` high neighbors at square order `q=9`. -/
def squareOrderNineLowIncidenceBin
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (i : ℕ) : Finset V :=
  ((Finset.univ : Finset V) \ squareOrderHighVertices G 9).filter
    fun x => squareOrderHighIncidenceCount G 9 x = i

/-- Each q=9 low-incidence bin has an exact defect-stub total and an exact
incidence-weighted defect-neighbor total.  These are the quotient equations
needed beyond the scalar five-bin moments. -/
theorem squareOrderNine_lowIncidenceBin_quotient_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (i : ℕ) :
    let H := squareOrderHighVertices G 9
    let D := secondOrderDefectGraph G
    let k := squareOrderHighIncidenceCount G 9
    let B := squareOrderNineLowIncidenceBin G i
    (∑ x ∈ B, D.degree x) = (8 - i) * B.card ∧
      (∑ x ∈ B, ∑ y ∈ D.neighborFinset x, k y) =
        (H.card - i) * B.card := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let L := (Finset.univ : Finset V) \ H
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G 9
  let B := squareOrderNineLowIncidenceBin G i
  have hlow {x : V} (hx : x ∈ B) : G.degree x = 9 := by
    have hxL : x ∈ L := by
      exact (Finset.mem_filter.mp hx).1
    have hxnot : x ∉ H := (Finset.mem_sdiff.mp hxL).2
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (by norm_num) hmin hcover hcard x with hxdeg | hxdeg
    · exact hxdeg
    · have hxH : x ∈ H :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxdeg⟩
      exact (hxnot hxH).elim
  have hki {x : V} (hx : x ∈ B) : k x = i :=
    (Finset.mem_filter.mp hx).2
  have hdegree (x : V) (hx : x ∈ B) : D.degree x = 8 - i := by
    have hp := squareOrder_defectDegree_add_highIncidence_eq_pred
      G hfree (by norm_num) hmin hcover hcard (hlow hx)
    change D.degree x + k x = 9 - 1 at hp
    rw [hki hx] at hp
    omega
  have hneighborWeight (x : V) (hx : x ∈ B) :
      (∑ y ∈ D.neighborFinset x, k y) = H.card - i := by
    have hp := squareOrder_sum_highIncidence_over_defectNeighbors_add_self
      G hfree (by norm_num) hmin hcard (hlow hx)
    change (∑ y ∈ D.neighborFinset x, k y) + k x = H.card at hp
    rw [hki hx] at hp
    omega
  constructor
  · calc
      _ = ∑ _x ∈ B, (8 - i) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hdegree x hx
      _ = (8 - i) * B.card := by
        simp
        ring
  · calc
      _ = ∑ _x ∈ B, (H.card - i) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hneighborWeight x hx
      _ = (H.card - i) * B.card := by
        simp
        ring

end


end Erdos85

#print axioms Erdos85.squareOrderNine_lowIncidenceBin_quotient_ledger

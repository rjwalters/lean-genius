import Proofs.Erdos85OrderFortyNineGeneralHighProfile

/-!
# Triple bound in the five-high stratum

A linear triple system on five high points has at most two blocks.  This
graph-facing corollary removes the apparent three-triple incidence profile
without a SAT computation.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- With five high vertices there are at most two low vertices incident with
three highs. -/
theorem orderFortyNine_highIncidenceCount_three_le_two_of_five_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 5) :
    orderFortyNineHighIncidenceCount G 3 ≤ 2 := by
  let H := orderFortyNineHighVertices G
  let S3 := (orderFortyNineLowVertices G).filter fun x =>
    (orderFortyNineHighSupport G x).card = 3
  have hS3count : S3.card = orderFortyNineHighIncidenceCount G 3 := by
    rfl
  by_contra hnot
  have hthree : 3 ≤ S3.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hthree
  obtain ⟨x, y, z, hxy, hxz, hyz, hT⟩ := Finset.card_eq_three.mp hTcard
  have hxS : x ∈ S3 := hTsub (by simp [hT])
  have hyS : y ∈ S3 := hTsub (by simp [hT])
  have hzS : z ∈ S3 := hTsub (by simp [hT])
  have hx3 : (orderFortyNineHighSupport G x).card = 3 :=
    (Finset.mem_filter.mp hxS).2
  have hy3 : (orderFortyNineHighSupport G y).card = 3 :=
    (Finset.mem_filter.mp hyS).2
  have hz3 : (orderFortyNineHighSupport G z).card = 3 :=
    (Finset.mem_filter.mp hzS).2
  have hxH : orderFortyNineHighSupport G x ⊆ H := by
    intro w hw
    exact (Finset.mem_inter.mp hw).2
  have hyH : orderFortyNineHighSupport G y ⊆ H := by
    intro w hw
    exact (Finset.mem_inter.mp hw).2
  have hzH : orderFortyNineHighSupport G z ⊆ H := by
    intro w hw
    exact (Finset.mem_inter.mp hw).2
  exact not_three_pairwise_linear_triples_of_card_five
    H (orderFortyNineHighSupport G x)
      (orderFortyNineHighSupport G y) (orderFortyNineHighSupport G z)
    (by simpa [H] using hHigh) hxH hyH hzH hx3 hy3 hz3
    (orderFortyNine_card_inter_highSupport_le_one G hfree hxy)
    (orderFortyNine_card_inter_highSupport_le_one G hfree hxz)
    (orderFortyNine_card_inter_highSupport_le_one G hfree hyz)

end

end Erdos85

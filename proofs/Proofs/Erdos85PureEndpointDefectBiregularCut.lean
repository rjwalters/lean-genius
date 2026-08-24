import Proofs.Erdos85PureEndpointDefectCutProfile

/-!
# The pure endpoint defect cut is biregular

The exact replication census and pointwise defect-cut degrees identify the
entire shore boundary.  Only replication-two shore points meet the
complement in the defect graph, and both sides of that cut have degree
`m = q/2` and the same cleared cardinality `q(q-1)`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact biregular description of the second-order-defect cut at the pure
endpoint. -/
theorem c4Free_binarySquare_pureEndpoint_defectCut_biregular
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
    let R₂ := S.filter fun x =>
      (G.neighborFinset x ∩ fullLineCenters G S q).card = 2
    2 * R₂.card = q * (q - 1) ∧
    2 * (Sᶜ : Finset V).card = q * (q - 1) ∧
    (∀ x ∈ R₂,
      ((secondOrderDefectGraph G).neighborFinset x ∩
        (Sᶜ : Finset V)).card = m) ∧
    (∀ y ∈ (Sᶜ : Finset V),
      ((secondOrderDefectGraph G).neighborFinset y ∩ S).card = m) ∧
    (∀ x ∈ S,
      (((secondOrderDefectGraph G).neighborFinset x ∩
          (Sᶜ : Finset V)).card = 0 ↔
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 1)) := by
  classical
  dsimp only
  have hprofile :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hcut := c4Free_binarySquare_pureEndpoint_defectCutDegree_profile
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hcompCard : 2 * (Sᶜ : Finset V).card = q * (q - 1) := by
    have hpartition := Finset.card_compl_add_card S
    rw [hcard] at hpartition
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  refine ⟨hprofile.2.2.1, hcompCard, ?_, ?_, ?_⟩
  · intro x hx
    have hxData := Finset.mem_filter.mp hx
    exact (hcut x).2.1 hxData.1 hxData.2
  · intro y hy
    exact (hcut y).2.2 (by simpa using hy)
  · intro x hxS
    have hxClass := (hprofile.1 x).mp hxS
    constructor
    · intro hzero
      rcases hxClass with hxOne | hxTwo
      · exact hxOne
      · have htwo := (hcut x).2.1 hxS hxTwo
        have hmpos : 0 < m := by omega
        omega
    · intro hxOne
      exact (hcut x).1 hxS hxOne

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_defectCut_biregular

import Proofs.Erdos85PureEndpointDefectBiregularCut

/-!
# A preconnected endpoint has a private-to-pair defect bridge

Private shore points have no defect edge across the shore.  Consequently,
if they also had no defect edge to the replication-two shore class, the
private class would be closed under defect adjacency.  Preconnectedness and
the nonempty off-shore class rule this out.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the preconnected pure endpoint, some replication-one shore point is
defect-adjacent to a replication-two shore point. -/
theorem c4Free_binarySquare_pureEndpoint_exists_private_pair_defectBridge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∃ x ∈ S.filter (fun x =>
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 1),
      ∃ y ∈ S.filter (fun y =>
          (G.neighborFinset y ∩ fullLineCenters G S q).card = 2),
        (secondOrderDefectGraph G).Adj x y := by
  classical
  let D := secondOrderDefectGraph G
  let R₁ := S.filter fun x =>
    (G.neighborFinset x ∩ fullLineCenters G S q).card = 1
  let R₂ := S.filter fun x =>
    (G.neighborFinset x ∩ fullLineCenters G S q).card = 2
  have hprofile :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hcut := c4Free_binarySquare_pureEndpoint_defectCutDegree_profile
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hR₁card : R₁.card = q := by simpa [R₁] using hprofile.2.1
  have hR₁nonempty : R₁.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hxR₁⟩ := hR₁nonempty
  have hScCard : 2 * (Sᶜ : Finset V).card = q * (q - 1) :=
    (c4Free_binarySquare_pureEndpoint_defectCut_biregular
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.1
  have hprodPos : 0 < q * (q - 1) := Nat.mul_pos (by omega) (by omega)
  have hScNonempty : (Sᶜ : Finset V).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨z, hzSc⟩ := hScNonempty
  by_contra hbridge
  push Not at hbridge
  have hclosed : ∀ u v, D.Adj u v → u ∈ R₁ → v ∈ R₁ := by
    intro u v huv huR₁
    have huData := Finset.mem_filter.mp huR₁
    have hvS : v ∈ S := by
      by_contra hvS
      have hvSc : v ∈ (Sᶜ : Finset V) := by simpa using hvS
      have hvCut : v ∈ D.neighborFinset u ∩ (Sᶜ : Finset V) :=
        Finset.mem_inter.mpr ⟨by
          simpa [D, SimpleGraph.mem_neighborFinset] using huv, hvSc⟩
      have hzero := (hcut u).1 huData.1 huData.2
      change (D.neighborFinset u ∩ (Sᶜ : Finset V)).card = 0 at hzero
      rw [Finset.card_eq_zero.mp hzero] at hvCut
      simp at hvCut
    rcases (hprofile.1 v).mp hvS with hvOne | hvTwo
    · exact Finset.mem_filter.mpr ⟨hvS, hvOne⟩
    · have hvR₂ : v ∈ R₂ := Finset.mem_filter.mpr ⟨hvS, hvTwo⟩
      exact (hbridge u huR₁ v hvR₂ huv).elim
  have hpropagate : ∀ {u v}, D.Reachable u v → u ∈ R₁ → v ∈ R₁ := by
    intro u v huv hu
    obtain ⟨p⟩ := huv
    induction p with
    | nil => exact hu
    | cons hadj _ ih => exact ih (hclosed _ _ hadj hu)
  have hreach : D.Reachable x z := hconn x z
  have hzR₁ : z ∈ R₁ := hpropagate hreach hxR₁
  have hzS : z ∈ S := (Finset.mem_filter.mp hzR₁).1
  exact (by simpa using hzSc : z ∉ S) hzS

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_private_pair_defectBridge

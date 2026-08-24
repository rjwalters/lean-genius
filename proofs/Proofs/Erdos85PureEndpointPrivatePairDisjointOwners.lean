import Proofs.Erdos85PureEndpointPrivatePairDefectBridge
import Proofs.Erdos85ExteriorDefectDecomposition

/-!
# Disjoint owners forced by a private-to-pair defect bridge

Preconnectedness forces a defect edge from a private shore point to a pair
point.  Since defect-adjacent vertices have no common graph neighbor, the
private owner cannot be either owner of the pair point.  Thus the endpoint
contains a canonical three-distinct-center configuration.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A preconnected pure endpoint contains a defect-adjacent private/pair
point pair whose owner sets are a singleton and a disjoint two-set. -/
theorem c4Free_binarySquare_pureEndpoint_exists_private_pair_disjointOwners
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
    ∃ x y i j k,
      x ∈ S ∧ y ∈ S ∧
      i ∈ fullLineCenters G S q ∧
      j ∈ fullLineCenters G S q ∧
      k ∈ fullLineCenters G S q ∧
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      G.neighborFinset x ∩ fullLineCenters G S q = {i} ∧
      G.neighborFinset y ∩ fullLineCenters G S q = {j, k} ∧
      (secondOrderDefectGraph G).Adj x y := by
  classical
  let F := fullLineCenters G S q
  let D := secondOrderDefectGraph G
  obtain ⟨x, hxR₁, y, hyR₂, hxyD⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_private_pair_defectBridge
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hxData := Finset.mem_filter.mp hxR₁
  have hyData := Finset.mem_filter.mp hyR₂
  obtain ⟨i, hiOwners⟩ := Finset.card_eq_one.mp hxData.2
  obtain ⟨j, k, hjk, hjkOwners⟩ := Finset.card_eq_two.mp hyData.2
  have hiF : i ∈ F := by
    have : i ∈ G.neighborFinset x ∩ F := by rw [hiOwners]; simp
    exact (Finset.mem_inter.mp this).2
  have hjF : j ∈ F := by
    have : j ∈ G.neighborFinset y ∩ F := by rw [hjkOwners]; simp
    exact (Finset.mem_inter.mp this).2
  have hkF : k ∈ F := by
    have : k ∈ G.neighborFinset y ∩ F := by rw [hjkOwners]; simp
    exact (Finset.mem_inter.mp this).2
  have hxyNe : x ≠ y := D.ne_of_adj hxyD
  have hcommonZero :
      (G.neighborFinset x ∩ G.neighborFinset y).card = 0 :=
    (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hxyNe).mp hxyD
  have hiNotYOwner : i ∉ G.neighborFinset y ∩ F := by
    intro hiY
    have hiX : i ∈ G.neighborFinset x ∩ F := by rw [hiOwners]; simp
    have hiCommon : i ∈ G.neighborFinset x ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hiX).1, (Finset.mem_inter.mp hiY).1⟩
    have : 0 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
      Finset.card_pos.mpr ⟨i, hiCommon⟩
    omega
  have hij : i ≠ j := by
    intro hijEq
    apply hiNotYOwner
    rw [hjkOwners, hijEq]
    simp
  have hik : i ≠ k := by
    intro hikEq
    apply hiNotYOwner
    rw [hjkOwners, hikEq]
    simp
  exact ⟨x, y, i, j, k, hxData.1, hyData.1,
    hiF, hjF, hkF, hij, hik, hjk,
    by simpa [F] using hiOwners,
    by simpa [F] using hjkOwners, hxyD⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_private_pair_disjointOwners

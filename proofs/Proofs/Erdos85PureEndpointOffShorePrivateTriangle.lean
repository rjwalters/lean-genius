import Proofs.Erdos85PureEndpointPrivateDefectClosure
import Proofs.Erdos85ExteriorDefectDecomposition

/-!
# Triangles forced by off-shore full centers at the pure endpoint

The canonical private point of a full center is defect-closed inside the
occupied shore.  If the center itself is off that shore, their graph edge
therefore cannot be a second-order defect edge.  In a `C₄`-free graph this
forces a common neighbor, hence a triangle; fullness puts its third vertex
back on the occupied shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At the pure endpoint, every off-shore full center has a private neighbor
whose incident edge lies in a triangle with a third vertex on `S`. -/
theorem c4Free_binarySquare_pureEndpoint_offShore_privateTriangle
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
    ∃ p : {i // i ∈ fullLineCenters G S q} → V,
      Function.Injective p ∧
      ∀ i, G.Adj i.1 (p i) ∧
        G.neighborFinset (p i) ∩ fullLineCenters G S q = {i.1} ∧
        p i ∈ S ∧
        ((secondOrderDefectGraph G).neighborFinset (p i) ∩
          (Sᶜ : Finset V)).card = 0 ∧
        (i.1 ∉ S →
          (G.neighborFinset (p i) ∩ G.neighborFinset i.1).card = 1 ∧
          ∃ z ∈ S, G.Adj i.1 z ∧ G.Adj (p i) z) := by
  classical
  obtain ⟨p, hpInj, hp⟩ :=
    c4Free_binarySquare_pureEndpoint_privateMatching_defectClosed
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨p, hpInj, ?_⟩
  intro i
  rcases hp i with ⟨hip, hpPrivate, hpS, hpClosed⟩
  refine ⟨hip, hpPrivate, hpS, hpClosed, ?_⟩
  intro hiOff
  have hnotD : ¬ (secondOrderDefectGraph G).Adj (p i) i.1 := by
    intro hD
    have hiN : i.1 ∈ (secondOrderDefectGraph G).neighborFinset (p i) :=
      ((secondOrderDefectGraph G).mem_neighborFinset (p i) i.1).mpr hD
    have hiComp : i.1 ∈ (Sᶜ : Finset V) := by simpa using hiOff
    have hiInter : i.1 ∈
        (secondOrderDefectGraph G).neighborFinset (p i) ∩ (Sᶜ : Finset V) :=
      Finset.mem_inter.mpr ⟨hiN, hiComp⟩
    have hemptyInter :
        (secondOrderDefectGraph G).neighborFinset (p i) ∩
            (Sᶜ : Finset V) = ∅ :=
      Finset.card_eq_zero.mp hpClosed
    rw [hemptyInter] at hiInter
    simp at hiInter
  have hipNe : p i ≠ i.1 := by
    intro heq
    exact G.loopless.irrefl i.1 (heq ▸ hip.symm)
  have hcommonNe :
      (G.neighborFinset (p i) ∩ G.neighborFinset i.1).card ≠ 0 := by
    intro hzero
    exact hnotD
      ((secondOrderDefectGraph_adj_iff_card_common_eq_zero
        G hfree hipNe).mpr hzero)
  have hcommonPos :
      0 < (G.neighborFinset (p i) ∩ G.neighborFinset i.1).card :=
    Nat.pos_of_ne_zero hcommonNe
  have hcommonLe :
      (G.neighborFinset (p i) ∩ G.neighborFinset i.1).card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree (p i) i.1 hipNe
  have hcommonEq :
      (G.neighborFinset (p i) ∩ G.neighborFinset i.1).card = 1 := by
    omega
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hcommonPos
  have hzp : G.Adj (p i) z :=
    (G.mem_neighborFinset (p i) z).mp (Finset.mem_inter.mp hz).1
  have hzi : G.Adj i.1 z :=
    (G.mem_neighborFinset i.1 z).mp (Finset.mem_inter.mp hz).2
  have hiFull := (mem_fullLineCenters G S q i.1).mp i.2
  have hiNeighbors : G.neighborFinset i.1 ∩ S = G.neighborFinset i.1 := by
    apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
    rw [hiFull, G.card_neighborFinset_eq_degree, hreg]
  have hzS : z ∈ S := by
    have hzN : z ∈ G.neighborFinset i.1 :=
      (G.mem_neighborFinset i.1 z).mpr hzi
    have : z ∈ G.neighborFinset i.1 ∩ S := by
      rw [hiNeighbors]
      exact hzN
    exact (Finset.mem_inter.mp this).2
  exact ⟨hcommonEq, z, hzS, hzi, hzp⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_offShore_privateTriangle

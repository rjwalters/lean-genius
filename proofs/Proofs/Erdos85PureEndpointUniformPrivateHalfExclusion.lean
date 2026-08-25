import Proofs.Erdos85PureEndpointPrivateCollisionHalfOccupancy

/-!
# Excluding uniform private occupancy at the pure endpoint

Preconnectedness forces a half-occupancy center adjacent to two distinct
private points.  Consequently the endpoint branch in which every half center
contains exactly one private point is impossible.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At a preconnected pure endpoint, the private-point count on the
half-occupancy centers cannot be identically one. -/
theorem c4Free_binarySquare_pureEndpoint_not_uniform_private_halfOccupancy
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
    ¬ ∀ w, (G.neighborFinset w ∩ S).card = m →
      (G.neighborFinset w ∩
        S.filter (fun x =>
          (G.neighborFinset x ∩ fullLineCenters G S q).card = 1)).card = 1 := by
  intro huniform
  obtain ⟨x, x', w, hxS, hx'S, hxx', hxPrivate, hx'Private,
      hxw, hx'w, _hcommon, hwHalf⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_private_halfOccupancy_collision
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let R₁ := S.filter fun z =>
    (G.neighborFinset z ∩ fullLineCenters G S q).card = 1
  have hxR₁ : x ∈ R₁ := Finset.mem_filter.mpr ⟨hxS, hxPrivate⟩
  have hx'R₁ : x' ∈ R₁ := Finset.mem_filter.mpr ⟨hx'S, hx'Private⟩
  have hxMem : x ∈ G.neighborFinset w ∩ R₁ :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset w x).mpr hxw.symm, hxR₁⟩
  have hx'Mem : x' ∈ G.neighborFinset w ∩ R₁ :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset w x').mpr hx'w.symm, hx'R₁⟩
  have htwo : 2 ≤ (G.neighborFinset w ∩ R₁).card := by
    have hpair : ({x, x'} : Finset V) ⊆ G.neighborFinset w ∩ R₁ := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hxMem
      · exact hx'Mem
    calc
      2 = ({x, x'} : Finset V).card := (Finset.card_pair hxx').symm
      _ ≤ (G.neighborFinset w ∩ R₁).card := Finset.card_le_card hpair
  have hone : (G.neighborFinset w ∩ R₁).card = 1 := by
    simpa [R₁] using huniform w hwHalf
  omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_not_uniform_private_halfOccupancy

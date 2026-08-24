import Proofs.Erdos85PureEndpointOffShorePrivateTriangle
import Proofs.Erdos85PureEndpointOffShoreCenterIsolation

/-!
# Pair-point routing of off-shore full centers

The private edge of an off-shore full center has a unique triangle witness
on the occupied shore.  That witness cannot be another private point of the
same center, since endpoint private points are unique.  The global
replication cap therefore forces it to have exactly two full-center owners.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every off-shore full center is joined through its private point to a
shore point of exceptional replication exactly two. -/
theorem c4Free_binarySquare_pureEndpoint_offShore_pairPoint_route
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
    ∀ i : {i // i ∈ fullLineCenters G S q}, i.1 ∉ S →
      ∃ p z, p ∈ S ∧ z ∈ S ∧
        G.Adj i.1 p ∧
        G.neighborFinset p ∩ fullLineCenters G S q = {i.1} ∧
        G.Adj i.1 z ∧ G.Adj p z ∧
        (G.neighborFinset z ∩ fullLineCenters G S q).card = 2 := by
  classical
  let C := fullLineCenters G S q
  obtain ⟨hDindependent, hcap, _p₀, _hp₀Inj, _hp₀⟩ :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_structure_withReplicationCap
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hpair : ∀ x ∈ C, ∀ y ∈ C, x ≠ y →
      (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
    intro x hx y hy hxy
    have hnotMem : y ∉ (secondOrderDefectGraph G).neighborFinset x := by
      simpa [SimpleGraph.mem_neighborFinset] using
        hDindependent x hx y hy hxy
    have hcommon := card_common_eq_if_secondOrderDefect G hfree x y hxy
    rw [if_neg hnotMem] at hcommon
    exact hcommon
  obtain ⟨p, _hpInj, hp⟩ :=
    c4Free_binarySquare_pureEndpoint_offShore_privateTriangle
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  intro i hiOff
  rcases hp i with ⟨hip, hpPrivate, hpS, _hpClosed, hpTriangle⟩
  obtain ⟨_hcommonOne, z, hzS, hiz, hpz⟩ := hpTriangle hiOff
  have hiRep : i.1 ∈ G.neighborFinset z ∩ C :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset z i.1).mpr hiz.symm, i.2⟩
  have hrepPos : 0 < (G.neighborFinset z ∩ C).card :=
    Finset.card_pos.mpr ⟨i.1, hiRep⟩
  have hrepLe : (G.neighborFinset z ∩ C).card ≤ 2 := hcap z
  have hrepTwo : (G.neighborFinset z ∩ C).card = 2 := by
    by_contra hneTwo
    have hrepOne : (G.neighborFinset z ∩ C).card = 1 := by omega
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hrepOne
    have hiw : i.1 = w := Finset.mem_singleton.mp (hw ▸ hiRep)
    have hzPrivate : G.neighborFinset z ∩ C = {i.1} := by
      simpa [hiw] using hw
    have hzpEq : z = p i :=
      privateNeighbor_eq_of_endpointProfile
        G C (by simpa [C] using hCcard)
        (fun x _hx => hreg x) hpair hcap i
        hiz hzPrivate hip hpPrivate
    rw [hzpEq] at hpz
    exact G.loopless.irrefl (p i) hpz
  exact ⟨p i, z, hpS, hzS, hip, hpPrivate, hiz, hpz, hrepTwo⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_offShore_pairPoint_route

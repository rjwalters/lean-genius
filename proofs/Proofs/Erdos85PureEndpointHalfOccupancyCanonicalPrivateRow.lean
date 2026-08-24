import Proofs.Erdos85PureEndpointHalfOccupancyCoordinateNormalForm
import Proofs.Erdos85PureEndpointCanonicalPrivatePoints

/-!
# The half-occupancy singleton row is the canonical private row

The singleton-owner shore points in the local near-parallel class are not a
new choice: they are exactly the canonical private points of the full
centers.  This identifies their center indices and makes the local row
compatible with the off-shore private-triangle machinery.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The singleton blocks neighboring the forced half-occupancy vertex are
exactly the canonical private-point images of a center subset of the same
cardinality as the defect-center set. -/
theorem c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_canonicalPrivateRow
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
    let F := fullLineCenters G S q
    ∃ p : {i // i ∈ F} → V, ∃ w,
      Function.Injective p ∧
      (∀ i, p i ∈ S ∧ G.Adj i.1 (p i) ∧
        G.neighborFinset (p i) ∩ F = {i.1}) ∧
      let B := G.neighborFinset w ∩ S
      let P := B.filter fun y => (G.neighborFinset y ∩ F).card = 1
      let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
      let L := (Finset.univ : Finset {i // i ∈ F}).filter fun i => p i ∈ B
      B.card = m ∧ 2 ≤ P.card ∧ K.card = P.card ∧
      P = B ∩ Finset.univ.image p ∧ L.image p = P ∧ L.card = K.card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  obtain ⟨p, hpInj, hp, hpSurj⟩ :=
    c4Free_binarySquare_pureEndpoint_privatePoint_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  obtain ⟨w, hBcard, hPtwo, hKcard, _hQK, _hpairB,
      _hnear, _hpairQ, _hQsize, _hQcover⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_coordinateNormalForm
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  let B := G.neighborFinset w ∩ S
  let P := B.filter fun y => (G.neighborFinset y ∩ F).card = 1
  let K := (secondOrderDefectGraph G).neighborFinset w ∩ F
  let L := (Finset.univ : Finset {i // i ∈ F}).filter fun i => p i ∈ B
  have hPRange : P = B ∩ Finset.univ.image p := by
    ext y
    constructor
    · intro hyP
      have hyData := Finset.mem_filter.mp hyP
      obtain ⟨i, hi⟩ := hpSurj y (Finset.mem_inter.mp hyData.1).2
        (by simpa [F] using hyData.2)
      exact Finset.mem_inter.mpr
        ⟨hyData.1, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩⟩
    · intro hy
      have hyData := Finset.mem_inter.mp hy
      obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hyData.2
      apply Finset.mem_filter.mpr
      refine ⟨hyData.1, ?_⟩
      rw [← hi, (hp i).2.2]
      simp
  have hLimage : L.image p = P := by
    ext y
    constructor
    · intro hy
      obtain ⟨i, hiL, hi⟩ := Finset.mem_image.mp hy
      rw [hPRange]
      apply Finset.mem_inter.mpr
      exact ⟨hi ▸ (Finset.mem_filter.mp hiL).2,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩⟩
    · intro hyP
      rw [hPRange] at hyP
      have hyData := Finset.mem_inter.mp hyP
      obtain ⟨i, _hi, hi⟩ := Finset.mem_image.mp hyData.2
      apply Finset.mem_image.mpr
      refine ⟨i, ?_, hi⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ i, hi ▸ hyData.1⟩
  have hLcard : L.card = K.card := by
    have himageCard : (L.image p).card = L.card :=
      Finset.card_image_of_injective L hpInj
    rw [hLimage] at himageCard
    exact himageCard.symm.trans hKcard.symm
  refine ⟨p, w, hpInj, ?_, hBcard, hPtwo, hKcard, hPRange,
    hLimage, hLcard⟩
  intro i
  simpa [F] using hp i

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_canonicalPrivateRow

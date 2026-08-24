import Proofs.Erdos85PureEndpointOffShorePairSelection
import Proofs.Erdos85PureEndpointNeighborOwnerPacking

/-!
# Collision rigidity for private-point selections

Two distinct private points which are both adjacent to a base vertex cannot
also be adjacent to a second common selected point in a C4-free graph.
After aligning the off-shore selection witnesses with the canonical private
points, every collision of the selection on the local private row is
therefore forced to select the base vertex itself.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Two injectively indexed points cannot share two distinct common
neighbors in a C4-free graph. -/
theorem c4Free_injective_privateSelection_collision_eq_base
    {V I : Type*} (G : SimpleGraph V)
    (hfree : ¬ containsC4 V G) {p : I → V}
    (hp : Function.Injective p) {i j : I} (hij : i ≠ j)
    {w z : V} (hiw : G.Adj (p i) w) (hjw : G.Adj (p j) w)
    (hiz : G.Adj (p i) z) (hjz : G.Adj (p j) z) :
    z = w := by
  by_contra hzw
  apply hfree
  exact containsC4_of_two_common (hp.ne hij) hzw
    hiz.symm hjz.symm hiw.symm hjw.symm

/-- At a preconnected pure endpoint, the canonical private-point map and
the off-shore pair selection can be chosen so that the selection is aligned
with the private points.  On the private points adjacent to the forced
half-occupancy vertex, a selection collision can only land at that vertex. -/
theorem c4Free_binarySquare_pureEndpoint_privateSelection_collisionRigidity
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
    let C := {i : V // i ∈ F}
    let I := {e : Finset V // e ∈ F.powersetCard 2}
    let O := {i : V // i ∈ F ∧ i ∉ S}
    ∃ p : C → V, ∃ φ : I → V, ∃ σ : O → I, ∃ w,
      Function.Injective p ∧ Function.Injective φ ∧
      (G.neighborFinset w ∩ S).card = m ∧
      (∃ i j : C, i ≠ j ∧ G.Adj (p i) w ∧ G.Adj (p j) w) ∧
      (∀ i : O, i.1 ∈ (σ i).1) ∧
      (∀ i : O, G.Adj (p ⟨i.1, i.2.1⟩) (φ (σ i))) ∧
      ∀ i j : O, i ≠ j →
        G.Adj (p ⟨i.1, i.2.1⟩) w →
        G.Adj (p ⟨j.1, j.2.1⟩) w →
        σ i = σ j → φ (σ i) = w := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let C := {i : V // i ∈ F}
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  let O := {i : V // i ∈ F ∧ i ∉ S}
  obtain ⟨p, hpInj, hp, hpSurj⟩ :=
    c4Free_binarySquare_pureEndpoint_privatePoint_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  obtain ⟨φ, hφInj, hφ, _hφSurj, σ, hσ⟩ :=
    c4Free_binarySquare_pureEndpoint_offShore_pairSelection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  obtain ⟨x, x', w, hxS, hx'S, hxx', hxOne, hx'One,
      hxw, hx'w, hwCard, _hwNotFull, _hlabels, _hpair⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_halfOccupancy_ownerPacking
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have halign : ∀ i : O, G.Adj (p ⟨i.1, i.2.1⟩) (φ (σ i)) := by
    intro i
    obtain ⟨_hiMem, r, hrS, _hir, hrOwner, hrφ⟩ := hσ i
    have hrOne : (G.neighborFinset r ∩ F).card = 1 := by
      rw [show G.neighborFinset r ∩ F = {i.1} by simpa [F] using hrOwner]
      simp
    obtain ⟨j, hj⟩ := hpSurj r hrS (by simpa [F] using hrOne)
    have hownersJ := (hp j).2.2
    have hsingle : ({j.1} : Finset V) = {i.1} := by
      calc
        {j.1} = G.neighborFinset (p j) ∩ F := hownersJ.symm
        _ = G.neighborFinset r ∩ F := by rw [hj]
        _ = {i.1} := by simpa [F] using hrOwner
    have hji : j = (⟨i.1, i.2.1⟩ : C) := by
      apply Subtype.ext
      simpa using Finset.singleton_inj.mp hsingle
    rw [← hji, hj]
    exact hrφ
  obtain ⟨ix, hix⟩ := hpSurj x hxS (by simpa [F] using hxOne)
  obtain ⟨ix', hix'⟩ := hpSurj x' hx'S (by simpa [F] using hx'One)
  have hixNe : ix ≠ ix' := by
    intro h
    apply hxx'
    calc
      x = p ix := hix.symm
      _ = p ix' := by rw [h]
      _ = x' := hix'
  refine ⟨p, φ, σ, w, hpInj, hφInj, hwCard,
    ⟨ix, ix', hixNe, ?_, ?_⟩, (fun i => (hσ i).1), halign, ?_⟩
  · simpa [hix] using hxw
  · simpa [hix'] using hx'w
  · intro i j hij hiw hjw hσij
    apply c4Free_injective_privateSelection_collision_eq_base
      G hfree hpInj (show (⟨i.1, i.2.1⟩ : C) ≠ ⟨j.1, j.2.1⟩ by
        intro h
        apply hij
        have hv : i.1 = j.1 := congrArg (fun x : C => x.1) h
        exact Subtype.ext hv) hiw hjw
    · exact halign i
    · rw [hσij]
      exact halign j

end

end Erdos85

#print axioms Erdos85.c4Free_injective_privateSelection_collision_eq_base
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_privateSelection_collisionRigidity

import Proofs.Erdos85PureEndpointPrivateSelectionRowCapacity

/-!
# Universal private-selection capacity

The canonical private-point and pair-selection maps do not depend on the
forced half-occupancy row.  Their almost-injectivity argument therefore holds
simultaneously at every base vertex, making the local capacity bound available
for global double counting.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At a pure endpoint, choose the canonical private points and off-shore pair
selection once.  In every row, the off-shore private points adjacent to the
row base lose at most one element under the pair selection. -/
theorem c4Free_binarySquare_pureEndpoint_universal_privateSelection_capacity
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
    let F := fullLineCenters G S q
    let C := {i : V // i ∈ F}
    let I := {e : Finset V // e ∈ F.powersetCard 2}
    let O := {i : V // i ∈ F ∧ i ∉ S}
    ∃ p : C → V, ∃ φ : I → V, ∃ σ : O → I,
      Function.Injective p ∧ Function.Injective φ ∧
      (∀ i : O, i.1 ∈ (σ i).1) ∧
      (∀ i : O, G.Adj (p ⟨i.1, i.2.1⟩) (φ (σ i))) ∧
      ∀ w : V,
        let A := (Finset.univ : Finset O).filter fun i =>
          G.Adj (p ⟨i.1, i.2.1⟩) w
        A.card ≤ (A.image σ).card + 1 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let C := {i : V // i ∈ F}
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  let O := {i : V // i ∈ F ∧ i ∉ S}
  obtain ⟨p, hpInj, hp, hpSurj⟩ :=
    c4Free_binarySquare_pureEndpoint_privatePoint_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  obtain ⟨φ, hφInj, _hφ, _hφSurj, σ, hσ⟩ :=
    c4Free_binarySquare_pureEndpoint_offShore_pairSelection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have halign : ∀ i : O,
      G.Adj (p ⟨i.1, i.2.1⟩) (φ (σ i)) := by
    intro i
    obtain ⟨_hiMem, r, hrS, _hir, hrOwner, hrφ⟩ := hσ i
    have hrOne : (G.neighborFinset r ∩ F).card = 1 := by
      rw [show G.neighborFinset r ∩ F = {i.1} by simpa [F] using hrOwner]
      simp
    obtain ⟨j, hj⟩ := hpSurj r hrS (by simpa [F] using hrOne)
    have hsingle : ({j.1} : Finset V) = {i.1} := by
      calc
        {j.1} = G.neighborFinset (p j) ∩ F := (hp j).2.2.symm
        _ = G.neighborFinset r ∩ F := by rw [hj]
        _ = {i.1} := by simpa [F] using hrOwner
    have hji : j = (⟨i.1, i.2.1⟩ : C) := by
      apply Subtype.ext
      simpa using Finset.singleton_inj.mp hsingle
    rw [← hji, hj]
    exact hrφ
  refine ⟨p, φ, σ, hpInj, hφInj, (fun i => (hσ i).1), halign, ?_⟩
  intro w
  let A := (Finset.univ : Finset O).filter fun i =>
    G.Adj (p ⟨i.1, i.2.1⟩) w
  have hfiber : ∀ e : I, (A.filter fun i => σ i = e).card ≤ 2 := by
    intro e
    have hsub : A.filter (fun i => σ i = e) ⊆
        (Finset.univ : Finset O).filter fun i => σ i = e := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
    apply (Finset.card_le_card hsub).trans
    apply incident_twoSubset_selection_fiber_card_le_two
      (val := fun i : O => i.1) (edge := fun e : I => e.1)
      (σ := σ) (e := e)
    · exact Subtype.val_injective
    · intro a
      exact (Finset.mem_powersetCard.1 a.2).2
    · exact fun i => (hσ i).1
  apply card_le_card_image_add_one_of_unique_exceptional_collision
    A σ φ w hφInj hfiber
  intro i hiA j hjA hij hσij
  apply c4Free_injective_privateSelection_collision_eq_base
    G hfree hpInj (show (⟨i.1, i.2.1⟩ : C) ≠ ⟨j.1, j.2.1⟩ by
      intro h
      apply hij
      exact Subtype.ext (congrArg (fun x : C => x.1) h))
  · exact (Finset.mem_filter.mp hiA).2
  · exact (Finset.mem_filter.mp hjA).2
  · exact halign i
  · rw [hσij]
    exact halign j

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_universal_privateSelection_capacity

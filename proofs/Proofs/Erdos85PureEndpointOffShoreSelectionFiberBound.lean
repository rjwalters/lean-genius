import Proofs.Erdos85PureEndpointOffShorePairSelection

/-!
# Capacity of the off-shore canonical pair selection

Any selection of a two-subset which contains the selected center has fibers of
size at most two.  Applied to the endpoint selection map, this gives a direct
counting interface for the private-triangle routes.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A map which assigns to each center a two-set containing that center has
fibers of cardinality at most two. -/
theorem incident_twoSubset_selection_fiber_card_le_two
    {V O I : Type*} [Fintype O] [DecidableEq O] [DecidableEq I]
    (val : O → V) (edge : I → Finset V) (σ : O → I)
    (hval : Function.Injective val)
    (hedge : ∀ e, (edge e).card = 2)
    (hinc : ∀ i, val i ∈ edge (σ i)) (e : I) :
    ((univ : Finset O).filter fun i => σ i = e).card ≤ 2 := by
  classical
  let f : ↥((univ : Finset O).filter fun i => σ i = e) →
      ↥(edge e) := fun i =>
    ⟨val i.1, by
      have hiσ : σ i.1 = e := (mem_filter.1 i.2).2
      simpa [hiσ] using hinc i.1⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact hval (congrArg Subtype.val hij)
  have hc := Fintype.card_le_of_injective f hf
  calc
    ((univ : Finset O).filter fun i => σ i = e).card =
        Fintype.card ↥((univ : Finset O).filter fun i => σ i = e) :=
      (Fintype.card_coe _).symm
    _ ≤ Fintype.card ↥(edge e) := hc
    _ = (edge e).card := Fintype.card_coe _
    _ = 2 := hedge e

/-- The canonical off-shore selection has capacity two on every pair block. -/
theorem c4Free_binarySquare_pureEndpoint_offShore_pairSelection_fiberBound
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
    let I := {e : Finset V // e ∈ F.powersetCard 2}
    let O := {i : V // i ∈ F ∧ i ∉ S}
    ∃ φ : I → V, Function.Injective φ ∧
      (∀ e, φ e ∈ S ∧ G.neighborFinset (φ e) ∩ F = e.1) ∧
      (∀ z, z ∈ S → (G.neighborFinset z ∩ F).card = 2 →
        ∃ e, φ e = z) ∧
      ∃ σ : O → I,
        (∀ i, i.1 ∈ (σ i).1 ∧
          ∃ p, p ∈ S ∧ G.Adj i.1 p ∧
            G.neighborFinset p ∩ F = {i.1} ∧ G.Adj p (φ (σ i))) ∧
        ∀ e, ((univ : Finset O).filter fun i => σ i = e).card ≤ 2 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  let O := {i : V // i ∈ F ∧ i ∉ S}
  obtain ⟨φ, hφInj, hφ, hφSurj, σ, hσ⟩ :=
    c4Free_binarySquare_pureEndpoint_offShore_pairSelection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨φ, hφInj, hφ, hφSurj, σ, hσ, ?_⟩
  intro e
  apply incident_twoSubset_selection_fiber_card_le_two
      (val := fun i : O => i.1) (edge := fun e : I => e.1)
      (σ := σ) (e := e)
  · exact Subtype.val_injective
  · intro a
    exact (mem_powersetCard.1 a.2).2
  · intro i
    exact (hσ i).1

end

end Erdos85

#print axioms Erdos85.incident_twoSubset_selection_fiber_card_le_two
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_offShore_pairSelection_fiberBound

import Proofs.Erdos85PureEndpointOffShorePartnerRoute
import Proofs.Erdos85PureEndpointCanonicalPairPoints

/-!
# Canonical pair selection by off-shore endpoint centers

Using the canonical bijection between two-subsets of the full centers and
replication-two shore points, the off-shore partner route becomes a genuine
selection map.  Each off-shore center selects a pair containing itself, and
its private point is adjacent to the canonical point of that pair.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Off-shore centers select incident two-subsets of the full-center family,
with the private-triangle edge landing at the canonical pair point. -/
theorem c4Free_binarySquare_pureEndpoint_offShore_pairSelection
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
      ∃ σ : O → I, ∀ i,
        i.1 ∈ (σ i).1 ∧
        ∃ p, p ∈ S ∧ G.Adj i.1 p ∧
          G.neighborFinset p ∩ F = {i.1} ∧ G.Adj p (φ (σ i)) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  let O := {i : V // i ∈ F ∧ i ∉ S}
  obtain ⟨φ, hφInj, hφ, hφSurj⟩ :=
    c4Free_binarySquare_pureEndpoint_pairPoint_bijection
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hdata : ∀ i : O, ∃ e : I,
      i.1 ∈ e.1 ∧
      ∃ p, p ∈ S ∧ G.Adj i.1 p ∧
        G.neighborFinset p ∩ F = {i.1} ∧ G.Adj p (φ e) := by
    intro i
    let iF : {i // i ∈ fullLineCenters G S q} := ⟨i.1, i.2.1⟩
    obtain ⟨j, p, z, hji, hpS, hzS, hip, hpPrivate, _hiz, hpz, hzOwners⟩ :=
      c4Free_binarySquare_pureEndpoint_offShore_partnerCenter_route
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri iF i.2.2
    have hzTwo : (G.neighborFinset z ∩ F).card = 2 := by
      rw [show G.neighborFinset z ∩ F = {i.1, j.1} by
        simpa [F, iF] using hzOwners]
      exact Finset.card_pair (fun hij => hji (Subtype.ext hij.symm))
    obtain ⟨e, hez⟩ := hφSurj z hzS (by simpa [F] using hzTwo)
    have hiOwners : i.1 ∈ G.neighborFinset z ∩ F := by
      rw [show G.neighborFinset z ∩ F = {i.1, j.1} by
        simpa [F, iF] using hzOwners]
      simp
    have hiE : i.1 ∈ e.1 := by
      have heq : G.neighborFinset z ∩ F = e.1 := by
        rw [← hez]
        simpa [F] using (hφ e).2
      rw [← heq]
      exact hiOwners
    refine ⟨e, hiE, p, hpS, hip, ?_, ?_⟩
    · simpa [F, iF] using hpPrivate
    · simpa [hez] using hpz
  let σ : O → I := fun i => (hdata i).choose
  refine ⟨φ, hφInj, ?_, ?_, σ, ?_⟩
  · intro e
    simpa [F] using hφ e
  · intro z hzS hzTwo
    exact hφSurj z hzS (by simpa [F] using hzTwo)
  · intro i
    exact (hdata i).choose_spec

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_offShore_pairSelection

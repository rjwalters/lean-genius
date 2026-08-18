import Proofs.Erdos85Problem

open SimpleGraph

namespace Erdos85

universe u

theorem CommonNeighborIndependent.sum_degrees_le_card
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hsafe : CommonNeighborIndependent G S) :
    ∑ x ∈ S, G.degree x ≤ Fintype.card V := by
  let X := {x : V // x ∈ S}
  let N : X → Type u := fun x => {v : V // v ∈ G.neighborFinset x.1}
  let f : (Σ x : X, N x) → V := fun p => p.2.1
  have hf : Function.Injective f := by
    rintro ⟨x, v⟩ ⟨y, w⟩ h
    have hvw : v.1 = w.1 := h
    have hxy : x.1 = y.1 := by
      by_contra hxy
      have hz : v.1 ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
        rw [Finset.mem_inter]
        refine ⟨v.2, ?_⟩
        rw [hvw]
        exact w.2
      have hempty := hsafe x.2 y.2 hxy
      rw [Finset.card_eq_zero] at hempty
      exact Finset.notMem_empty v.1 (hempty ▸ hz)
    have hxySub : x = y := Subtype.ext hxy
    cases hxySub
    have hvEq : v = w := Subtype.ext hvw
    cases hvEq
    rfl
  have hc := Fintype.card_le_of_injective f hf
  change Fintype.card (Σ x : X, N x) ≤ Fintype.card V at hc
  rw [Fintype.card_sigma] at hc
  have hsum : (∑ x ∈ S, G.degree x) = ∑ x : X, Fintype.card (N x) := by
    rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro x hx
    dsimp [N]
    rw [SimpleGraph.degree, Fintype.card_coe]
  rw [hsum]
  exact hc

theorem CommonNeighborIndependent.card_mul_le_card_of_minDegree
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hsafe : CommonNeighborIndependent G S) {d : ℕ}
    (hdeg : d ≤ G.minDegree) :
    S.card * d ≤ Fintype.card V := by
  calc
    S.card * d = ∑ _x ∈ S, d := by simp
    _ ≤ ∑ x ∈ S, G.degree x := by
      apply Finset.sum_le_sum
      intro x hx
      exact hdeg.trans (G.minDegree_le_degree x)
    _ ≤ Fintype.card V := hsafe.sum_degrees_le_card G S

end Erdos85

import Proofs.Erdos85ThreeSeparatorExceptionalPointYTransversal

/-!
# Saturating the large-shore exceptional transversal

The B17Y' transversal occupies `q-2` of the `q` neighbors of `c`.  Once the
two unused neighbors are known to lie in the two-point K-section, cardinal
saturation identifies the image exactly with `N_A(c) \ K`.  This is B17Y''.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Generic finite-set saturation behind B17Y''. -/
theorem transversalImage_eq_neighbor_sdiff_cover
    {V : Type*} [DecidableEq V]
    (N P K : Finset V) (q : ℕ)
    (hq2 : 2 ≤ q)
    (hPN : P ⊆ N)
    (hNcard : N.card = q)
    (hPcard : P.card = q - 2)
    (hunusedK : N \ P ⊆ K)
    (hNKcard : (N ∩ K).card = 2) :
    N \ P = N ∩ K ∧ P = N \ K := by
  have hunusedSubset : N \ P ⊆ N ∩ K := by
    intro x hx
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx).1, hunusedK hx⟩
  have hunusedCard : (N \ P).card = 2 := by
    rw [Finset.card_sdiff_of_subset hPN, hNcard, hPcard]
    omega
  have hunusedEq : N \ P = N ∩ K := by
    apply Finset.eq_of_subset_of_card_le hunusedSubset
    rw [hNKcard, hunusedCard]
  refine ⟨hunusedEq, ?_⟩
  ext x
  constructor
  · intro hxP
    have hxN : x ∈ N := hPN hxP
    have hxNotK : x ∉ K := by
      intro hxK
      have hxInter : x ∈ N ∩ K := Finset.mem_inter.mpr ⟨hxN, hxK⟩
      rw [← hunusedEq] at hxInter
      exact (Finset.mem_sdiff.mp hxInter).2 hxP
    exact Finset.mem_sdiff.mpr ⟨hxN, hxNotK⟩
  · intro hx
    obtain ⟨hxN, hxNotK⟩ := Finset.mem_sdiff.mp hx
    by_contra hxNotP
    have hxUnused : x ∈ N \ P := Finset.mem_sdiff.mpr ⟨hxN, hxNotP⟩
    rw [hunusedEq] at hxUnused
    exact hxNotK (Finset.mem_inter.mp hxUnused).2

/-- Graph-facing B17Y'' saturation for the exceptional-point neighborhood. -/
theorem exceptionalPoint_Y_transversalImage_eq_nonK_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (P K : Finset V) (c : V) (q : ℕ)
    (hq2 : 2 ≤ q)
    (hdegree : A.degree c = q)
    (hPsub : P ⊆ A.neighborFinset c)
    (hPcard : P.card = q - 2)
    (hunusedK : A.neighborFinset c \ P ⊆ K)
    (hKneighbors : (A.neighborFinset c ∩ K).card = 2) :
    A.neighborFinset c \ P = A.neighborFinset c ∩ K ∧
      P = A.neighborFinset c \ K := by
  apply transversalImage_eq_neighbor_sdiff_cover
    (A.neighborFinset c) P K q hq2 hPsub
  · simpa using hdegree
  · exact hPcard
  · exact hunusedK
  · exact hKneighbors

end

end Erdos85

#print axioms Erdos85.transversalImage_eq_neighbor_sdiff_cover
#print axioms Erdos85.exceptionalPoint_Y_transversalImage_eq_nonK_neighbors

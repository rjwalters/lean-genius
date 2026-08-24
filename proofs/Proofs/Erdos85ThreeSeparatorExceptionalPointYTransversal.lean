import Proofs.Erdos85ThreeSeparatorExceptionalPointYLocation

/-!
# The exceptional-point transversal on the large-shore branch

When `c ∈ Y`, every endpoint-clique point has a common A-neighbor with
`c`.  Distinct clique points have disjoint A-neighborhoods, so these centers
are distinct.  This gives the injection in (B17Y').
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Graph-facing B17Y' transversal.  The final cardinal identity records
that exactly two neighbors of `c` lie outside the image. -/
theorem exists_exceptionalPoint_Y_commonNeighbor_transversal
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X : Finset V) (c : V) (q : ℕ)
    (hq2 : 2 ≤ q)
    (hdegree : A.degree c = q)
    (hXcard : X.card = q - 2)
    (hcenter : ∀ x ∈ X, ∃ y : V, A.Adj c y ∧ A.Adj x y)
    (hdisjoint : ∀ x ∈ X, ∀ x' ∈ X, x ≠ x' →
      Disjoint (A.neighborFinset x) (A.neighborFinset x')) :
    ∃ ψ : (↑X : Set V) ↪ (↑(A.neighborFinset c) : Set V),
      (∀ x, A.Adj x.1 (ψ x).1) ∧
      Fintype.card (↑(A.neighborFinset c) : Set V) =
        Fintype.card (↑X : Set V) + 2 := by
  choose center hcenterAdj using fun x : (↑X : Set V) ↦ hcenter x.1 x.2
  let f : (↑X : Set V) → (↑(A.neighborFinset c) : Set V) :=
    fun x ↦ ⟨center x, by simpa using (hcenterAdj x).1⟩
  have hfAdj : ∀ x, A.Adj x.1 (f x).1 := fun x ↦ (hcenterAdj x).2
  have hfInj : Function.Injective f := by
    intro x x' heq
    apply Subtype.ext
    by_contra hxx'
    have hd := hdisjoint x.1 x.2 x'.1 x'.2 hxx'
    have hyLeft : (f x).1 ∈ A.neighborFinset x.1 := by
      simpa using hfAdj x
    have hyRight : (f x).1 ∈ A.neighborFinset x'.1 := by
      have : A.Adj x'.1 (f x').1 := hfAdj x'
      rw [← heq] at this
      simpa using this
    exact Finset.disjoint_left.mp hd hyLeft hyRight
  let ψ : (↑X : Set V) ↪ (↑(A.neighborFinset c) : Set V) := ⟨f, hfInj⟩
  refine ⟨ψ, fun x ↦ hfAdj x, ?_⟩
  change Fintype.card ↑(A.neighborFinset c) = Fintype.card ↑X + 2
  rw [Fintype.card_coe, Fintype.card_coe,
    A.card_neighborFinset_eq_degree, hdegree, hXcard]
  omega

end

end Erdos85

#print axioms Erdos85.exists_exceptionalPoint_Y_commonNeighbor_transversal

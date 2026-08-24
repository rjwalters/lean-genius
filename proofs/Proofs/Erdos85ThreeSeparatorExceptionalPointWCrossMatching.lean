import Proofs.Erdos85ThreeSeparatorExceptionalPointWExactLocation

/-!
# The two-edge cross matching in the separator branch

When `c ∈ W`, B17W' leaves two K-points in `X` and two nonexceptional
separator vertices.  The signed profiles give cross-degree one on both
sides, hence the two cross edges form an exact matching.  This is (B17W'').
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Any finite bipartite incidence relation with degree exactly one on both
sides is an adjacency-preserving equivalence. -/
theorem exists_equiv_of_cross_neighbor_card_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (L R : Finset V)
    (hL : ∀ x ∈ L, (G.neighborFinset x ∩ R).card = 1)
    (hR : ∀ y ∈ R, (G.neighborFinset y ∩ L).card = 1) :
    ∃ e : L ≃ R, ∀ x : L, G.Adj x.1 (e x).1 := by
  have hLunique (x : L) : ∃! y, y ∈ R ∧ G.Adj x.1 y :=
    existsUnique_adj_of_neighborFinset_inter_card_one G x.1 R (hL x.1 x.2)
  let f : L → R := fun x =>
    ⟨Classical.choose (hLunique x),
      (Classical.choose_spec (hLunique x)).1.1⟩
  have hfadj (x : L) : G.Adj x.1 (f x).1 :=
    (Classical.choose_spec (hLunique x)).1.2
  have hfinj : Function.Injective f := by
    intro x₁ x₂ heq
    apply Subtype.ext
    have huniq := existsUnique_adj_of_neighborFinset_inter_card_one
      G (f x₁).1 L (hR (f x₁).1 (f x₁).2)
    have hx₁ : x₁.1 ∈ L ∧ G.Adj (f x₁).1 x₁.1 :=
      ⟨x₁.2, (hfadj x₁).symm⟩
    have hx₂ : x₂.1 ∈ L ∧ G.Adj (f x₁).1 x₂.1 := by
      refine ⟨x₂.2, ?_⟩
      rw [heq]
      exact (hfadj x₂).symm
    exact huniq.unique hx₁ hx₂
  have hfsurj : Function.Surjective f := by
    intro y
    have huniq := existsUnique_adj_of_neighborFinset_inter_card_one
      G y.1 L (hR y.1 y.2)
    let x : L := ⟨Classical.choose huniq, (Classical.choose_spec huniq).1.1⟩
    refine ⟨x, Subtype.ext ?_⟩
    have hy : y.1 ∈ R ∧ G.Adj x.1 y.1 :=
      ⟨y.2, (Classical.choose_spec huniq).1.2.symm⟩
    have hf : (f x).1 ∈ R ∧ G.Adj x.1 (f x).1 := ⟨(f x).2, hfadj x⟩
    exact (hLunique x).unique hf hy
  let e : L ≃ R := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨e, ?_⟩
  intro x
  exact hfadj x

/-- B17W'' specialized to the two exact endpoint sets. -/
theorem exists_exceptionalPoint_W_crossMatching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X W K : Finset V) (c : V)
    (hleft : ∀ x ∈ K ∩ X,
      (G.neighborFinset x ∩ (W \ {c})).card = 1)
    (hright : ∀ w ∈ W \ {c},
      (G.neighborFinset w ∩ (K ∩ X)).card = 1) :
    ∃ e : ↥(K ∩ X) ≃ ↥(W \ {c}),
      ∀ x : ↥(K ∩ X), G.Adj x.1 (e x).1 :=
  exists_equiv_of_cross_neighbor_card_one G (K ∩ X) (W \ {c}) hleft hright

#print axioms exists_equiv_of_cross_neighbor_card_one
#print axioms exists_exceptionalPoint_W_crossMatching

end

end Erdos85

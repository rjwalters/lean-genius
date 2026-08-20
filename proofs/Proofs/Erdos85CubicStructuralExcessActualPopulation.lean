import Proofs.Erdos85CubicStructuralExcessBaseline
import Proofs.Erdos85SameShoreNonantipodalTargetFinset
import Proofs.Erdos85CrossEdgeCoordinateRepresentation

/-! # The actual forty structurally good h305 service rows -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem shoreTypeEdgeFinset_disjoint_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (U : Finset V) {p q : ℕ} (hpq : p ≠ q) :
    Disjoint (shoreTypeEdgeFinset R U p) (shoreTypeEdgeFinset R U q) := by
  rw [Finset.disjoint_left]
  intro a hap haq
  have hp := (Finset.mem_filter.mp hap).2
  have hq := (Finset.mem_filter.mp haq).2
  exact hpq (hp.symm.trans hq)

/-- The 24 cross targets together with the eight nonantipodal targets on
each shore form a concrete forty-element family. -/
theorem h305_cubicStructuralGoodTargetFinset_card_forty
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hRreg : ∀ x, R.degree x = 6) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    let S := shoreTypeEdgeFinset R U 1
    let Nu := h305SameShoreNonantipodalTargetFinset R u hmodeu
    let Nv := h305SameShoreNonantipodalTargetFinset R v hmodev
    (S ∪ Nu ∪ Nv).card = 40 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let W := (Finset.univ : Finset (ZMod 8)).image v
  let S := shoreTypeEdgeFinset R U 1
  let Nu := h305SameShoreNonantipodalTargetFinset R u hmodeu
  let Nv := h305SameShoreNonantipodalTargetFinset R v hmodev
  have hpop := h305_correctShoreModes_typePopulations_of_coordinates
    R u v huinj hvinj hdisj hcover hmodeu hmodev hRreg
  have hS : S.card = 24 := by simpa [S, U] using hpop.2.1
  have hNu : Nu.card = 8 := by
    simpa [Nu] using h305SameShoreNonantipodalTargetFinset_card_eight
      R u huinj hmodeu
  have hNv : Nv.card = 8 := by
    simpa [Nv] using h305SameShoreNonantipodalTargetFinset_card_eight
      R v hvinj hmodev
  have hNuSub : Nu ⊆ shoreTypeEdgeFinset R U 2 := by
    intro a ha
    exact (Finset.mem_sdiff.mp ha).1
  have hcomp : Uᶜ = W := h305_shoreImages_compl_eq u v hdisj hcover
  have hNvSub : Nv ⊆ shoreTypeEdgeFinset R U 0 := by
    intro a ha
    have haW : a ∈ shoreTypeEdgeFinset R W 2 :=
      (Finset.mem_sdiff.mp ha).1
    rw [shoreTypeEdgeFinset_zero_eq_two_compl R U, hcomp]
    exact haW
  have hSNu : Disjoint S Nu :=
    (shoreTypeEdgeFinset_disjoint_of_ne R U (by decide : 1 ≠ 2)).mono_right hNuSub
  have hSNv : Disjoint S Nv :=
    (shoreTypeEdgeFinset_disjoint_of_ne R U (by decide : 1 ≠ 0)).mono_right hNvSub
  have hNuNv : Disjoint Nu Nv :=
    (shoreTypeEdgeFinset_disjoint_of_ne R U (by decide : 2 ≠ 0)).mono
      hNuSub hNvSub
  have hUnionNv : Disjoint (S ∪ Nu) Nv := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rcases Finset.mem_union.mp ha with haS | haNu
    · exact Finset.disjoint_left.mp hSNv haS hb
    · exact Finset.disjoint_left.mp hNuNv haNu hb
  rw [Finset.card_union_of_disjoint hUnionNv,
    Finset.card_union_of_disjoint hSNu, hS, hNu, hNv]

/-- The actual 24+8+8 population forces global cubic histogram excess at
least `160`. -/
theorem h305_sum_cubicRowHistogramExcess_ge_160_of_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hcard : Fintype.card R.edgeFinset = 48)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (A B : H.ConnectedComponent) (hAB : A ≠ B)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hurange : Set.range u = A.supp) (hvrange : Set.range v = B.supp)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v) :
    160 ≤ ∑ a : R.edgeFinset, cubicRowHistogramExcess Cedge a := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let S := shoreTypeEdgeFinset R U 1
  let Nu := h305SameShoreNonantipodalTargetFinset R u hmodeu
  let Nv := h305SameShoreNonantipodalTargetFinset R v hmodev
  let N := S ∪ Nu ∪ Nv
  apply sum_cubicRowHistogramExcess_ge_160_of_forty_good Cedge hfree hCreg N
  · simpa [N, S, Nu, Nv, U] using
      h305_cubicStructuralGoodTargetFinset_card_forty
        R u v huinj hvinj hdisj hcover hmodeu hmodev hRreg
  · intro a ha
    rcases Finset.mem_union.mp ha with haSN | haNv
    · rcases Finset.mem_union.mp haSN with haS | haNu
      · obtain ⟨i, j, haij⟩ :=
          shoreTypeOneEdge_exists_crossCoordinates R u v hcover a haS
        apply cubicRowHistogramExcess_ge_four_of_residual_squareMass_ge_550
          R Cedge hfree hcard hCreg a
        exact h305_cross_cubicResidualEdge_squareMass_ge_550_of_components
          H R Cedge hservice hfree hHreg hRreg hCreg A B hAB u v
            huinj hvinj hurange hvrange hu hv hdisj hcover a i j haij
      · obtain ⟨i, j, haij, ho⟩ :=
          h305SameShoreNonantipodalTarget_exists_oddCoordinates
            R u huinj hmodeu a haNu
        exact h305_sameShore_nonantipodal_cubicRowHistogramExcess_ge_four_of_components
          H R Cedge hservice hfree hcard hHreg hRreg hCreg A B hAB u v
            huinj hvinj hurange hvrange hu hv hdisj hcover a i j ho haij
    · obtain ⟨i, j, haij, ho⟩ :=
        h305SameShoreNonantipodalTarget_exists_oddCoordinates
          R v hvinj hmodev a haNv
      have hd : ∀ k l, v k ≠ u l := fun k l h ↦ hdisj l k h.symm
      have hc : ∀ x : V, (∃ k, x = v k) ∨ ∃ l, x = u l := by
        intro x
        rcases hcover x with h | h
        · exact Or.inr h
        · exact Or.inl h
      exact h305_sameShore_nonantipodal_cubicRowHistogramExcess_ge_four_of_components
        H R Cedge hservice hfree hcard hHreg hRreg hCreg B A hAB.symm v u
          hvinj huinj hvrange hurange hv hu hd hc a i j ho haij

end


end Erdos85

#print axioms Erdos85.h305_cubicStructuralGoodTargetFinset_card_forty
#print axioms Erdos85.h305_sum_cubicRowHistogramExcess_ge_160_of_components

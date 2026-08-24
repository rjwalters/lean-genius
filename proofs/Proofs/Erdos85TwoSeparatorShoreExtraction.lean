import Proofs.Erdos85DisconnectedShorePartition

/-!
# Extracting ambient shores from a deleted separator

The canonical shore partition of the induced graph on `univ \ W` lifts to
two ambient shores separated by `W`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If deleting `W` leaves a non-preconnected induced graph, the remaining
vertices split into two nonempty ambient shores with no edge between them. -/
theorem exists_ambient_shores_of_induce_sdiff_not_preconnected
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hnot : ¬ (D.induce (↑(Finset.univ \ W) : Set V)).Preconnected) :
    ∃ S T : Finset V,
      S.Nonempty ∧ T.Nonempty ∧
      S ∪ T ∪ W = Finset.univ ∧ Disjoint S T ∧
      (∀ s ∈ S, ∀ t ∈ T, ¬ D.Adj s t) := by
  let U : Finset V := Finset.univ \ W
  let H := D.induce (↑U : Set V)
  obtain ⟨S₀, T₀, hS₀ne, hT₀ne, hcover₀, hdisj₀, hno₀⟩ :=
    exists_nonempty_anticomplete_partition_of_not_preconnected H
      (by simpa [H, U] using hnot)
  let S : Finset V := S₀.image Subtype.val
  let T : Finset V := T₀.image Subtype.val
  have hSne : S.Nonempty := hS₀ne.image _
  have hTne : T.Nonempty := hT₀ne.image _
  have hcover : S ∪ T ∪ W = Finset.univ := by
    ext z
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hzW : z ∈ W
    · exact Or.inr hzW
    · have hzU : z ∈ U := by simp [U, hzW]
      let a : {z : V // z ∈ (↑U : Set V)} := ⟨z, hzU⟩
      have ha : a ∈ S₀ ∨ a ∈ T₀ := by
        have : a ∈ S₀ ∪ T₀ := by rw [hcover₀]; simp
        exact Finset.mem_union.mp this
      rcases ha with haS | haT
      · exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨a, haS, rfl⟩))
      · exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨a, haT, rfl⟩))
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    obtain ⟨a, haS, haz⟩ := Finset.mem_image.mp hzS
    obtain ⟨b, hbT, hbz⟩ := Finset.mem_image.mp hzT
    have hab : a = b := Subtype.ext (haz.trans hbz.symm)
    subst b
    exact Finset.disjoint_left.mp hdisj₀ haS hbT
  have hno : ∀ s ∈ S, ∀ t ∈ T, ¬ D.Adj s t := by
    intro s hs t ht hst
    obtain ⟨a, haS, has⟩ := Finset.mem_image.mp hs
    obtain ⟨b, hbT, hbt⟩ := Finset.mem_image.mp ht
    have hab : H.Adj a b := by
      change D.Adj a.1 b.1
      simpa [has, hbt] using hst
    exact hno₀ a haS b hbT hab
  exact ⟨S, T, hSne, hTne, hcover, hdisj, hno⟩

end

end Erdos85

#print axioms Erdos85.exists_ambient_shores_of_induce_sdiff_not_preconnected

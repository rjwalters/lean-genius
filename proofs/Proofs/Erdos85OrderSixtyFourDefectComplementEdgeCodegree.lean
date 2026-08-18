import Proofs.Erdos85OrderSixtyFourDefectComponentEquitable

/-! # Complement codegree on a regular sixteen-vertex defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For adjacent vertices of a seven-regular graph on sixteen vertices, the
number of common neighbors in the complement is two plus their original
common-neighbor count.  This is the local arithmetic behind the source part
of the fourth cross-root transition factor. -/
theorem sevenRegular_sixteen_compl_commonNeighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ z, D.degree z = 7)
    {x y : V} (hxy : D.Adj x y) :
    ((Dᶜ).neighborFinset x ∩ (Dᶜ).neighborFinset y).card =
      2 + (D.neighborFinset x ∩ D.neighborFinset y).card := by
  classical
  let U := ((Finset.univ : Finset V).erase x).erase y
  let A := (D.neighborFinset x).erase y
  let B := (D.neighborFinset y).erase x
  have hne : x ≠ y := D.ne_of_adj hxy
  have hxcard : (D.neighborFinset x).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg x]
  have hycard : (D.neighborFinset y).card = 7 := by
    rw [D.card_neighborFinset_eq_degree, hreg y]
  have hyNx : y ∈ D.neighborFinset x := (D.mem_neighborFinset x y).mpr hxy
  have hxNy : x ∈ D.neighborFinset y :=
    (D.mem_neighborFinset y x).mpr hxy.symm
  have hAcard : A.card = 6 := by
    dsimp [A]
    rw [Finset.card_erase_of_mem hyNx, hxcard]
  have hBcard : B.card = 6 := by
    dsimp [B]
    rw [Finset.card_erase_of_mem hxNy, hycard]
  have hUcard : U.card = 14 := by
    dsimp [U]
    rw [Finset.card_erase_of_mem
      (Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ y⟩)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ,
      hcard]
  have hAB : A ∩ B = D.neighborFinset x ∩ D.neighborFinset y := by
    ext z
    simp only [A, B, Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, hzx⟩, _, hzy⟩
      exact ⟨hzx, hzy⟩
    · rintro ⟨hzx, hzy⟩
      refine ⟨⟨?_, hzx⟩, ?_, hzy⟩
      · intro hzyEq
        subst z
        exact D.loopless.irrefl y ((D.mem_neighborFinset y y).mp hzy)
      · intro hzxEq
        subst z
        exact D.loopless.irrefl x ((D.mem_neighborFinset x x).mp hzx)
  have hUnionCard : (A ∪ B).card =
      12 - (D.neighborFinset x ∩ D.neighborFinset y).card := by
    rw [Finset.card_union, hAcard, hBcard, hAB]
  have hsub : A ∪ B ⊆ U := by
    intro z hz
    have hz' := Finset.mem_union.mp hz
    apply Finset.mem_erase.mpr
    apply And.intro
    · intro hzyEq
      subst z
      rcases hz' with hzA | hzB
      · exact (Finset.mem_erase.mp hzA).1 rfl
      · exact D.loopless.irrefl y
          ((D.mem_neighborFinset y y).mp (Finset.mem_erase.mp hzB).2)
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ z⟩
    intro hzxEq
    subst z
    rcases hz' with hzA | hzB
    · exact D.loopless.irrefl x
        ((D.mem_neighborFinset x x).mp (Finset.mem_erase.mp hzA).2)
    · exact (Finset.mem_erase.mp hzB).1 rfl
  have hComplEq :
      (Dᶜ).neighborFinset x ∩ (Dᶜ).neighborFinset y = U \ (A ∪ B) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_union]
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj]
    simp only [U, A, B, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor <;> aesop
  rw [hComplEq, Finset.card_sdiff_of_subset hsub, hUcard, hUnionCard]
  have hle : (D.neighborFinset x ∩ D.neighborFinset y).card ≤ 6 := by
    have hs : D.neighborFinset x ∩ D.neighborFinset y ⊆ A := by
      rw [← hAB]
      exact Finset.inter_subset_left
    have := Finset.card_le_card hs
    rw [hAcard] at this
    exact this
  omega

end

end Erdos85

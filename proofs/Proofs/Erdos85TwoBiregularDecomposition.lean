import Proofs.HallsTheoremOQ01OQ03

/-! # Decomposing a two-biregular incidence structure -/

namespace Erdos85

open Finset
open HallsTheoremOQ01OQ03

/-- Every finite two-biregular incidence structure is the disjoint union of
two perfect matchings. -/
theorem exists_two_disjoint_equiv_of_two_biregular
    {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq ι] [DecidableEq α]
    (t : ι → Finset α) (h : IsBiregular t 2) :
    ∃ f g : ι ≃ α,
      (∀ i, f i ∈ t i) ∧ (∀ i, g i ∈ t i) ∧ ∀ i, f i ≠ g i := by
  obtain ⟨f, hfbij, hfmem⟩ :=
    exists_perfect_matching_of_regular h (by omega : 1 ≤ 2)
  let F : ι ≃ α := Equiv.ofBijective f hfbij
  let t' : ι → Finset α := fun i => (t i).erase (F i)
  have ht' : IsBiregular t' 1 := by
    constructor
    · intro i
      have hFi : F i ∈ t i := hfmem i
      change ((t i).erase (F i)).card = 1
      rw [Finset.card_erase_of_mem hFi, h.left]
    · intro a
      let i₀ : ι := F.symm a
      have hi₀ : i₀ ∈ (Finset.univ.filter fun i => a ∈ t i) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        have hFa : F i₀ = a := by simp [i₀]
        rw [← hFa]
        exact hfmem i₀
      have heq :
          (Finset.univ.filter fun i => a ∈ t' i) =
            (Finset.univ.filter fun i => a ∈ t i).erase i₀ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_erase, t']
        have hne : a ≠ F i ↔ i ≠ i₀ := by
          constructor
          · intro h hi
            apply h
            rw [hi]
            exact (F.apply_symm_apply a).symm
          · intro h hai
            apply h
            apply F.injective
            calc
              F i = a := hai.symm
              _ = F i₀ := (F.apply_symm_apply a).symm
        rw [hne]
      rw [heq, Finset.card_erase_of_mem hi₀, h.right]
  obtain ⟨g, hgbij, hgmem⟩ :=
    exists_perfect_matching_of_regular ht' (by omega : 1 ≤ 1)
  let H : ι ≃ α := Equiv.ofBijective g hgbij
  refine ⟨F, H, ?_, ?_, ?_⟩
  · exact hfmem
  · intro i
    exact (Finset.mem_erase.mp (hgmem i)).2
  · intro i
    exact (Finset.mem_erase.mp (hgmem i)).1.symm

end Erdos85

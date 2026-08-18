import Proofs.Erdos85DegreeTwoRepeatedForkSaturation

/-! # Three equal rows are impossible in a two-regular graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A two-regular simple graph cannot contain three distinct vertices with
the same neighborhood row: any neighbor in the common row would itself have
at least those three neighbors. -/
theorem degreeTwo_no_three_distinct_equal_neighborFinsets
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v = 2)
    {x y z : V} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxyRows : H.neighborFinset x = H.neighborFinset y)
    (hxzRows : H.neighborFinset x = H.neighborFinset z) : False := by
  have hNxCard : (H.neighborFinset x).card = 2 := by
    rw [H.card_neighborFinset_eq_degree, hdeg x]
  obtain ⟨r, hrx⟩ := Finset.card_pos.mp
    (show 0 < (H.neighborFinset x).card by omega)
  have hry : r ∈ H.neighborFinset y := by
    rw [← hxyRows]
    exact hrx
  have hrz : r ∈ H.neighborFinset z := by
    rw [← hxzRows]
    exact hrx
  have hsub : ({x, y, z} : Finset V) ⊆ H.neighborFinset r := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with hu | hu | hu
    · subst u
      exact (H.mem_neighborFinset r x).mpr
        ((H.mem_neighborFinset x r).mp hrx).symm
    · subst u
      exact (H.mem_neighborFinset r y).mpr
        ((H.mem_neighborFinset y r).mp hry).symm
    · subst u
      exact (H.mem_neighborFinset r z).mpr
        ((H.mem_neighborFinset z r).mp hrz).symm
  have hle := Finset.card_le_card hsub
  have hthree : ({x, y, z} : Finset V).card = 3 := by
    simp [hxy, hxz, hyz]
  rw [hthree, H.card_neighborFinset_eq_degree, hdeg r] at hle
  omega

/-- Two repeated forks of the same two-regular color, sharing one root and
having three distinct roots overall, are impossible.  Each fork equates its
two root rows, producing the forbidden triple of equal rows. -/
theorem degreeTwo_no_two_repeatedForks_with_shared_root
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ v, H.degree v = 2)
    {x y z a₁ a₂ b₁ b₂ : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ha : a₁ ≠ a₂)
    (hxa₁ : H.Adj x a₁) (hya₁ : H.Adj y a₁)
    (hxa₂ : H.Adj x a₂) (hya₂ : H.Adj y a₂)
    (hb : b₁ ≠ b₂)
    (hyb₁ : H.Adj y b₁) (hzb₁ : H.Adj z b₁)
    (hyb₂ : H.Adj y b₂) (hzb₂ : H.Adj z b₂) : False := by
  have hxyRows := degreeTwo_repeatedFork_neighborFinset_eq
    H hdeg ha hxa₁ hya₁ hxa₂ hya₂
  have hyzRows := degreeTwo_repeatedFork_neighborFinset_eq
    H hdeg hb hyb₁ hzb₁ hyb₂ hzb₂
  exact degreeTwo_no_three_distinct_equal_neighborFinsets
    H hdeg hxy hxz hyz hxyRows (hxyRows.trans hyzRows)

end

end Erdos85

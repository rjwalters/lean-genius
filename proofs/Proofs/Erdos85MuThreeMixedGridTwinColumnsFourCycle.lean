import Proofs.Erdos85MuThreeMixedGridForeignRowTransportSaturation

/-!
# Twin H-columns force an H four-cycle

In a two-regular bipartite relation, two distinct columns with identical
neighborhoods are the opposite column vertices of an isolated `K₂,₂`
component.  This identifies the saturated transport regime with an actual
four-cycle of `H`.
-/

open SimpleGraph

namespace Erdos85

/-- Distinct twin H-columns have exactly two common rows, and those rows have
exactly the twin columns as their H-neighborhoods. -/
theorem MuThreeMixedGridCode.twinColumns_H_fourCycle
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {b b' : Y} (hbb' : b ≠ b') (htwin : ∀ x, H x b ↔ H x b') :
    ∃ x z : X, x ≠ z ∧
      ((Finset.univ : Finset X).filter fun q => H q b) = {x, z} ∧
      ((Finset.univ : Finset X).filter fun q => H q b') = {x, z} ∧
      ((Finset.univ : Finset Y).filter fun y => H x y) = {b, b'} ∧
      ((Finset.univ : Finset Y).filter fun y => H z y) = {b, b'} := by
  let Sb := (Finset.univ : Finset X).filter fun q => H q b
  have hSbCard : Sb.card = 2 := code.H_twoRegular.2 b
  obtain ⟨x, z, hxz, hSb⟩ := Finset.card_eq_two.mp hSbCard
  have hxSb : x ∈ Sb := by rw [hSb]; simp
  have hzSb : z ∈ Sb := by rw [hSb]; simp
  have hxb : H x b := (Finset.mem_filter.mp hxSb).2
  have hzb : H z b := (Finset.mem_filter.mp hzSb).2
  have hxb' : H x b' := (htwin x).mp hxb
  have hzb' : H z b' := (htwin z).mp hzb
  have hSb' : ((Finset.univ : Finset X).filter fun q => H q b') = {x, z} := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [← htwin q]
    simpa [Sb] using congrArg (fun S : Finset X => q ∈ S) hSb
  have hxRow : ((Finset.univ : Finset Y).filter fun y => H x y) = {b, b'} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with rfl | rfl
      · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb⟩)
      · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxb'⟩)
    · rw [code.H_twoRegular.1 x]
      simp [hbb']
  have hzRow : ((Finset.univ : Finset Y).filter fun y => H z y) = {b, b'} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with rfl | rfl
      · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzb⟩)
      · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzb'⟩)
    · rw [code.H_twoRegular.1 z]
      simp [hbb']
  exact ⟨x, z, hxz, hSb, hSb', hxRow, hzRow⟩

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.twinColumns_H_fourCycle

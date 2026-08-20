import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations

/-! # Coordinates for every shore-type-one exterior edge -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A two-point finset meeting `U` in exactly one point consists of one point
of `U` and one point outside `U`. -/
theorem twoPointFinset_eq_pair_of_inter_card_one
    {α : Type*} [DecidableEq α]
    (E U : Finset α) (hE : E.card = 2)
    (hinter : (E ∩ U).card = 1) :
    ∃ x y, x ∈ U ∧ y ∉ U ∧ E = {x, y} := by
  have hdiffCard : (E \ U).card = 1 := by
    have hsplit := Finset.card_inter_add_card_sdiff E U
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hinter
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hdiffCard
  have hxmem : x ∈ U := by
    have : x ∈ E ∩ U := by rw [hx]; simp
    exact Finset.mem_inter.mp this |>.2
  have hymem : y ∉ U := by
    have : y ∈ E \ U := by rw [hy]; simp
    exact Finset.mem_sdiff.mp this |>.2
  refine ⟨x, y, hxmem, hymem, ?_⟩
  ext z
  constructor
  · intro hz
    by_cases hzU : z ∈ U
    · have hz' : z ∈ E ∩ U := Finset.mem_inter.mpr ⟨hz, hzU⟩
      rw [hx] at hz'
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hz'))
    · have hz' : z ∈ E \ U := Finset.mem_sdiff.mpr ⟨hz, hzU⟩
      rw [hy] at hz'
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr (Finset.mem_singleton.mp hz')))
  · intro hz
    rcases Finset.mem_insert.mp hz with hzx | hz
    · subst z
      have : x ∈ E ∩ U := by rw [hx]; simp
      exact Finset.mem_inter.mp this |>.1
    · have hzy : z = y := Finset.mem_singleton.mp hz
      subst z
      have : y ∈ E \ U := by rw [hy]; simp
      exact Finset.mem_sdiff.mp this |>.1

/-- Every h305 shore-type-one edge has a unique-shore coordinate support
`{u i, v j}` (existence only; injectivity later supplies uniqueness). -/
theorem shoreTypeOneEdge_exists_crossCoordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (a : R.edgeFinset)
    (ha : a ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1) :
    ∃ i j : ZMod 8, a.1.toFinset = {u i, v j} := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  have hinter : (a.1.toFinset ∩ U).card = 1 :=
    (Finset.mem_filter.mp ha).2
  obtain ⟨x, y, hxU, hyU, hxy⟩ :=
    twoPointFinset_eq_pair_of_inter_card_one a.1.toFinset U
      (R.card_toFinset_mem_edgeFinset a) hinter
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxU
  rcases hcover y with ⟨k, hyk⟩ | ⟨j, hyj⟩
  · subst y
    exact False.elim (hyU (Finset.mem_image.mpr
      ⟨k, Finset.mem_univ _, rfl⟩))
  · subst y
    exact ⟨i, j, hxy⟩

end

end Erdos85

#print axioms Erdos85.twoPointFinset_eq_pair_of_inter_card_one
#print axioms Erdos85.shoreTypeOneEdge_exists_crossCoordinates

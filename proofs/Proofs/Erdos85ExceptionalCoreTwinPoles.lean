import Proofs.Erdos85DefectTwinPoleFixedVector

/-!
# Exceptional-core census produces twin poles

This is the exact consumer of the Baer census
`N_D(E_i)=F ∪ (E \ {E_i})`.  Any two distinct empty centers in `E` are
adjacent and have identical neighborhoods away from themselves.
-/

open SimpleGraph

namespace Erdos85

/-- Two vertices satisfying the exceptional-core neighborhood census are
adjacent off-pole twins. -/
theorem adjacent_twins_of_exceptionalCore_neighbor_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (full empty : Finset V) (pole₁ pole₂ : V)
    (hpole₂ : pole₂ ∈ empty)
    (hpoles : pole₁ ≠ pole₂)
    (hN₁ : D.neighborFinset pole₁ = full ∪ empty.erase pole₁)
    (hN₂ : D.neighborFinset pole₂ = full ∪ empty.erase pole₂) :
    D.Adj pole₁ pole₂ ∧
      ∀ v, v ≠ pole₁ → v ≠ pole₂ →
        (D.Adj v pole₁ ↔ D.Adj v pole₂) := by
  have hpole₂N₁ : pole₂ ∈ D.neighborFinset pole₁ := by
    rw [hN₁]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hpoles.symm, hpole₂⟩)
  have hadj : D.Adj pole₁ pole₂ :=
    (D.mem_neighborFinset pole₁ pole₂).mp hpole₂N₁
  refine ⟨hadj, ?_⟩
  intro v hv₁ hv₂
  have hm₁ : v ∈ D.neighborFinset pole₁ ↔
      v ∈ full ∨ (v ≠ pole₁ ∧ v ∈ empty) := by
    rw [hN₁]
    simp only [Finset.mem_union, Finset.mem_erase]
  have hm₂ : v ∈ D.neighborFinset pole₂ ↔
      v ∈ full ∨ (v ≠ pole₂ ∧ v ∈ empty) := by
    rw [hN₂]
    simp only [Finset.mem_union, Finset.mem_erase]
  have hmem : v ∈ D.neighborFinset pole₁ ↔
      v ∈ D.neighborFinset pole₂ := by
    rw [hm₁, hm₂]
    tauto
  simpa only [D.mem_neighborFinset, D.adj_comm] using hmem

/-- The exceptional-core census fixes the binary pair indicator. -/
theorem adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (full empty : Finset V) (pole₁ pole₂ : V)
    (hpole₂ : pole₂ ∈ empty)
    (hpoles : pole₁ ≠ pole₂)
    (hN₁ : D.neighborFinset pole₁ = full ∪ empty.erase pole₁)
    (hN₂ : D.neighborFinset pole₂ = full ∪ empty.erase pole₂) :
    (D.adjMatrix (ZMod 2)).mulVec
        (Pi.single pole₁ 1 + Pi.single pole₂ 1) =
      Pi.single pole₁ 1 + Pi.single pole₂ 1 := by
  rcases adjacent_twins_of_exceptionalCore_neighbor_census
    D full empty pole₁ pole₂ hpole₂ hpoles hN₁ hN₂ with
    ⟨hadj, htwin⟩
  exact adjMatrix_mulVec_twoCoordinate_eq_self_of_adjacent_twins
    D pole₁ pole₂ hpoles hadj htwin

end Erdos85

#print axioms Erdos85.adjacent_twins_of_exceptionalCore_neighbor_census
#print axioms Erdos85.adjMatrix_mulVec_twoCoordinate_eq_self_of_exceptionalCore_census

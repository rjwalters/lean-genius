import Proofs.Erdos85C4FreeRegularCommonSupport
import Proofs.Erdos85MuNegThreeZeroFiveAntipodalTwoWalkTypeMass

/-! # Antipodal common-target shore-type balance -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Number of off-diagonal common-service targets of a fixed shore type. -/
def offDiagonalCommonShoreTypeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (S : Finset V) (t : ℕ) : ℕ :=
  ((offDiagonalCommonNeighborSupport Cedge a).filter fun b ↦
    (b.1.toFinset ∩ S).card = t).card

private theorem partition_and_mass_of_le_two
    {α : Type*} [DecidableEq α] (T : Finset α) (q : α → ℕ)
    (hle : ∀ a ∈ T, q a ≤ 2) :
    let n := fun t ↦ (T.filter fun a ↦ q a = t).card
    n 0 + n 1 + n 2 = T.card ∧
      (∑ a ∈ T, q a) = 2 * n 2 + n 1 := by
  classical
  dsimp only
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      have hi := ih (fun b hb ↦ hle b (Finset.mem_insert_of_mem hb))
      have hqa := hle a (Finset.mem_insert_self a T)
      interval_cases htag : q a <;>
        simp [Finset.filter_insert, ha, htag, hi.2] <;> omega

private theorem edgeType_partition_and_mass
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (T : Finset R.edgeFinset) (S : Finset V) :
    let n := fun t ↦ (T.filter fun b ↦
      (b.1.toFinset ∩ S).card = t).card
    n 0 + n 1 + n 2 = T.card ∧
      (∑ b ∈ T, (b.1.toFinset ∩ S).card) = 2 * n 2 + n 1 := by
  apply partition_and_mass_of_le_two
  intro a _
  calc
    _ ≤ a.1.toFinset.card := Finset.card_le_card Finset.inter_subset_left
    _ = 2 := R.card_toFinset_mem_edgeFinset a

/-- For an antipodal type-two central edge, its thirty off-diagonal
common-service targets contain exactly two more type-zero than type-two
edges. -/
theorem h305_antipodal_offDiagonalCommon_typeZero_eq_typeTwo_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j : ZMod 8)
    (hoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j}) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    offDiagonalCommonShoreTypeCount R Cedge a U 0 =
      offDiagonalCommonShoreTypeCount R Cedge a U 2 + 2 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let T := offDiagonalCommonNeighborSupport Cedge a
  let n := fun t ↦ (T.filter fun b ↦
    (b.1.toFinset ∩ U).card = t).card
  change n 0 = n 2 + 2
  have hcard : T.card = 30 := by
    have h := offDiagonalCommonNeighborSupport_card_of_regular_not_containsC4
      Cedge hfree 6 hCreg a
    norm_num at h
    exact h
  have haWeight : (a.1.toFinset ∩ U).card = 2 := by
    have hsub : a.1.toFinset ⊆ U := by
      intro x hx
      rw [ha] at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      · exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    rw [Finset.inter_eq_left.mpr hsub,
      R.card_toFinset_mem_edgeFinset a]
  have hfull := h305_antipodal_endpointWeighted_common_sum_eq_forty
    H R Cedge hservice hHreg hCreg u huinj hu a i j hoffset ha
  have hweighted := sum_commonNeighbor_card_mul_weight_eq_diag_add_support
    Cedge hfree 6 hCreg a (fun b ↦ (b.1.toFinset ∩ U).card)
  have hmass : (∑ b ∈ T, (b.1.toFinset ∩ U).card) = 28 := by
    change (∑ b ∈ offDiagonalCommonNeighborSupport Cedge a,
      (b.1.toFinset ∩ U).card) = 28
    rw [hfull] at hweighted
    rw [haWeight] at hweighted
    omega
  have hp := edgeType_partition_and_mass R T U
  change n 0 + n 1 + n 2 = T.card ∧
    (∑ b ∈ T, (b.1.toFinset ∩ U).card) = 2 * n 2 + n 1 at hp
  omega

end

end Erdos85

#print axioms
  Erdos85.h305_antipodal_offDiagonalCommon_typeZero_eq_typeTwo_add_two

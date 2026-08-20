import Proofs.Erdos85EdgeIndexedServiceCubicCensus
import Proofs.Erdos85EdgeIndexedServiceTypeHandshake

/-! # Shore-type decomposition of cubic service mass -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def serviceCubicWalkCount
    {V : Type*} [Fintype V] [DecidableEq V]
    {R : SimpleGraph V} [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (b a : R.edgeFinset) : ℕ :=
  Fintype.card {p : Cedge.Walk b a | p.length = 3}

def shoreTypeCubicWalkMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (t : ℕ) (a : R.edgeFinset) : ℕ :=
  ∑ b ∈ shoreTypeEdgeFinset R S t, serviceCubicWalkCount Cedge b a

/-- Summing incident cubic mass over a shore weights each exterior edge by
its number of endpoints in that shore. -/
theorem sum_incidentServiceCubicWalkMass_eq_endpointWeighted
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (a : R.edgeFinset) :
    (∑ u ∈ S, incidentServiceCubicWalkMass R Cedge u a) =
      ∑ b : R.edgeFinset,
        serviceCubicWalkCount Cedge b a * (b.1.toFinset ∩ S).card := by
  classical
  unfold incidentServiceCubicWalkMass serviceCubicWalkCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  let c := Fintype.card {p : Cedge.Walk b a | p.length = 3}
  calc
    (∑ u ∈ S, if u ∈ b.1.toFinset then c else 0) =
        ∑ _u ∈ S.filter (· ∈ b.1.toFinset), c := by
          rw [Finset.sum_filter]
    _ = c * (b.1.toFinset ∩ S).card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have heq : S.filter (· ∈ b.1.toFinset) = b.1.toFinset ∩ S := by
        ext u
        simp [and_comm]
      rw [heq, mul_comm]
      simp

private theorem weighted_sum_eq_two_bin_add_one_bin
    {α : Type*} [DecidableEq α] (T : Finset α)
    (f q : α → ℕ) (hle : ∀ a ∈ T, q a ≤ 2) :
    (∑ a ∈ T, f a * q a) =
      2 * (∑ a ∈ T.filter fun a => q a = 2, f a) +
        ∑ a ∈ T.filter fun a => q a = 1, f a := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      have hi := ih (fun b hb => hle b (Finset.mem_insert_of_mem hb))
      have hqa := hle a (Finset.mem_insert_self a T)
      interval_cases htag : q a <;>
        simp [Finset.filter_insert, ha, htag, hi] <;> omega

/-- Endpoint weighting is exactly twice the type-two cubic mass plus the
type-one cubic mass. -/
theorem sum_incidentServiceCubicWalkMass_eq_two_typeTwo_add_typeOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (a : R.edgeFinset) :
    (∑ u ∈ S, incidentServiceCubicWalkMass R Cedge u a) =
      2 * shoreTypeCubicWalkMass R Cedge S 2 a +
        shoreTypeCubicWalkMass R Cedge S 1 a := by
  rw [sum_incidentServiceCubicWalkMass_eq_endpointWeighted]
  let q : R.edgeFinset → ℕ := fun b => (b.1.toFinset ∩ S).card
  let f : R.edgeFinset → ℕ := fun b => serviceCubicWalkCount Cedge b a
  have hle : ∀ b ∈ (Finset.univ : Finset R.edgeFinset), q b ≤ 2 := by
    intro b _
    calc
      q b ≤ b.1.toFinset.card := Finset.card_le_card Finset.inter_subset_left
      _ = 2 := R.card_toFinset_mem_edgeFinset b
  have h := weighted_sum_eq_two_bin_add_one_bin
    (Finset.univ : Finset R.edgeFinset) f q hle
  simpa [q, f, shoreTypeCubicWalkMass, shoreTypeEdgeFinset] using h

/-- Comparing a shore and its complement eliminates the type-one mass.  This
is the abstract arithmetic form behind the h305 identity
`S₀ - S₂ = 8(t-1)`. -/
theorem shoreTypeCubicWalkMass_balance_of_complement_sums
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (a : R.edgeFinset) (L M : ℕ)
    (hS : (∑ u ∈ S, incidentServiceCubicWalkMass R Cedge u a) = L)
    (hSc : (∑ u ∈ Sᶜ, incidentServiceCubicWalkMass R Cedge u a) = M) :
    2 * shoreTypeCubicWalkMass R Cedge S 0 a + L =
      M + 2 * shoreTypeCubicWalkMass R Cedge S 2 a := by
  classical
  have hzero : shoreTypeEdgeFinset R Sᶜ 2 =
      shoreTypeEdgeFinset R S 0 := by
    ext b
    simp only [shoreTypeEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    have hsplit := Finset.card_inter_add_card_sdiff b.1.toFinset S
    have hcomp : (b.1.toFinset ∩ Sᶜ).card =
        (b.1.toFinset \ S).card := by
      congr 1
      ext x
      simp
    have hedge := R.card_toFinset_mem_edgeFinset b
    rw [hcomp]
    omega
  have hone : shoreTypeEdgeFinset R Sᶜ 1 =
      shoreTypeEdgeFinset R S 1 := by
    ext b
    simp only [shoreTypeEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    have hsplit := Finset.card_inter_add_card_sdiff b.1.toFinset S
    have hcomp : (b.1.toFinset ∩ Sᶜ).card =
        (b.1.toFinset \ S).card := by
      congr 1
      ext x
      simp
    have hedge := R.card_toFinset_mem_edgeFinset b
    rw [hcomp]
    omega
  have hleft := sum_incidentServiceCubicWalkMass_eq_two_typeTwo_add_typeOne
    R Cedge S a
  have hright := sum_incidentServiceCubicWalkMass_eq_two_typeTwo_add_typeOne
    R Cedge Sᶜ a
  rw [hS] at hleft
  rw [hSc] at hright
  have hmassZero : shoreTypeCubicWalkMass R Cedge Sᶜ 2 a =
      shoreTypeCubicWalkMass R Cedge S 0 a := by
    simp only [shoreTypeCubicWalkMass, hzero]
  have hmassOne : shoreTypeCubicWalkMass R Cedge Sᶜ 1 a =
      shoreTypeCubicWalkMass R Cedge S 1 a := by
    simp only [shoreTypeCubicWalkMass, hone]
  rw [hmassZero, hmassOne] at hright
  omega

end

end Erdos85

#print axioms
  Erdos85.sum_incidentServiceCubicWalkMass_eq_endpointWeighted
#print axioms
  Erdos85.sum_incidentServiceCubicWalkMass_eq_two_typeTwo_add_typeOne
#print axioms
  Erdos85.shoreTypeCubicWalkMass_balance_of_complement_sums

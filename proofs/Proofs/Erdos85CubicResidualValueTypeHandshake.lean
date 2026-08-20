import Proofs.Erdos85CubicResidualFiberHistogram
import Proofs.Erdos85EdgeIndexedServiceTypeHandshake

/-! # Residual cubic-value handshake by shore type -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Residual service edges of shore type `t` whose cubic entry toward `a`
equals `q`. -/
def residualCubicValueShoreTypeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (t q : ℕ) (a : R.edgeFinset) : Finset R.edgeFinset :=
  (shoreTypeEdgeFinset R S t).filter fun b ↦
    ¬ Cedge.Adj b a ∧ residualFiberCubicWalkCount R Cedge a b = q

/-- Summing a residual histogram bin over a shore counts each marked edge
once for every endpoint it has in that shore. -/
theorem sum_cubicResidualFiberHistogram_eq_endpointWeighted
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (q : ℕ) (a : R.edgeFinset) :
    (∑ u ∈ S, cubicResidualFiberHistogram R Cedge u a q) =
      ∑ b ∈ (Finset.univ : Finset R.edgeFinset).filter (fun b ↦
          ¬ Cedge.Adj b a ∧
            residualFiberCubicWalkCount R Cedge a b = q),
        (b.1.toFinset ∩ S).card := by
  classical
  unfold cubicResidualFiberHistogram boundedHistogram cubicResidualFiber
    incidentEdgeFiber
  simp_rw [Finset.card_eq_sum_ones]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : ¬ Cedge.Adj b a ∧
      residualFiberCubicWalkCount R Cedge a b = q
  · simp [hb.1, hb.2]
    congr 1
    ext u
    simp [and_comm]
  · simp [hb]
    intro i _ _ hna hq
    exact hb ⟨hna, hq⟩

private theorem weighted_card_eq_two_bin_add_one_bin
    {α : Type*} [DecidableEq α] (T : Finset α) (w : α → ℕ)
    (hle : ∀ a ∈ T, w a ≤ 2) :
    (∑ a ∈ T, w a) =
      2 * (T.filter fun a ↦ w a = 2).card +
        (T.filter fun a ↦ w a = 1).card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      have hi := ih (fun b hb ↦ hle b (Finset.mem_insert_of_mem hb))
      have hwa := hle a (Finset.mem_insert_self a T)
      interval_cases htag : w a <;>
        simp [Finset.filter_insert, ha, htag, hi] <;> omega

/-- Residual cubic-value handshake: the sum of the `q` histogram bin over
one shore is twice the number of type-two marked edges plus the number of
type-one marked edges. -/
theorem sum_cubicResidualFiberHistogram_eq_two_typeTwo_add_typeOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (q : ℕ) (a : R.edgeFinset) :
    (∑ u ∈ S, cubicResidualFiberHistogram R Cedge u a q) =
      2 * (residualCubicValueShoreTypeFinset R Cedge S 2 q a).card +
        (residualCubicValueShoreTypeFinset R Cedge S 1 q a).card := by
  rw [sum_cubicResidualFiberHistogram_eq_endpointWeighted]
  let T : Finset R.edgeFinset := Finset.univ.filter fun b ↦
    ¬ Cedge.Adj b a ∧ residualFiberCubicWalkCount R Cedge a b = q
  let w : R.edgeFinset → ℕ := fun b ↦ (b.1.toFinset ∩ S).card
  have hle : ∀ b ∈ T, w b ≤ 2 := by
    intro b _
    calc
      w b ≤ b.1.toFinset.card := Finset.card_le_card Finset.inter_subset_left
      _ = 2 := R.card_toFinset_mem_edgeFinset b
  have h := weighted_card_eq_two_bin_add_one_bin T w hle
  have htwo : T.filter (fun b ↦ w b = 2) =
      residualCubicValueShoreTypeFinset R Cedge S 2 q a := by
    ext b
    simp only [T, w, residualCubicValueShoreTypeFinset,
      shoreTypeEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  have hone : T.filter (fun b ↦ w b = 1) =
      residualCubicValueShoreTypeFinset R Cedge S 1 q a := by
    ext b
    simp only [T, w, residualCubicValueShoreTypeFinset,
      shoreTypeEdgeFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  rw [htwo, hone] at h
  exact h

end

end Erdos85

#print axioms Erdos85.sum_cubicResidualFiberHistogram_eq_endpointWeighted
#print axioms
  Erdos85.sum_cubicResidualFiberHistogram_eq_two_typeTwo_add_typeOne

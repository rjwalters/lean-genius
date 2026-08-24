import Proofs.Erdos85EulerianCutParity
import Proofs.Erdos85WitnessLabelCharacterSwitchInvariant

/-!
# Residual witness character as a physical cross-witness cut

This is the graph-native handshake identity `(73rnz_cjibkzk)`.  The sum of
witness degree parities over the residual set is exactly the parity of the
witness-label cut.  Character one therefore produces an actual segment from
a residual witness to a non-residual witness.
-/

open SimpleGraph

namespace Erdos85

private theorem zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · left; rfl
  · right; rfl

/-- General F₂ handshake identity on a vertex subset. -/
theorem degreeParity_sum_eq_graphCutMass_cast
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj] (R : Finset V) :
    (∑ y ∈ R, (W.degree y : ZMod 2)) =
      (graphCutMass W R : ZMod 2) := by
  have hinternal := even_sum_internalNeighbor_card W R
  have hsplit :
      (∑ y ∈ R, W.degree y) =
        graphCutMass W R +
          ∑ y ∈ R, (W.neighborFinset y ∩ R).card := by
    simp only [graphCutMass, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    calc
      W.degree y = (W.neighborFinset y).card :=
        (W.card_neighborFinset_eq_degree y).symm
      _ = (W.neighborFinset y \ R).card +
          (W.neighborFinset y ∩ R).card :=
        (Finset.card_sdiff_add_card_inter _ _).symm
  have hcast := congrArg (fun n : ℕ => (n : ZMod 2)) hsplit
  push_cast at hcast
  have hi : ((∑ y ∈ R, (W.neighborFinset y ∩ R).card : ℕ) : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hinternal
  push_cast at hi
  rw [hi, add_zero] at hcast
  exact hcast

/-- Character one forces a concrete residual-to-nonresidual witness edge. -/
theorem exists_crossWitness_edge_of_degreeParity_sum_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj] (R : Finset V)
    (hchar : (∑ y ∈ R, (W.degree y : ZMod 2)) = 1) :
    ∃ y ∈ R, ∃ z ∉ R, W.Adj y z := by
  have hcut : (graphCutMass W R : ZMod 2) = 1 := by
    rw [← degreeParity_sum_eq_graphCutMass_cast W R]
    exact hchar
  by_contra hno
  push Not at hno
  have hzero : graphCutMass W R = 0 := by
    unfold graphCutMass
    apply Finset.sum_eq_zero
    intro y hy
    apply Finset.card_eq_zero.mpr
    ext z
    constructor
    · intro hz
      have hzParts := Finset.mem_sdiff.mp hz
      have hyz : W.Adj y z := by
        simpa [SimpleGraph.mem_neighborFinset] using hzParts.1
      exact (hno y hy z hzParts.2 hyz).elim
    · intro hz
      simp at hz
  rw [hzero] at hcut
  exact zero_ne_one hcut

/-- Dichotomy form used after the local-switch no-go: either the residual
character vanishes, or it is carried by an explicit cross-witness segment. -/
theorem residualCharacter_zero_or_exists_crossWitness_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (W : SimpleGraph V) [DecidableRel W.Adj] (R : Finset V) :
    (∑ y ∈ R, (W.degree y : ZMod 2)) = 0 ∨
      ∃ y ∈ R, ∃ z ∉ R, W.Adj y z := by
  have hbinary := zmod2_eq_zero_or_one
    (∑ y ∈ R, (W.degree y : ZMod 2))
  rcases hbinary with hz | hone
  · exact Or.inl hz
  · exact Or.inr (exists_crossWitness_edge_of_degreeParity_sum_eq_one
      W R hone)

end Erdos85

#print axioms Erdos85.degreeParity_sum_eq_graphCutMass_cast
#print axioms Erdos85.exists_crossWitness_edge_of_degreeParity_sum_eq_one
#print axioms Erdos85.residualCharacter_zero_or_exists_crossWitness_edge

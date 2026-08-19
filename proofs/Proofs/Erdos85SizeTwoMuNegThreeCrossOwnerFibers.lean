import Proofs.Erdos85SizeTwoMuNegThreeCrossOwnerCollisionNormalForm

/-! # Fibre bounds for `mu = -3` cross-pair owners -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A collision rule with three possible normalized target positions bounds
every owner fibre by three. The equivalence `b` allows the same lemma to
handle the identity, `sigma`, and `tau` matching indices. -/
theorem owner_fiber_card_le_three_of_collision_index
    {X W : Type*} [Fintype X] [DecidableEq X] [DecidableEq W]
    (σ τ b : Equiv.Perm X) (o : X → W)
    (hcollision : ∀ x x', o x = o x' →
      b x' = x ∨ b x' = σ x ∨ b x' = τ x)
    (x : X) :
    ((Finset.univ : Finset X).filter fun x' ↦ o x' = o x).card ≤ 3 := by
  let T : Finset X := {b.symm x, b.symm (σ x), b.symm (τ x)}
  have hsub : ((Finset.univ : Finset X).filter fun x' ↦ o x' = o x) ⊆ T := by
    intro x' hx'
    have ho : o x = o x' := (Finset.mem_filter.mp hx').2.symm
    rcases hcollision x x' ho with h | h | h
    · have : x' = b.symm x := by
        calc
          x' = b.symm (b x') := (b.symm_apply_apply x').symm
          _ = b.symm x := congrArg b.symm h
      simp [T, this]
    · have : x' = b.symm (σ x) := by
        calc
          x' = b.symm (b x') := (b.symm_apply_apply x').symm
          _ = b.symm (σ x) := congrArg b.symm h
      simp [T, this]
    · have : x' = b.symm (τ x) := by
        calc
          x' = b.symm (b x') := (b.symm_apply_apply x').symm
          _ = b.symm (τ x) := congrArg b.symm h
      simp [T, this]
  calc
    _ ≤ T.card := Finset.card_le_card hsub
    _ ≤ 3 := by
      dsimp [T]
      exact (Finset.card_insert_le _ _).trans <|
        (Nat.add_le_add_right (Finset.card_insert_le _ _) 1).trans <| by simp

/-- Each of the three concrete owner maps in the coherent normal form has
fibres of cardinality at most three. -/
theorem MuNegThreeCrossOwnerNormalForm.owner_fiber_cards_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s) :
    (∀ x, ((Finset.univ.filter fun x' ↦ N.o₀ x' = N.o₀ x)).card ≤ 3) ∧
    (∀ x, ((Finset.univ.filter fun x' ↦ N.oσ x' = N.oσ x)).card ≤ 3) ∧
    ∀ x, ((Finset.univ.filter fun x' ↦ N.oτ x' = N.oτ x)).card ≤ 3 := by
  let laws := N.diagonal_collision_laws G hfree c s
  constructor
  · intro x
    exact owner_fiber_card_le_three_of_collision_index
      N.σ N.τ (Equiv.refl _) N.o₀ laws.1 x
  constructor
  · intro x
    exact owner_fiber_card_le_three_of_collision_index
      N.σ N.τ N.σ N.oσ laws.2.1 x
  · intro x
    exact owner_fiber_card_le_three_of_collision_index
      N.σ N.τ N.τ N.oτ laws.2.2 x

end

end Erdos85

#print axioms Erdos85.owner_fiber_card_le_three_of_collision_index
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.owner_fiber_cards_le_three

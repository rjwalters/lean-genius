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

/-- Eight inputs and fibres of size at most three force at least three
distinct values in the image. -/
theorem image_card_ge_three_of_card_eight_of_fibers_le_three
    {X W : Type*} [Fintype X] [DecidableEq X] [DecidableEq W]
    (o : X → W) (hcard : Fintype.card X = 8)
    (hfiber : ∀ x,
      ((Finset.univ : Finset X).filter fun x' ↦ o x' = o x).card ≤ 3) :
    3 ≤ ((Finset.univ : Finset X).image o).card := by
  let I := (Finset.univ : Finset X).image o
  have hsum := Finset.card_eq_sum_card_image o (Finset.univ : Finset X)
  have hterm : ∀ w ∈ I,
      ((Finset.univ : Finset X).filter fun x ↦ o x = w).card ≤ 3 := by
    intro w hw
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hw
    exact hfiber x
  have hle : 8 ≤ I.card * 3 := by
    calc
      8 = (Finset.univ : Finset X).card := by simp [hcard]
      _ = ∑ w ∈ I, ((Finset.univ : Finset X).filter fun x ↦ o x = w).card :=
        hsum
      _ ≤ ∑ _w ∈ I, 3 := Finset.sum_le_sum fun w hw ↦ hterm w hw
      _ = I.card * 3 := by simp
  change 3 ≤ I.card
  omega

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

/-- On an eight-point positive shore, every normalized owner map uses at
least three distinct exterior vertices. -/
theorem MuNegThreeCrossOwnerNormalForm.owner_image_cards_ge_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s)
    (hshore : Fintype.card
      (MuNegThreePositiveShore (secondOrderDefectGraph G) c s) = 8) :
    3 ≤ (Finset.univ.image N.o₀).card ∧
    3 ≤ (Finset.univ.image N.oσ).card ∧
    3 ≤ (Finset.univ.image N.oτ).card := by
  have hfibers := N.owner_fiber_cards_le_three G hfree c s
  exact ⟨
    image_card_ge_three_of_card_eight_of_fibers_le_three N.o₀ hshore hfibers.1,
    image_card_ge_three_of_card_eight_of_fibers_le_three N.oσ hshore hfibers.2.1,
    image_card_ge_three_of_card_eight_of_fibers_le_three N.oτ hshore hfibers.2.2⟩

end

end Erdos85

#print axioms Erdos85.owner_fiber_card_le_three_of_collision_index
#print axioms Erdos85.image_card_ge_three_of_card_eight_of_fibers_le_three
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.owner_fiber_cards_le_three
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.owner_image_cards_ge_three

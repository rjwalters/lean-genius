import Proofs.Erdos85MuThreeMixedGridRookSector
import Proofs.Erdos85MuThreeMixedGridIndicatorAction

/-!
# Kernel of the occupied row/column incidence map

The complement of a two-regular relation on two eight-element shores is
connected in the precise linear-algebraic sense needed here: if coefficients
`aₓ`, `bᵧ` satisfy `aₓ + bᵧ = 0` on every occupied cell, then all `aₓ` are
one constant and all `bᵧ` its negative.  Thus the sixteen row/column
indicators have exactly their one obvious dependence, the rank-15 input for
the dimension-33 zero sector.
-/

open SimpleGraph

namespace Erdos85

/-- **Occupied-incidence kernel.**  The only rational potentials summing to
zero on every occupied cell are a constant on the left shore and its
negative on the right shore. -/
theorem MuThreeMixedGridCode.occupied_incidence_kernel
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a : X → ℚ) (b : Y → ℚ)
    (hzero : ∀ x y, ¬ K x y → a x + b y = 0) :
    (∀ x x', a x = a x') ∧
      (∀ y y', b y = b y') ∧
      (∀ x y, a x = -b y) := by
  have hrow : ∀ x x', a x = a x' := by
    intro x x'
    obtain ⟨y, hxy, hx'y⟩ := code.exists_common_occupied_column H K C x x'
    have h1 := hzero x y hxy
    have h2 := hzero x' y hx'y
    linarith
  have hcol : ∀ y y', b y = b y' := by
    intro y y'
    obtain ⟨x, hxy, hxy'⟩ := code.exists_common_occupied_row H K C y y'
    have h1 := hzero x y hxy
    have h2 := hzero x y' hxy'
    linarith
  refine ⟨hrow, hcol, ?_⟩
  intro x y
  obtain ⟨y', hxy', _⟩ := code.exists_common_occupied_column H K C x x
  have h := hzero x y' hxy'
  have hyy' := hcol y y'
  linarith

/-- A rational linear combination of all row and column indicators vanishes
only for the constant/opposite coefficient relation. -/
theorem MuThreeMixedGridCode.indicator_combination_eq_zero
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a : X → ℚ) (b : Y → ℚ)
    (hzero : ∀ u : muThreeMixedCell K,
      (∑ x, a x * if u.1.1 = x then 1 else 0) +
        (∑ y, b y * if u.1.2 = y then 1 else 0) = 0) :
    (∀ x x', a x = a x') ∧
      (∀ y y', b y = b y') ∧
      (∀ x y, a x = -b y) := by
  apply code.occupied_incidence_kernel H K C a b
  intro x y hxy
  let u : muThreeMixedCell K := ⟨(x, y), hxy⟩
  have hu := hzero u
  change (∑ z, a z * if x = z then 1 else 0) +
      (∑ z, b z * if y = z then 1 else 0) = 0 at hu
  simpa using hu

/-- Equivalent one-dimensional description of the incidence kernel. -/
theorem MuThreeMixedGridCode.occupied_incidence_kernel_iff
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a : X → ℚ) (b : Y → ℚ) :
    (∀ x y, ¬ K x y → a x + b y = 0) ↔
      ∃ c : ℚ, (∀ x, a x = c) ∧ (∀ y, b y = -c) := by
  constructor
  · intro hzero
    have hk := code.occupied_incidence_kernel H K C a b hzero
    have hX : Nonempty X := Fintype.card_pos_iff.mp (by simp [code.card_left])
    let x₀ : X := Classical.choice hX
    refine ⟨a x₀, fun x => hk.1 x x₀, ?_⟩
    intro y
    linarith [hk.2.2 x₀ y]
  · rintro ⟨c, ha, hb⟩ x y _hxy
    rw [ha x, hb y]
    ring

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.occupied_incidence_kernel
#print axioms Erdos85.MuThreeMixedGridCode.indicator_combination_eq_zero
#print axioms Erdos85.MuThreeMixedGridCode.occupied_incidence_kernel_iff

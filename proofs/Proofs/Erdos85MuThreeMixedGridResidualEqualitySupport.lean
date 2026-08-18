import Proofs.Erdos85MuThreeMixedGridResidualEnergyRigidity

/-!
# Support structure at equality in the mixed-grid energy bound

At equality, residual edges reverse signs.  Thus the nonzero support is
canonically bipartite by positive versus negative values, and every residual
triangle is forced into the zero set.
-/

open SimpleGraph

namespace Erdos85

/-- Across a residual edge, a nonzero equality-case vector has the opposite
strict sign. -/
theorem MuThreeMixedGridCode.residual_adj_pos_iff_neg_of_energy_eq_fourteen
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f)
    (heq : ((C.adjMatrix ℤ).mulVec f) ⬝ᵥ ((C.adjMatrix ℤ).mulVec f) =
      14 * (f ⬝ᵥ f))
    {u v : muThreeMixedCell K}
    (huv : (mixedGridSquareResidualGraph K C).Adj u v) :
    (0 < f u ↔ f v < 0) ∧ (f u < 0 ↔ 0 < f v) := by
  have hadd :=
    MuThreeMixedGridCode.residual_adj_add_eq_zero_of_energy_eq_fourteen
      H K C code hf heq huv
  constructor <;> omega

/-- A residual triangle cannot meet the support of an equality-case vector. -/
theorem MuThreeMixedGridCode.eq_zero_of_residual_triangle_of_energy_eq_fourteen
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f)
    (heq : ((C.adjMatrix ℤ).mulVec f) ⬝ᵥ ((C.adjMatrix ℤ).mulVec f) =
      14 * (f ⬝ᵥ f))
    {u v w : muThreeMixedCell K}
    (huv : (mixedGridSquareResidualGraph K C).Adj u v)
    (hvw : (mixedGridSquareResidualGraph K C).Adj v w)
    (hwu : (mixedGridSquareResidualGraph K C).Adj w u) :
    f u = 0 ∧ f v = 0 ∧ f w = 0 := by
  have huv0 :=
    MuThreeMixedGridCode.residual_adj_add_eq_zero_of_energy_eq_fourteen
      H K C code hf heq huv
  have hvw0 :=
    MuThreeMixedGridCode.residual_adj_add_eq_zero_of_energy_eq_fourteen
      H K C code hf heq hvw
  have hwu0 :=
    MuThreeMixedGridCode.residual_adj_add_eq_zero_of_energy_eq_fourteen
      H K C code hf heq hwu
  omega

/-- If every vertex of the residual graph lies in a residual triangle, the
energy bound is strict away from the zero vector. -/
theorem MuThreeMixedGridCode.energy_ne_fourteen_of_residual_triangle_cover
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (htri : ∀ u, ∃ v w,
      (mixedGridSquareResidualGraph K C).Adj u v ∧
      (mixedGridSquareResidualGraph K C).Adj v w ∧
      (mixedGridSquareResidualGraph K C).Adj w u)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f)
    (hfne : f ≠ 0) :
    ((C.adjMatrix ℤ).mulVec f) ⬝ᵥ ((C.adjMatrix ℤ).mulVec f) ≠
      14 * (f ⬝ᵥ f) := by
  intro heq
  apply hfne
  funext u
  obtain ⟨v, w, huv, hvw, hwu⟩ := htri u
  exact (MuThreeMixedGridCode.eq_zero_of_residual_triangle_of_energy_eq_fourteen
    H K C code hf heq huv hvw hwu).1

/-- Triangle coverage improves the universal energy bound to a strict bound
for every nonzero integer vector in the zero row/column sector. -/
theorem MuThreeMixedGridCode.adjMatrix_energy_lt_fourteen_of_residual_triangle_cover
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (htri : ∀ u, ∃ v w,
      (mixedGridSquareResidualGraph K C).Adj u v ∧
      (mixedGridSquareResidualGraph K C).Adj v w ∧
      (mixedGridSquareResidualGraph K C).Adj w u)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f)
    (hfne : f ≠ 0) :
    ((C.adjMatrix ℤ).mulVec f) ⬝ᵥ ((C.adjMatrix ℤ).mulVec f) <
      14 * (f ⬝ᵥ f) := by
  exact lt_of_le_of_ne
    (MuThreeMixedGridCode.adjMatrix_energy_le_fourteen_on_zeroSector
      H K C code hf)
    (MuThreeMixedGridCode.energy_ne_fourteen_of_residual_triangle_cover
      H K C code htri hf hfne)

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.residual_adj_pos_iff_neg_of_energy_eq_fourteen
#print axioms
  Erdos85.MuThreeMixedGridCode.eq_zero_of_residual_triangle_of_energy_eq_fourteen
#print axioms
  Erdos85.MuThreeMixedGridCode.energy_ne_fourteen_of_residual_triangle_cover
#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_energy_lt_fourteen_of_residual_triangle_cover

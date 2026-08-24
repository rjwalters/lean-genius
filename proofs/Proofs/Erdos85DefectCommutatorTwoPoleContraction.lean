import Proofs.Erdos85CrossNeighborhoodFlipDefectExpansion

/-!
# Two-pole contraction of the defect commutator

Contract the defect commutator against the two-pole vector `h`.  Symmetry
turns left multiplication by `h` into the known right actions `M h` and
`D h`.  Under the Baer identities `M h = 1_L`, `D h = h`, the result is a
leaf-weighted defect term plus a pole-weighted adjacency term; the latter
vanishes when the binary weight is zero on the poles.  This is the matrix
core of `(73rnz_cjibkzb)`.
-/

namespace Erdos85

/-- General symmetric contraction identity for the defect commutator. -/
theorem defectCommutator_contract_eq_leaf_add_pole
    {V : Type*} [Fintype V] [DecidableEq V]
    (M D : Matrix V V (ZMod 2)) (b h leaf : V → ZMod 2)
    (hMsymm : M.IsSymm) (hDsymm : D.IsSymm)
    (hMh : M.mulVec h = leaf) (hDh : D.mulVec h = h)
    (G : V) :
    (∑ i, h i *
      (M * Matrix.diagonal b * D + D * Matrix.diagonal b * M) i G) =
      (∑ x, leaf x * b x * D x G) +
      ∑ x, h x * b x * M x G := by
  have hMleft : ∀ x, (∑ i, h i * M i x) = leaf x := by
    intro x
    calc
      (∑ i, h i * M i x) = ∑ i, M x i * h i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hMsymm.apply x i]
        ac_rfl
      _ = M.mulVec h x := by rfl
      _ = leaf x := by rw [hMh]
  have hDleft : ∀ x, (∑ i, h i * D i x) = h x := by
    intro x
    calc
      (∑ i, h i * D i x) = ∑ i, D x i * h i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hDsymm.apply x i]
        ac_rfl
      _ = D.mulVec h x := by rfl
      _ = h x := by rw [hDh]
  have hfirst : (∑ i, h i * (M * Matrix.diagonal b * D) i G) =
      ∑ x, leaf x * b x * D x G := by
    change (∑ i, h i * ∑ x, (M * Matrix.diagonal b) i x * D x G) = _
    simp_rw [Matrix.mul_diagonal, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    calc
      (∑ i, h i * (M i x * b x * D x G)) =
          ∑ i, (h i * M i x) * (b x * D x G) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, h i * M i x) * (b x * D x G) := by
        rw [Finset.sum_mul]
      _ = leaf x * b x * D x G := by rw [hMleft]; ring
  have hsecond : (∑ i, h i * (D * Matrix.diagonal b * M) i G) =
      ∑ x, h x * b x * M x G := by
    change (∑ i, h i * ∑ x, (D * Matrix.diagonal b) i x * M x G) = _
    simp_rw [Matrix.mul_diagonal, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    calc
      (∑ i, h i * (D i x * b x * M x G)) =
          ∑ i, (h i * D i x) * (b x * M x G) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, h i * D i x) * (b x * M x G) := by
        rw [Finset.sum_mul]
      _ = h x * b x * M x G := by rw [hDleft]; ring
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib,
    hfirst, hsecond]

/-- If the binary weight vanishes on the support of the pole vector, only
the leaf-weighted defect term survives. -/
theorem defectCommutator_contract_eq_leaf_of_poleWeight_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (M D : Matrix V V (ZMod 2)) (b h leaf : V → ZMod 2)
    (hMsymm : M.IsSymm) (hDsymm : D.IsSymm)
    (hMh : M.mulVec h = leaf) (hDh : D.mulVec h = h)
    (hpoleZero : ∀ x, h x * b x = 0) (G : V) :
    (∑ i, h i *
      (M * Matrix.diagonal b * D + D * Matrix.diagonal b * M) i G) =
      ∑ x, leaf x * b x * D x G := by
  rw [defectCommutator_contract_eq_leaf_add_pole
    M D b h leaf hMsymm hDsymm hMh hDh G]
  simp [hpoleZero]

end Erdos85

#print axioms Erdos85.defectCommutator_contract_eq_leaf_add_pole
#print axioms Erdos85.defectCommutator_contract_eq_leaf_of_poleWeight_zero

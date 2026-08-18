import Proofs.Erdos85MuThreeMixedGridZeroSectorOperator

/-!
# Rook and residual actions on the zero sector

Zero row and column sums force the rook operator to act as `-2I`.  Therefore
the residual defect operator acts as `7I - A_C²` on the same sector.
-/

open SimpleGraph

namespace Erdos85

/-- Dotting with a row indicator is summing over that occupied row. -/
theorem dotProduct_rowIndicator_eq_sum_filter
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (x : X) (f : muThreeMixedCell K → ℤ) :
    mixedGridRowIndicator K x ⬝ᵥ f =
      ∑ u ∈ (Finset.univ.filter fun u : muThreeMixedCell K => u.1.1 = x), f u := by
  rw [dotProduct]
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : u.1.1 = x <;> simp [mixedGridRowIndicator, h]

/-- Column dual of the filtered-sum identity. -/
theorem dotProduct_columnIndicator_eq_sum_filter
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (y : Y) (f : muThreeMixedCell K → ℤ) :
    mixedGridColumnIndicator K y ⬝ᵥ f =
      ∑ u ∈ (Finset.univ.filter fun u : muThreeMixedCell K => u.1.2 = y), f u := by
  rw [dotProduct]
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : u.1.2 = y <;> simp [mixedGridColumnIndicator, h]

/-- **Rook eigenvalue on the residual sector.** -/
theorem MixedGridZeroRowColumn.rowColumn_adjMatrix_mulVec_eq_neg_two
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    ((mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f = (-2 : ℤ) • f := by
  funext u
  let R := (Finset.univ : Finset (muThreeMixedCell K)).filter
    fun v => v.1.1 = u.1.1
  let L := R.erase u
  let S := (Finset.univ : Finset (muThreeMixedCell K)).filter
    fun v => v.1.2 = u.1.2
  let M := S.erase u
  have huR : u ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hdisjoint : Disjoint L M := by
    rw [Finset.disjoint_left]
    intro v hvL hvM
    have hvR := Finset.mem_erase.mp hvL
    have hvS := Finset.mem_erase.mp hvM
    apply hvR.1
    apply Subtype.ext
    apply Prod.ext
    · exact (Finset.mem_filter.mp hvR.2).2
    · exact (Finset.mem_filter.mp hvS.2).2
  have hneighbors : (mixedGridRowColumnGraph K).neighborFinset u = L ∪ M := by
    ext v
    simp only [mem_neighborFinset, mixedGridRowColumnGraph,
      Finset.mem_union, L, M, Finset.mem_erase, R, S,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hrow | hcol⟩
      · exact Or.inl ⟨hne.symm, hrow.symm⟩
      · exact Or.inr ⟨hne.symm, hcol.symm⟩
    · rintro (⟨hne, hrow⟩ | ⟨hne, hcol⟩)
      · exact ⟨hne.symm, Or.inl hrow.symm⟩
      · exact ⟨hne.symm, Or.inr hcol.symm⟩
  have hRzero : ∑ v ∈ R, f v = 0 := by
    rw [← dotProduct_rowIndicator_eq_sum_filter u.1.1 f]
    exact hf.1 u.1.1
  have hSzero : ∑ v ∈ S, f v = 0 := by
    rw [← dotProduct_columnIndicator_eq_sum_filter u.1.2 f]
    exact hf.2 u.1.2
  have hLsum : ∑ v ∈ L, f v = -f u := by
    have hsplit := Finset.sum_erase_add R f huR
    change (∑ v ∈ R.erase u, f v) + f u = ∑ v ∈ R, f v at hsplit
    rw [hRzero] at hsplit
    change (∑ v ∈ R.erase u, f v) = -f u
    linarith
  have hMsum : ∑ v ∈ M, f v = -f u := by
    have hsplit := Finset.sum_erase_add S f huS
    change (∑ v ∈ S.erase u, f v) + f u = ∑ v ∈ S, f v at hsplit
    rw [hSzero] at hsplit
    change (∑ v ∈ S.erase u, f v) = -f u
    linarith
  rw [SimpleGraph.adjMatrix_mulVec_apply, hneighbors,
    Finset.sum_union hdisjoint, hLsum, hMsum]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Residual square action.** On the zero sector, `A_D = 7I - A_C²`. -/
theorem MuThreeMixedGridCode.residual_adjMatrix_mulVec_eq_on_zeroSector
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    ((mixedGridSquareResidualGraph K C).adjMatrix ℤ).mulVec f =
      (7 : ℤ) • f -
        (C.adjMatrix ℤ).mulVec ((C.adjMatrix ℤ).mulVec f) := by
  have h := MuThreeMixedGridCode.residual_add_rowColumn_mulVec_eq_on_zeroSector
    H K C code hf
  rw [Matrix.add_mulVec,
    MixedGridZeroRowColumn.rowColumn_adjMatrix_mulVec_eq_neg_two hf] at h
  funext u
  have hu := congrFun h u
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hu ⊢
  linarith

end Erdos85

#print axioms
  Erdos85.MixedGridZeroRowColumn.rowColumn_adjMatrix_mulVec_eq_neg_two
#print axioms
  Erdos85.MuThreeMixedGridCode.residual_adjMatrix_mulVec_eq_on_zeroSector

import Proofs.Erdos85BinarySquareOwnerCommonBottom
import Proofs.Erdos85PrincipalIndicatorTrace

/-!
# Exact adjacency kernel in the regular binary-square core

The component-constant construction exhausts the ambient adjacency kernel.
Thus adjacency nullity is exactly one less than the number of connected
components of the second-order defect graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem binarySquare_regular_sum_adj_mulVec_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hreg : ∀ x, G.degree x = q) (v : V → ℚ) :
    ∑ x, (G.adjMatrix ℚ).mulVec v x = (q : ℚ) * ∑ x, v x := by
  have hcol (y : V) : ∑ x, G.adjMatrix ℚ x y = (q : ℚ) := by
    have hrow := G.adjMatrix_mulVec_const_apply (α := ℚ)
      (v := y) (a := 1)
    rw [Matrix.mulVec, dotProduct] at hrow
    simpa [SimpleGraph.adjMatrix_apply, G.adj_comm, hreg y] using hrow
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ x, G.adjMatrix ℚ x y * v y) =
        ∑ y, (∑ x, G.adjMatrix ℚ x y) * v y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [Finset.sum_mul]
    _ = ∑ y, (q : ℚ) * v y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [hcol y]
    _ = (q : ℚ) * ∑ y, v y := by rw [Finset.mul_sum]

private theorem binarySquare_regular_defect_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    ∀ x, (secondOrderDefectGraph G).degree x = q - 1 := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  intro x
  have h := secondOrderDefectGraph_degree_eq_excess_add_two
    G hfree hreg hcensus x
  change (secondOrderDefectGraph G).degree x = (q - 3) + 2 at h
  omega

/-- A rational adjacency-kernel vector is exactly the component-constant
extension of its values at component representatives, and those coefficients
annihilate the component quotient row. -/
theorem binarySquare_regular_adj_kernel_vector_component_representation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (v : V → ℚ) (hv : (G.adjMatrix ℚ).mulVec v = 0) :
    let a : (secondOrderDefectGraph G).ConnectedComponent → ℚ :=
      fun c => v (componentRepresentative (secondOrderDefectGraph G) c)
    defectComponentConstantLinearMapRat (secondOrderDefectGraph G) a = v ∧
      componentQuotientRowLinearMapRat G
        (secondOrderDefectGraph G) e₀ a = 0 := by
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let J := ratOnesMatrix V
  let a : D.ConnectedComponent → ℚ :=
    fun c => v (componentRepresentative D c)
  have hsumA := binarySquare_regular_sum_adj_mulVec_eq G hreg v
  rw [hv] at hsumA
  simp only [Pi.zero_apply, Finset.sum_const_zero] at hsumA
  have hq0 : (q : ℚ) ≠ 0 := by positivity
  have hsum : ∑ x, v x = 0 := by
    exact (mul_eq_zero.mp hsumA.symm).resolve_left hq0
  have hJv : J.mulVec v = 0 := by
    funext x
    simp [J, ratOnesMatrix, Matrix.mulVec, dotProduct, hsum]
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
    G hfree hreg
  have hvD : (D.adjMatrix ℚ).mulVec v = ((q - 1 : ℕ) : ℚ) • v := by
    have hh := congrArg (fun M => M.mulVec v) hsq
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero] at hh
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec] at hh
    rw [hJv] at hh
    have hcast : ((q : ℚ) - 1) = ((q - 1 : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
    rw [hcast] at hh
    simpa using (sub_eq_zero.mp hh.symm).symm
  have hDreg : ∀ x, D.degree x = q - 1 :=
    binarySquare_regular_defect_degree G hfree hq hreg hcard
  have hconst (x y : V) (hxy : D.connectedComponentMk x =
      D.connectedComponentMk y) : v x = v y := by
    apply apply_eq_of_mulVec_eq_smul_of_reachable D hDreg hvD
    exact SimpleGraph.ConnectedComponent.eq.mp hxy
  have hext : defectComponentConstantLinearMapRat D a = v := by
    funext x
    let c := D.connectedComponentMk x
    have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c
        (componentRepresentative D c)).mp (componentRepresentative_mem D c)
    change v (componentRepresentative D c) = v x
    exact hconst _ _ (hrep.trans rfl.symm)
  have hrowAction :=
    binarySquare_regular_adj_mulVec_defectComponentConstantLinearMapRat
      G hfree hq hreg hcard e₀ a
  rw [hext, hv] at hrowAction
  have hrow : componentQuotientRowLinearMapRat G D e₀ a = 0 := by
    have happ := congrFun hrowAction (componentRepresentative D e₀)
    simpa using happ.symm
  exact ⟨hext, hrow⟩

/-- Read a kernel vector on one representative of each defect component. -/
def binarySquareAdjKernelToComponentRowKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ : (secondOrderDefectGraph G).ConnectedComponent) :
    LinearMap.ker (G.adjMatrix ℚ).mulVecLin →ₗ[ℚ]
      LinearMap.ker (componentQuotientRowLinearMapRat G
        (secondOrderDefectGraph G) e₀) where
  toFun v := ⟨fun c => v.1 (componentRepresentative
      (secondOrderDefectGraph G) c),
    (binarySquare_regular_adj_kernel_vector_component_representation
      G hfree hq hreg hcard e₀ v.1 v.2).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem binarySquareAdjKernelToComponentRowKernel_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ : (secondOrderDefectGraph G).ConnectedComponent) :
    Function.Injective
      (binarySquareAdjKernelToComponentRowKernel
        G hfree hq hreg hcard e₀) := by
  intro u v huv
  apply Subtype.ext
  have hcoeff : (fun c => u.1 (componentRepresentative
      (secondOrderDefectGraph G) c)) =
      (fun c => v.1 (componentRepresentative
        (secondOrderDefectGraph G) c)) :=
    congrArg Subtype.val huv
  have hu := (binarySquare_regular_adj_kernel_vector_component_representation
    G hfree hq hreg hcard e₀ u.1 u.2).1
  have hv := (binarySquare_regular_adj_kernel_vector_component_representation
    G hfree hq hreg hcard e₀ v.1 v.2).1
  rw [← hu, ← hv, hcoeff]

/-- **Exact nullity theorem.**  No adjacency-kernel directions exist beyond
the weighted-zero component-constant vectors. -/
theorem binarySquare_regular_finrank_adj_kernel_eq_card_components_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ : (secondOrderDefectGraph G).ConnectedComponent) :
    Module.finrank ℚ (LinearMap.ker (G.adjMatrix ℚ).mulVecLin) =
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent - 1 := by
  let f := componentQuotientRowLinearMapRat G
    (secondOrderDefectGraph G) e₀
  have hf : f ≠ 0 :=
    binarySquare_regular_componentQuotientRowLinearMapRat_ne_zero
      G hfree hq hreg hcard e₀
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  rw [Module.finrank_pi] at hdim
  have hrowdim : Module.finrank ℚ (LinearMap.ker f) =
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent - 1 := by
    omega
  have hlower :=
    binarySquare_regular_card_components_sub_one_le_finrank_adj_kernel
      G hfree hq hreg hcard e₀
  have hupper0 := LinearMap.finrank_le_finrank_of_injective
    (binarySquareAdjKernelToComponentRowKernel_injective
      G hfree hq hreg hcard e₀)
  rw [hrowdim] at hupper0
  exact Nat.le_antisymm hupper0 hlower

end

end Erdos85

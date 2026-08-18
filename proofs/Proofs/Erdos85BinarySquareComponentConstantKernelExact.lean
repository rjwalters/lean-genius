import Proofs.Erdos85BinarySquareAdjacencyKernelRat
import Proofs.Erdos85BinarySquareComponentConstantKernelDimension

/-!
# Exact component-constant adjacency kernel over `ℚ`

The previously constructed quotient-row-kernel embedding is surjective: the
pointwise kernel classification shows that every rational adjacency-kernel
vector is constant on defect components.  Hence the map is a linear
equivalence and the rational adjacency nullity is exactly `r - 1`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The component-constant kernel embedding hits every rational adjacency
kernel vector. -/
theorem binarySquareComponentConstantKernelMap_surjective
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
    Function.Surjective
      (binarySquareComponentConstantKernelMap
        G hfree hq hreg hcard e₀) := by
  let D := secondOrderDefectGraph G
  intro v
  have hvchar := (binarySquare_regular_adjMatrix_mulVec_eq_zero_iff_rat
    G hfree hq hreg hcard v.1).mp v.2
  let a : D.ConnectedComponent → ℚ :=
    fun c => v.1 (componentRepresentative D c)
  have hext : defectComponentConstantLinearMapRat D a = v.1 := by
    funext x
    rw [defectComponentConstantLinearMapRat_apply]
    let c := D.connectedComponentMk x
    have hrep : componentRepresentative D c ∈ c.supp :=
      componentRepresentative_mem D c
    have hx : x ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
    exact hvchar.1 _ _ (c.reachable_of_mem_supp hrep hx)
  have ha : componentQuotientRowLinearMapRat G D e₀ a = 0 := by
    have hact :=
      binarySquare_regular_adj_mulVec_defectComponentConstantLinearMapRat
        G hfree hq hreg hcard e₀ a
    have hvzero : (G.adjMatrix ℚ).mulVec v.1 = 0 := v.2
    rw [hext, hvzero] at hact
    have hx := congrFun hact (componentRepresentative D e₀)
    simpa using hx.symm
  let aker : LinearMap.ker (componentQuotientRowLinearMapRat G D e₀) :=
    ⟨a, ha⟩
  refine ⟨aker, ?_⟩
  apply Subtype.ext
  exact hext

/-- The quotient-row kernel and ambient adjacency kernel are linearly
equivalent. -/
def binarySquareComponentConstantKernelEquiv
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
    LinearMap.ker (componentQuotientRowLinearMapRat G
        (secondOrderDefectGraph G) e₀) ≃ₗ[ℚ]
      LinearMap.ker (G.adjMatrix ℚ).mulVecLin :=
  LinearEquiv.ofBijective
    (binarySquareComponentConstantKernelMap
      G hfree hq hreg hcard e₀)
    ⟨binarySquareComponentConstantKernelMap_injective
        G hfree hq hreg hcard e₀,
      binarySquareComponentConstantKernelMap_surjective
        G hfree hq hreg hcard e₀⟩

/-- **Exact rational adjacency nullity.** -/
theorem binarySquare_regular_finrank_adj_kernel_rat
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
  let D := secondOrderDefectGraph G
  let f := componentQuotientRowLinearMapRat G D e₀
  have hf : f ≠ 0 :=
    binarySquare_regular_componentQuotientRowLinearMapRat_ne_zero
      G hfree hq hreg hcard e₀
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hequiv := binarySquareComponentConstantKernelEquiv
    G hfree hq hreg hcard e₀
  have heq : Module.finrank ℚ (LinearMap.ker f) =
      Module.finrank ℚ (LinearMap.ker (G.adjMatrix ℚ).mulVecLin) :=
    LinearEquiv.finrank_eq hequiv
  have hdim' :
      Module.finrank ℚ (LinearMap.ker f) + 1 =
        Fintype.card D.ConnectedComponent := by
    calc
      _ = Module.finrank ℚ (D.ConnectedComponent → ℚ) := hdim
      _ = Fintype.card D.ConnectedComponent := by
        simp only [Module.finrank_pi]
  have htarget :
      Module.finrank ℚ
          (LinearMap.ker (G.adjMatrix ℚ).mulVecLin) + 1 =
        Fintype.card D.ConnectedComponent := by
    rw [← heq]
    exact hdim'
  have hrpos : 1 ≤ Fintype.card D.ConnectedComponent := by
    exact Fintype.card_pos_iff.mpr ⟨e₀⟩
  change Module.finrank ℚ
      (LinearMap.ker (G.adjMatrix ℚ).mulVecLin) =
    Fintype.card D.ConnectedComponent - 1
  omega

end

end Erdos85

import Proofs.Erdos85BinarySquareAdjacencyKernelCharacterization
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Exact real adjacency nullity at regular square order

The pointwise kernel characterization identifies the real adjacency kernel
with component-constant functions whose total coordinate sum is zero.  This
file packages that description as a linear equivalence and computes its
dimension directly over `ℝ`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Extend real coefficients constantly over connected components. -/
def defectComponentConstantLinearMapReal
    {V : Type*} (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent] :
    (D.ConnectedComponent → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun a x := a (D.connectedComponentMk x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem defectComponentConstantLinearMapReal_apply
    {V : Type*} (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (a : D.ConnectedComponent → ℝ) (x : V) :
    defectComponentConstantLinearMapReal D a x =
      a (D.connectedComponentMk x) := rfl

/-- Sum of all ambient coordinates after component-constant extension. -/
def componentConstantCoordinateSumLinearMapReal
    {V : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent] :
    (D.ConnectedComponent → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ x, a (D.connectedComponentMk x)
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.mul_sum]

@[simp] theorem componentConstantCoordinateSumLinearMapReal_apply
    {V : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (a : D.ConnectedComponent → ℝ) :
    componentConstantCoordinateSumLinearMapReal D a =
      ∑ x, a (D.connectedComponentMk x) := rfl

private theorem defectComponentConstantLinearMapReal_injective
    {V : Type*} (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent] :
    Function.Injective (defectComponentConstantLinearMapReal D) := by
  intro a b hab
  funext c
  let x := componentRepresentative D c
  have hx : D.connectedComponentMk x = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp
      (componentRepresentative_mem D c)
  have h := congrFun hab x
  simpa [defectComponentConstantLinearMapReal_apply, hx] using h

private theorem componentConstantCoordinateSumLinearMapReal_ne_zero
    {V : Type*} [Fintype V] [Nonempty V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent] :
    componentConstantCoordinateSumLinearMapReal D ≠ 0 := by
  intro hzero
  have h := LinearMap.congr_fun hzero (fun _ => (1 : ℝ))
  simp [componentConstantCoordinateSumLinearMapReal] at h

/-- Component-sum-zero coefficients embed into the real adjacency kernel. -/
def binarySquareRealComponentConstantKernelMap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    LinearMap.ker (componentConstantCoordinateSumLinearMapReal
        (secondOrderDefectGraph G)) →ₗ[ℝ]
      LinearMap.ker (G.adjMatrix ℝ).mulVecLin where
  toFun a := ⟨defectComponentConstantLinearMapReal
      (secondOrderDefectGraph G) a.1, by
    rw [LinearMap.mem_ker]
    apply (binarySquare_regular_adjMatrix_mulVec_eq_zero_iff
      G hfree hq hreg hcard _).mpr
    constructor
    · intro x y hxy
      change a.1 ((secondOrderDefectGraph G).connectedComponentMk x) =
        a.1 ((secondOrderDefectGraph G).connectedComponentMk y)
      exact congrArg a.1 (ConnectedComponent.sound hxy)
    · exact a.2⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

private theorem binarySquareRealComponentConstantKernelMap_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    Function.Injective
      (binarySquareRealComponentConstantKernelMap
        G hfree hq hreg hcard) := by
  intro a b hab
  apply Subtype.ext
  apply defectComponentConstantLinearMapReal_injective
    (secondOrderDefectGraph G)
  exact congrArg Subtype.val hab

private theorem binarySquareRealComponentConstantKernelMap_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    Function.Surjective
      (binarySquareRealComponentConstantKernelMap
        G hfree hq hreg hcard) := by
  intro v
  obtain ⟨hconst, hsum⟩ :=
    (binarySquare_regular_adjMatrix_mulVec_eq_zero_iff
      G hfree hq hreg hcard v.1).mp v.2
  let D := secondOrderDefectGraph G
  let a : D.ConnectedComponent → ℝ :=
    fun c => v.1 (componentRepresentative D c)
  have hext : defectComponentConstantLinearMapReal D a = v.1 := by
    funext x
    rw [defectComponentConstantLinearMapReal_apply]
    let c := D.connectedComponentMk x
    have hrep : componentRepresentative D c ∈ c.supp :=
      componentRepresentative_mem D c
    have hx : x ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
    exact hconst _ _ (c.reachable_of_mem_supp hrep hx)
  have ha : componentConstantCoordinateSumLinearMapReal D a = 0 := by
    change ∑ x, a (D.connectedComponentMk x) = 0
    change ∑ x, defectComponentConstantLinearMapReal D a x = 0
    rw [hext]
    exact hsum
  refine ⟨⟨a, ha⟩, ?_⟩
  apply Subtype.ext
  exact hext

/-- The real component-sum kernel and real adjacency kernel are linearly
equivalent. -/
def binarySquareRealComponentConstantKernelEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    LinearMap.ker (componentConstantCoordinateSumLinearMapReal
        (secondOrderDefectGraph G)) ≃ₗ[ℝ]
      LinearMap.ker (G.adjMatrix ℝ).mulVecLin :=
  LinearEquiv.ofBijective
    (binarySquareRealComponentConstantKernelMap
      G hfree hq hreg hcard)
    ⟨binarySquareRealComponentConstantKernelMap_injective
        G hfree hq hreg hcard,
      binarySquareRealComponentConstantKernelMap_surjective
        G hfree hq hreg hcard⟩

/-- **Exact real adjacency nullity:** one less than the number of defect
components. -/
theorem binarySquare_regular_finrank_adj_kernel_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    Module.finrank ℝ (LinearMap.ker (G.adjMatrix ℝ).mulVecLin) =
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent - 1 := by
  let D := secondOrderDefectGraph G
  let f := componentConstantCoordinateSumLinearMapReal D
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  have hf : f ≠ 0 :=
    componentConstantCoordinateSumLinearMapReal_ne_zero D
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have heq : Module.finrank ℝ (LinearMap.ker f) =
      Module.finrank ℝ (LinearMap.ker (G.adjMatrix ℝ).mulVecLin) :=
    LinearEquiv.finrank_eq
      (binarySquareRealComponentConstantKernelEquiv
        G hfree hq hreg hcard)
  have htarget :
      Module.finrank ℝ (LinearMap.ker (G.adjMatrix ℝ).mulVecLin) + 1 =
        Fintype.card D.ConnectedComponent := by
    rw [← heq]
    calc
      _ = Module.finrank ℝ (D.ConnectedComponent → ℝ) := hdim
      _ = Fintype.card D.ConnectedComponent := by
        simp only [Module.finrank_pi]
  have hpos : 1 ≤ Fintype.card D.ConnectedComponent := by
    exact Fintype.card_pos_iff.mpr ⟨D.connectedComponentMk
      (Classical.choice inferInstance)⟩
  change Module.finrank ℝ (LinearMap.ker (G.adjMatrix ℝ).mulVecLin) =
    Fintype.card D.ConnectedComponent - 1
  omega

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_finrank_adj_kernel_real

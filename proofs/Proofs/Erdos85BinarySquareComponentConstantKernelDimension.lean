import Proofs.Erdos85BinarySquareRegularParity
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Dimension of the component-constant adjacency kernel

The component quotient has one scalar row.  Extending coefficient vectors
constantly over defect components embeds the kernel of that row into the
ambient adjacency kernel.  Since the quotient row is nonzero, this gives an
exact `(number of components) - 1` dimensional subspace of `ker A`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Extend rational coefficients constantly over connected components. -/
def defectComponentConstantLinearMapRat
    {V : Type*} (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent] :
    (D.ConnectedComponent → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun a x := a (D.connectedComponentMk x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem defectComponentConstantLinearMapRat_apply
    {V : Type*} (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (a : D.ConnectedComponent → ℚ) (x : V) :
    defectComponentConstantLinearMapRat D a x =
      a (D.connectedComponentMk x) := rfl

/-- Component-constant extension loses no coefficient information. -/
theorem defectComponentConstantLinearMapRat_injective
    {V : Type*} (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent] :
    Function.Injective (defectComponentConstantLinearMapRat D) := by
  intro a b hab
  funext c
  let x := componentRepresentative D c
  have hx : D.connectedComponentMk x = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp
      (componentRepresentative_mem D c)
  have h := congrFun hab x
  simpa [defectComponentConstantLinearMapRat_apply, hx] using h

/-- One rational row of the component quotient. -/
def componentQuotientRowLinearMapRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (e₀ : D.ConnectedComponent) :
    (D.ConnectedComponent → ℚ) →ₗ[ℚ] ℚ :=
  ∑ c, (componentQuotientMatrix G D e₀ c : ℚ) •
    LinearMap.proj c

@[simp] theorem componentQuotientRowLinearMapRat_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (e₀ : D.ConnectedComponent) (a : D.ConnectedComponent → ℚ) :
    componentQuotientRowLinearMapRat G D e₀ a =
      ∑ c, (componentQuotientMatrix G D e₀ c : ℚ) * a c := by
  simp [componentQuotientRowLinearMapRat]

/-- Rational indicator of one defect component. -/
private def defectComponentIndicatorRat
    {V : Type*} (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) : V → ℚ :=
  fun x => if D.connectedComponentMk x = c then 1 else 0

private theorem binarySquare_regular_adj_mulVec_defectComponentIndicatorRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ c : (secondOrderDefectGraph G).ConnectedComponent) :
    (G.adjMatrix ℚ).mulVec
        (defectComponentIndicatorRat (secondOrderDefectGraph G) c) =
      fun _ => (componentQuotientMatrix G
        (secondOrderDefectGraph G) e₀ c : ℚ) := by
  funext x
  rw [Matrix.mulVec, dotProduct]
  simp only [SimpleGraph.adjMatrix_apply, defectComponentIndicatorRat,
    ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilt : Finset.univ.filter (fun y => G.Adj x y) =
      G.neighborFinset x := by
    ext y
    simp [SimpleGraph.mem_neighborFinset]
  rw [hfilt]
  calc
    (∑ y ∈ G.neighborFinset x,
        if (secondOrderDefectGraph G).connectedComponentMk y = c
          then (1 : ℚ) else 0) =
        ((componentNeighborFinset G (secondOrderDefectGraph G) c x).card : ℚ) := by
      rw [Finset.sum_boole]
      congr 2
    _ = (componentQuotientMatrix G
          (secondOrderDefectGraph G) e₀ c : ℚ) := by
      exact congrArg (fun n : ℕ => (n : ℚ))
        (binarySquare_regular_componentNeighborCard_eq_quotient
          G hfree hq hreg hcard e₀ c x)

/-- Exact adjacency action on rational component-constant vectors. -/
theorem binarySquare_regular_adj_mulVec_defectComponentConstantLinearMapRat
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
    (a : (secondOrderDefectGraph G).ConnectedComponent → ℚ) :
    (G.adjMatrix ℚ).mulVec
        (defectComponentConstantLinearMapRat (secondOrderDefectGraph G) a) =
      fun _ => componentQuotientRowLinearMapRat G
        (secondOrderDefectGraph G) e₀ a := by
  let D := secondOrderDefectGraph G
  have hdecomp : defectComponentConstantLinearMapRat D a =
      ∑ c, a c • defectComponentIndicatorRat D c := by
    funext x
    simp [defectComponentConstantLinearMapRat_apply,
      defectComponentIndicatorRat]
  dsimp only [D] at hdecomp
  rw [hdecomp, Matrix.mulVec_sum]
  simp_rw [Matrix.mulVec_smul]
  simp_rw [binarySquare_regular_adj_mulVec_defectComponentIndicatorRat
    G hfree hq hreg hcard e₀]
  funext x
  simp [componentQuotientRowLinearMapRat_apply, mul_comm]

/-- The quotient-row kernel embeds linearly into the ambient adjacency
kernel through component-constant extension. -/
def binarySquareComponentConstantKernelMap
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
        (secondOrderDefectGraph G) e₀) →ₗ[ℚ]
      LinearMap.ker (G.adjMatrix ℚ).mulVecLin where
  toFun a := ⟨defectComponentConstantLinearMapRat
      (secondOrderDefectGraph G) a.1, by
    rw [LinearMap.mem_ker]
    have hact := binarySquare_regular_adj_mulVec_defectComponentConstantLinearMapRat
      G hfree hq hreg hcard e₀ a.1
    rw [show componentQuotientRowLinearMapRat G
      (secondOrderDefectGraph G) e₀ a.1 = 0 from a.2] at hact
    change (G.adjMatrix ℚ).mulVec
      (defectComponentConstantLinearMapRat (secondOrderDefectGraph G) a.1) =
        (fun _ => 0)
    exact hact⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

theorem binarySquareComponentConstantKernelMap_injective
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
      (binarySquareComponentConstantKernelMap G hfree hq hreg hcard e₀) := by
  intro a b hab
  apply Subtype.ext
  apply defectComponentConstantLinearMapRat_injective
    (secondOrderDefectGraph G)
  exact congrArg Subtype.val hab

/-- The quotient row is nonzero: every defect component has positive order,
and its quotient entry is that order divided by `q`. -/
theorem binarySquare_regular_componentQuotientRowLinearMapRat_ne_zero
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
    componentQuotientRowLinearMapRat G
      (secondOrderDefectGraph G) e₀ ≠ 0 := by
  intro hz
  have hmul := binarySquare_regular_mul_componentQuotient_eq_componentCard
    G hfree hq hreg hcard e₀ e₀
  have hpos : 0 < e₀.supp.ncard := e₀.nonempty_supp.ncard_pos
  have hqpos : 0 < q := by omega
  have hQpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) e₀ e₀ := by
    apply Nat.pos_of_mul_pos_left
    rw [hmul]
    exact hpos
  have heval : componentQuotientRowLinearMapRat G
      (secondOrderDefectGraph G) e₀ (Pi.single e₀ 1) =
      (componentQuotientMatrix G (secondOrderDefectGraph G) e₀ e₀ : ℚ) := by
    rw [componentQuotientRowLinearMapRat_apply, Finset.sum_eq_single e₀]
    · simp
    · intro c _hc hce
      simp [Pi.single_eq_of_ne hce]
    · simp
  have happ := LinearMap.congr_fun hz (Pi.single e₀ 1)
  rw [heval] at happ
  norm_num at happ
  have hnat : componentQuotientMatrix G
      (secondOrderDefectGraph G) e₀ e₀ = 0 := by
    exact_mod_cast happ
  exact hQpos.ne' hnat

/-- **Component-kernel dimension theorem.**  The ambient adjacency kernel
has dimension at least one less than the number of defect components. -/
theorem binarySquare_regular_card_components_sub_one_le_finrank_adj_kernel
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
    Fintype.card (secondOrderDefectGraph G).ConnectedComponent - 1 ≤
      Module.finrank ℚ (LinearMap.ker (G.adjMatrix ℚ).mulVecLin) := by
  let D := secondOrderDefectGraph G
  let f := componentQuotientRowLinearMapRat G D e₀
  let ι := binarySquareComponentConstantKernelMap G hfree hq hreg hcard e₀
  have hf : f ≠ 0 :=
    binarySquare_regular_componentQuotientRowLinearMapRat_ne_zero
      G hfree hq hreg hcard e₀
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have hinj : Function.Injective ι :=
    binarySquareComponentConstantKernelMap_injective
      G hfree hq hreg hcard e₀
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_pi] at hdim
  have hkerdim : Module.finrank ℚ (LinearMap.ker f) =
      Fintype.card D.ConnectedComponent - 1 := by omega
  rw [← hkerdim]
  exact hle

end

end Erdos85

import Proofs.Erdos85BinarySquareComponentAdjacencyToAllOwnerSpectrum
import Proofs.Erdos85AdjacencyDefectEigenvector

/-!
# From a defect-component eigenvector to the ambient adjacency square

This file supplies the zero-extension bridge between a single connected
component of the defect graph and the global defect/ambient operators.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Extend a vector on one connected-component support by zero. -/
def connectedComponentExtend
    {V R : Type*} [Zero R] (D : SimpleGraph V)
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) (v : c.supp → R) : V → R := by
  classical
  exact fun x => if hx : x ∈ c.supp then v ⟨x, hx⟩ else 0

@[simp] theorem connectedComponentExtend_apply_mem
    {V R : Type*} [Zero R] (D : SimpleGraph V)
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) (v : c.supp → R)
    (x : V) (hx : x ∈ c.supp) :
    connectedComponentExtend D c v x = v ⟨x, hx⟩ := by
  simp [connectedComponentExtend, hx]

@[simp] theorem connectedComponentExtend_apply_not_mem
    {V R : Type*} [Zero R] (D : SimpleGraph V)
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) (v : c.supp → R)
    (x : V) (hx : x ∉ c.supp) :
    connectedComponentExtend D c v x = 0 := by
  simp [connectedComponentExtend, hx]

/-- Zero extension preserves the coordinate sum. -/
theorem sum_connectedComponentExtend
    {V R : Type*} [Fintype V] [DecidableEq V] [AddCommMonoid R]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [Fintype c.supp] (v : c.supp → R) :
    ∑ x : V, connectedComponentExtend D c v x = ∑ z : c.supp, v z := by
  classical
  let s := (Finset.univ : Finset V).filter (fun x => x ∈ c.supp)
  have hrestrict :
      (∑ x ∈ s, connectedComponentExtend D c v x) =
        ∑ x : V, connectedComponentExtend D c v x := by
    apply Finset.sum_subset (by simp [s])
    intro x _hx hxnot
    have hnot : x ∉ c.supp := by simpa [s] using hxnot
    simp [connectedComponentExtend, hnot]
  calc
    (∑ x : V, connectedComponentExtend D c v x) =
        ∑ x ∈ s, connectedComponentExtend D c v x := hrestrict.symm
    _ = ∑ z : c.supp, v z := by
      rw [Finset.sum_subtype s]
      · apply Finset.sum_congr rfl
        intro z _hz
        simp [connectedComponentExtend]
      · intro x
        simp [s]

/-- A nonprincipal eigenvector of a finite regular graph has coordinate sum
zero. -/
theorem sum_eq_zero_of_regular_adjMatrix_eigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (k : ℕ) (hreg : ∀ x, H.degree x = k)
    (v : V → ℝ) (μ : ℝ)
    (hv : (H.adjMatrix ℝ).mulVec v = μ • v)
    (hμ : μ ≠ k) :
    ∑ x, v x = 0 := by
  have hJ := ones_mulVec_eq_zero_of_adj_eigenvector_ne_degree
    H hreg hμ v hv
  cases isEmpty_or_nonempty V with
  | inl h => simp
  | inr h =>
      let x : V := Classical.choice h
      have hx := congrFun hJ x
      simpa [Matrix.mulVec, dotProduct] using hx

/-- Zero extension intertwines an induced connected-component adjacency block
with the global adjacency matrix. -/
theorem adjMatrix_mulVec_connectedComponentExtend
    {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent)
    (v : c.supp → R) :
    (D.adjMatrix R).mulVec (connectedComponentExtend D c v) =
      connectedComponentExtend D c
        (((D.induce c.supp).adjMatrix R).mulVec v) := by
  classical
  ext x
  rw [D.adjMatrix_mulVec_apply]
  by_cases hx : x ∈ c.supp
  · rw [connectedComponentExtend_apply_mem D c _ x hx,
      (D.induce c.supp).adjMatrix_mulVec_apply]
    apply Finset.sum_bij
        (fun y hy =>
          ⟨y, c.mem_supp_of_adj_mem_supp hx
            ((D.mem_neighborFinset x y).mp hy)⟩)
    · intro y hy
      simp only [SimpleGraph.mem_neighborFinset]
      exact (D.mem_neighborFinset x y).mp hy
    · intro y₁ hy₁ y₂ hy₂ heq
      exact Subtype.ext_iff.mp heq
    · intro z hz
      have hz' : D.Adj x z.1 := by
        simpa [SimpleGraph.mem_neighborFinset] using hz
      refine ⟨z.1, (D.mem_neighborFinset x z.1).mpr hz', ?_⟩
      exact Subtype.ext rfl
    · intro y hy
      rw [connectedComponentExtend_apply_mem D c v y
        (c.mem_supp_of_adj_mem_supp hx
          ((D.mem_neighborFinset x y).mp hy))]
  · rw [connectedComponentExtend_apply_not_mem D c _ x hx]
    apply Finset.sum_eq_zero
    intro y hy
    apply connectedComponentExtend_apply_not_mem
    intro hyc
    exact hx (c.mem_supp_of_adj_mem_supp hyc
      ((D.adj_comm x y).mp ((D.mem_neighborFinset x y).mp hy)))

/-- Hence a component adjacency eigenvector extends to a global defect
eigenvector with the same eigenvalue. -/
theorem global_adjMatrix_eigenvector_of_component_adjMatrix_eigenvector
    {V R : Type*} [Fintype V] [DecidableEq V] [CommSemiring R]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent)
    (v : c.supp → R) (μ : R)
    (hv : ((D.induce c.supp).adjMatrix R).mulVec v = μ • v) :
    (D.adjMatrix R).mulVec (connectedComponentExtend D c v) =
      μ • connectedComponentExtend D c v := by
  rw [adjMatrix_mulVec_connectedComponentExtend D c v, hv]
  ext x
  by_cases hx : x ∈ c.supp <;>
    simp [connectedComponentExtend, hx]

/-- **Ambient square bridge.**  At square order, the zero extension of a
nonprincipal component eigenvector lies in the ambient adjacency-square
eigenspace with eigenvalue `q - 1 - μ`. -/
theorem binarySquare_ambientAdjMatrix_sq_componentEigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (v : c.supp → ℝ) (μ : ℝ)
    (hv : (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℝ).mulVec v =
      μ • v)
    (hμ : μ ≠ ((q - 1 : ℕ) : ℝ)) :
    let u := connectedComponentExtend (secondOrderDefectGraph G) c v
    (G.adjMatrix ℝ).mulVec ((G.adjMatrix ℝ).mulVec u) =
      (((q : ℝ) - 1 - μ) • u) := by
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℝ
  let J : Matrix V V ℝ := Matrix.of fun _ _ => 1
  let u := connectedComponentExtend D c v
  have hDreg : ∀ z : c.supp, (D.induce c.supp).degree z = q - 1 := by
    intro z
    simpa only [D] using
      binarySquare_regular_inducedDefectComponent_degree
        G hfree hq hreg hcard c z
  have hvsum : ∑ z, v z = 0 :=
    sum_eq_zero_of_regular_adjMatrix_eigenvector
      (D.induce c.supp) (q - 1) hDreg v μ hv hμ
  have husum : ∑ x, u x = 0 := by
    rw [sum_connectedComponentExtend D c v]
    exact hvsum
  have hJu : J.mulVec u = 0 := by
    funext x
    simp [J, Matrix.mulVec, dotProduct, husum]
  have hDu : (D.adjMatrix ℝ).mulVec u = μ • u :=
    global_adjMatrix_eigenvector_of_component_adjMatrix_eigenvector
      D c v μ hv
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hsq : A * A = ((q : ℝ) - 1) • (1 : Matrix V V ℝ) + J -
      D.adjMatrix ℝ := by
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hsqZ
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply] at hxy ⊢
    have hc := congrArg (fun z : ℤ => (z : ℝ)) hxy
    push_cast at hc
    simpa [A, D, J, SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix] using hc
  have happ := congrArg (fun M : Matrix V V ℝ => M.mulVec u) hsq
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, hJu, add_zero, hDu] at happ
  simpa [A, D, J, u, sub_smul] using happ

end

end Erdos85

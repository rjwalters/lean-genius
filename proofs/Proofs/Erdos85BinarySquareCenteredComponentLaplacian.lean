import Proofs.Erdos85BinarySquareCenteredComponentIncidence
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Centered component incidences factor defect Laplacians

At the regular square order, the combined defect graph is `(q - 1)`-regular.
Restricting to a connected component preserves every degree.  Consequently the
centered component-incidence self Gram is exactly `q²` times the integral graph
Laplacian of that component.  This exposes the one-dimensional constant kernel
of each block to Mathlib's graph-Laplacian API.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every induced connected component of the square-order defect graph remains
`(q - 1)`-regular. -/
theorem binarySquare_regular_inducedDefectComponent_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) :
    ((secondOrderDefectGraph G).induce c.supp).degree x = q - 1 := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : D.degree x.1 = q - 1 := by
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x.1
    change D.degree x.1 = (q - 3) + 2 at h
    omega
  have hneighbor : D.neighborSet x.1 ⊆ c.supp := by
    intro y hxy
    exact c.mem_supp_of_adj_mem_supp x.2 hxy
  rw [D.degree_induce_of_neighborSet_subset hneighbor]
  exact hDdegree

/-- The centered defect operator on one component is its integral graph
Laplacian. -/
theorem binarySquare_regular_inducedDefectComponent_lapMatrix_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℤ =
      ((q - 1 : ℕ) : ℤ) • (1 : Matrix c.supp c.supp ℤ) -
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ := by
  let H := (secondOrderDefectGraph G).induce c.supp
  change H.lapMatrix ℤ =
    ((q - 1 : ℕ) : ℤ) • (1 : Matrix c.supp c.supp ℤ) - H.adjMatrix ℤ
  ext x y
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
    Matrix.sub_apply, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    have hxdeg : H.degree x = q - 1 := by
      simpa [H] using
        binarySquare_regular_inducedDefectComponent_degree
          G hfree hq hreg hcard c x
    simp [hxdeg]
  · simp [hxy]

/-- **Component Laplacian factorization.**  The centered rectangular incidence
self Gram is `q²` times the integral Laplacian of the induced defect component. -/
theorem transpose_centeredDefectComponentNeighborIncidenceMatrix_mul_self_eq_lapMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (centeredDefectComponentNeighborIncidenceMatrix G q c).transpose *
        centeredDefectComponentNeighborIncidenceMatrix G q c =
      ((q * q : ℕ) : ℤ) •
        ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℤ := by
  rw [binarySquare_regular_inducedDefectComponent_lapMatrix_eq
    G hfree hq hreg hcard c]
  exact transpose_centeredDefectComponentNeighborIncidenceMatrix_mul_self
    G hfree (by omega) hreg hcard c

/-- An induced graph on the support of a connected component has exactly one
connected component.  This packages the quotient-level fact in the cardinal
form needed by the Laplacian nullity theorem. -/
theorem induced_connectedComponent_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (c : D.ConnectedComponent) :
    Fintype.card (D.induce c.supp).ConnectedComponent = 1 := by
  let H := D.induce c.supp
  have hconn : H.Connected := c.connected_toSimpleGraph
  have hsub : Subsingleton H.ConnectedComponent := by
    constructor
    intro a b
    obtain ⟨x, rfl⟩ := a.exists_rep
    obtain ⟨y, rfl⟩ := b.exists_rep
    exact ConnectedComponent.sound (hconn x y)
  have hnonempty : Nonempty H.ConnectedComponent :=
    hconn.nonempty.map H.connectedComponentMk
  rw [Fintype.card_eq_one_iff]
  exact ⟨Classical.choice hnonempty, fun y => hsub.elim y _⟩

/-- Each component Laplacian has exactly the expected one-dimensional real
kernel: the constant direction removed by centering. -/
theorem induced_connectedComponent_lapMatrix_nullity_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (c : D.ConnectedComponent) :
    Module.finrank ℝ
        (Matrix.toLin' ((D.induce c.supp).lapMatrix ℝ)).ker = 1 := by
  rw [← (D.induce c.supp).card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  exact induced_connectedComponent_card_eq_one D c

end

end Erdos85

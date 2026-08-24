import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85ConnectedIncidenceBottleneckEnergy

/-!
# Binary incidence-bottleneck energy

For `E = AD - (J-A)`, the diagonal entry at `x` is
`deg_T(x)-1`, where `T` is the triangle-free-edge graph. At even ambient
degree, `deg_T(x)` is even, so every row of `E` is nonzero. Exact regular
row sums and integrality then give the uniform squared-energy lower bound
`2q²` at square order.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The bottleneck diagonal is one less than the local triangle-free degree. -/
theorem incidenceBottleneck_diag_eq_triangleFreeDegree_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (x : V) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    (A * D - (J - A)) x x =
      ((triangleFreeEdgeGraph G).degree x : ℤ) - 1 := by
  dsimp only
  rw [Matrix.sub_apply, Matrix.sub_apply, G.adjMatrix_mul_apply]
  have hsum :
      (∑ y ∈ G.neighborFinset x,
          (secondOrderDefectGraph G).adjMatrix ℤ y x) =
        ((triangleFreeEdgeGraph G).degree x : ℤ) := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
    have hcast :
        (((triangleFreeEdgeGraph G).neighborFinset x).card : ℤ) =
          ∑ _y ∈ (triangleFreeEdgeGraph G).neighborFinset x, (1 : ℤ) := by
      simp
    rw [hcast]
    simp only [SimpleGraph.adjMatrix_apply]
    rw [← Finset.sum_filter]
    congr 1
    ext y
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨hG, hD⟩
      rcases hD with hanti | htf
      · exact False.elim (((mem_antipodalNeighbors G x y).mp
          ((antipodalGraph_adj G x y).mp hanti.symm)).2.1 hG)
      · exact htf.symm
    · intro htf
      exact ⟨((mem_triangleFreeNeighbors G x y).mp
          ((triangleFreeEdgeGraph_adj G x y).mp htf)).1,
        Or.inr htf.symm⟩
  rw [hsum]
  simp [SimpleGraph.adjMatrix_apply]

/-- At regular square order every row of the incidence bottleneck sums to
zero. -/
theorem binarySquare_incidenceBottleneck_row_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (x : V) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    ∑ y, (A * D - (J - A)) x y = 0 := by
  dsimp only
  let one : V → ℤ := Function.const V 1
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = q - 1 := by
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change (secondOrderDefectGraph G).degree z = (q - 3) + 2 at h
    omega
  have hDone :
      ((secondOrderDefectGraph G).adjMatrix ℤ).mulVec one =
        Function.const V ((q - 1 : ℕ) : ℤ) := by
    funext z
    simpa [one, hDreg z] using
      (SimpleGraph.adjMatrix_mulVec_const_apply
        (G := secondOrderDefectGraph G) (a := (1 : ℤ)) (v := z))
  have hAone : (G.adjMatrix ℤ).mulVec one =
      Function.const V (q : ℤ) := by
    funext z
    simpa [one, hreg z] using
      (SimpleGraph.adjMatrix_mulVec_const_apply
        (G := G) (a := (1 : ℤ)) (v := z))
  have hJone : (Matrix.of (fun _ _ : V => (1 : ℤ))).mulVec one =
      Function.const V (Fintype.card V : ℤ) := by
    funext z
    simp [Matrix.mulVec, dotProduct, one]
  have hAq1 : (G.adjMatrix ℤ).mulVec
      (Function.const V ((q - 1 : ℕ) : ℤ)) =
        Function.const V ((q : ℤ) * ((q - 1 : ℕ) : ℤ)) := by
    funext z
    simpa [hreg z] using
      (SimpleGraph.adjMatrix_mulVec_const_apply
        (G := G) (a := ((q - 1 : ℕ) : ℤ)) (v := z))
  have hmul :
      ((G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
        (Matrix.of (fun _ _ : V => (1 : ℤ)) - G.adjMatrix ℤ)).mulVec one) x = 0 := by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    rw [hDone, hAq1]
    rw [hJone, hAone]
    simp [hcard]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  simpa [Matrix.mulVec, dotProduct, one] using hmul

/-- At even square degree, diagonal parity makes every incidence-bottleneck
row nonzero. Combined with the exact zero row sums and integrality, this gives
the global `2q²` squared-energy lower bound. -/
theorem binarySquare_even_incidenceBottleneck_energy_ge_two_mul_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hqEven : Even q) (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := Matrix.of (fun _ _ : V => (1 : ℤ))
    let E := A * D - (J - A)
    2 * (q * q : ℕ) ≤ ∑ x, ∑ y, (E x y) ^ 2 := by
  dsimp only
  let E := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (Matrix.of (fun _ _ : V => (1 : ℤ)) - G.adjMatrix ℤ)
  have hsum : ∀ x, ∑ y, E x y = 0 := by
    intro x
    exact binarySquare_incidenceBottleneck_row_sum_zero
      G hfree hq hreg hcard x
  have hne : ∀ x, ∃ y, E x y ≠ 0 := by
    intro x
    refine ⟨x, ?_⟩
    have hdiag := incidenceBottleneck_diag_eq_triangleFreeDegree_sub_one G x
    have heven := binarySquare_regular_triangleFree_degree_even
      G hfree hqEven hreg x
    change E x x ≠ 0
    dsimp only [E]
    rw [hdiag]
    obtain ⟨a, ha⟩ := heven
    omega
  have henergy :=
    two_mul_card_le_sum_matrix_sq_of_rows_sum_zero_nonzero E hsum hne
  rw [hcard] at henergy
  exact henergy

#print axioms incidenceBottleneck_diag_eq_triangleFreeDegree_sub_one
#print axioms binarySquare_incidenceBottleneck_row_sum_zero
#print axioms binarySquare_even_incidenceBottleneck_energy_ge_two_mul_sq

end

end Erdos85

import Proofs.Erdos85BinarySquareRegularParity

/-
# Triangle-free degree is bounded by the defect-component multiplicity

In a `q`-regular C4-free graph on `q²` vertices the second-order defect
graph `D = antipodalGraph ⊔ triangleFreeEdgeGraph` splits `V` into
components of order `q · m_c`, and every vertex has exactly `m_c`
neighbours inside component `c`
(`binarySquare_regular_mul_componentNeighborCard_eq_componentCard`).

The `d_x` triangle-free neighbours of `x` are `D`-adjacent to `x` by the
very definition of `D`, hence lie in `x`'s own component.  Therefore

  `q · d_x ≤ |C_x|`, i.e. `d_x ≤ m_{C_x}`.

Consequences recorded in the ledger (2026-09-08, divergence round #111):
a vertex of a size-two component has `d_x ≤ 2`; a vertex with `d_x > q/2`
forces its component to be the unique large one; and summing over `x`,
`q · Σ_x d_x ≤ Σ_x |C_x| = Σ_c |C|² = q² · Σ_c m_c²`, so with
`Σ_x d_x = q³ − 6t` (`t` = triangle count) one gets
`6t ≥ q³ − q · Σ_c m_c²`.
-/

namespace Erdos85

open SimpleGraph

/-- `q · d_x ≤ |C_x|`: the triangle-free degree of `x` is at most the
multiplicity `m_{C_x} = |C_x| / q` of its defect component.  The inclusion
of the triangle-free neighbours in `componentNeighborFinset` is the banked
`triangleFreeNeighbors_subset_componentNeighborFinset`; the count is the
banked partition law. -/
theorem binarySquare_regular_mul_triangleFreeDegree_le_componentCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) (x : V) :
    q * (triangleFreeNeighbors G x).card ≤
      ((secondOrderDefectGraph G).connectedComponentMk x).supp.ncard := by
  have hx : x ∈ ((secondOrderDefectGraph G).connectedComponentMk x).supp :=
    (ConnectedComponent.mem_supp_iff _ _).2 rfl
  have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree hq hreg hcard
    ((secondOrderDefectGraph G).connectedComponentMk x)
    ((secondOrderDefectGraph G).connectedComponentMk x) hx
  rw [← h]
  exact Nat.mul_le_mul_left q
    (Finset.card_le_card
      (triangleFreeNeighbors_subset_componentNeighborFinset G _ hx))

/-- Summed form: `q · Σ_x d_x ≤ Σ_x |C_x|`. -/
theorem binarySquare_regular_mul_sum_triangleFreeDegree_le_sum_componentCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    q * ∑ x, (triangleFreeNeighbors G x).card ≤
      ∑ x, ((secondOrderDefectGraph G).connectedComponentMk x).supp.ncard := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ =>
    binarySquare_regular_mul_triangleFreeDegree_le_componentCard
      G hfree hq hreg hcard x

end Erdos85

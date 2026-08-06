import Proofs.Erdos85ConflictDegreeAccounting
import Proofs.Erdos85ConflictDefectDuality

/-!
# Degree stratification by order excess

For an edge-minimal `C₄`-free minimum-degree-`d` graph of order
`d(d-1)+1+q`, exact conflict-degree accounting turns the order excess `q`
into a pointwise budget on degree excess:

`(degree x - d) * (d - 1) ≤ q`.

Thus bands of width `d-1` above the Moore count admit only one additional
degree level at a time.
-/

namespace Erdos85

open SimpleGraph

/-- **Order excess controls degree excess.** -/
theorem degree_sub_mul_pred_le_order_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ}
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (x : V) :
    (G.degree x - d) * (d - 1) ≤ q := by
  by_cases hx : G.degree x = d
  · simp [hx]
  have hexact :=
    degree_commonNeighborConflict_eq_degree_mul_pred_of_nontight
      G hfree hcover x hx
  have hlt := (commonNeighborConflict G).degree_lt_card_verts x
  rw [hexact, hcard] at hlt
  have hxlow := hmin x
  have hsplit : G.degree x = (G.degree x - d) + d := by omega
  rw [hsplit] at hlt
  nlinarith

/-- The full stratification statement: before the `(k+1)`st excess block,
no degree can rise above `d+k`. -/
theorem degree_le_add_of_order_excess_lt_succ_mul_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d q k : ℕ}
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (hq : q < (k + 1) * (d - 1)) :
    ∀ x : V, G.degree x ≤ d + k := by
  intro x
  have hbudget := degree_sub_mul_pred_le_order_excess
    G hfree hmin hcover hcard x
  have hxlow := hmin x
  by_contra hx
  have hk : k + 1 ≤ G.degree x - d := by omega
  have hmul := Nat.mul_le_mul_right (d - 1) hk
  omega

/-- Below the first full `d-1` excess block, every vertex is tight. -/
theorem regular_of_order_excess_lt_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ}
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (hq : q < d - 1) :
    ∀ x : V, G.degree x = d := by
  intro x
  have hupper := degree_le_add_of_order_excess_lt_succ_mul_pred
    G hfree hmin hcover hcard (k := 0) (by simpa using hq) x
  have hxlow := hmin x
  omega

/-- Below the second full `d-1` excess block, only the two degree levels
`d` and `d+1` can occur. -/
theorem degree_le_succ_of_order_excess_lt_two_mul_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ}
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (hq : q < 2 * (d - 1)) :
    ∀ x : V, G.degree x ≤ d + 1 := by
  exact degree_le_add_of_order_excess_lt_succ_mul_pred
    G hfree hmin hcover hcard (k := 1) (by simpa using hq)

/-- **Exact defect-degree expenditure at a non-tight vertex.**  Raising the
original degree by one consumes exactly `d-1` of the order-excess degree in
the complementary second-order defect graph. -/
theorem secondOrderDefect_degree_add_degreeExcess_mul_pred_eq_orderExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ}
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (x : V) (hx : G.degree x ≠ d) :
    (secondOrderDefectGraph G).degree x +
        (G.degree x - d) * (d - 1) = q := by
  have hdual := commonNeighborConflict_compl_eq_secondOrderDefectGraph
    G hfree
  have hcompl := (commonNeighborConflict G).degree_compl x
  have hexact :=
    degree_commonNeighborConflict_eq_degree_mul_pred_of_nontight
      G hfree hcover x hx
  have hDdegree : (secondOrderDefectGraph G).degree x =
      ((commonNeighborConflict G)ᶜ).degree x := by
    rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      ← ((commonNeighborConflict G)ᶜ).card_neighborFinset_eq_degree]
    apply congrArg Finset.card
    ext y
    simp only [SimpleGraph.mem_neighborFinset]
    rw [hdual]
  rw [← hDdegree] at hcompl
  have hconfLt := (commonNeighborConflict G).degree_lt_card_verts x
  have hconfLe : (commonNeighborConflict G).degree x ≤
      Fintype.card V - 1 := by omega
  have hsum : (secondOrderDefectGraph G).degree x +
      (commonNeighborConflict G).degree x = Fintype.card V - 1 := by
    rw [hcompl]
    exact Nat.sub_add_cancel hconfLe
  have hxlow := hmin x
  have hsplit : G.degree x = (G.degree x - d) + d := by omega
  have hprod : G.degree x * (d - 1) =
      d * (d - 1) + (G.degree x - d) * (d - 1) := by
    calc
      G.degree x * (d - 1) =
          ((G.degree x - d) + d) * (d - 1) :=
        congrArg (fun z : ℕ ↦ z * (d - 1)) hsplit
      _ = d * (d - 1) + (G.degree x - d) * (d - 1) := by ring
  rw [hexact, hprod, hcard] at hsum
  omega

end Erdos85

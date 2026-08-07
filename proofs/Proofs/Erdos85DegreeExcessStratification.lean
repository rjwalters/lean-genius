import Proofs.Erdos85ConflictDegreeAccounting
import Proofs.Erdos85ConflictDefectDuality
import Proofs.Erdos85GadgetCounting
import Proofs.Erdos85MinimalWitness

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

private theorem two_mul_choose_two (k : ℕ) :
    2 * k.choose 2 = k * (k - 1) := by
  have h₁ : k.descFactorial 2 = 2 * k.choose 2 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    rfl
  have h₂ : k.descFactorial 2 = (k - 1) * k := by
    simp [Nat.descFactorial]
  rw [← h₁, h₂, Nat.mul_comm]

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

/-- Total degree excess among the neighbors of `x`. -/
def neighborDegreeExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (x : V) : ℕ :=
  ∑ y : {z : V // z ∈ G.neighborSet x}, (G.degree y.1 - d)

theorem neighborDegreeExcess_eq_sum_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) (x : V) :
    neighborDegreeExcess G d x =
      ∑ y ∈ G.neighborFinset x, (G.degree y - d) := by
  classical
  letI : Fintype {z : V // G.Adj x z} := Fintype.ofFinite _
  rw [neighborDegreeExcess,
    Finset.sum_subtype (G.neighborFinset x) (fun y ↦ G.mem_neighborFinset x y)]
  rfl

/-- **Local excess conservation.**  At order `d(d-1)+1+q`, the order
excess splits at every vertex into its defect degree, its own degree excess
weighted by `d-1`, and the degree excess carried by its neighbors.  No
edge-minimality assumption is needed for this identity. -/
theorem secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ} (hd : 1 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q)
    (x : V) :
    (secondOrderDefectGraph G).degree x +
        (G.degree x - d) * (d - 1) + neighborDegreeExcess G d x = q := by
  have hdual := commonNeighborConflict_compl_eq_secondOrderDefectGraph
    G hfree
  have hcompl := (commonNeighborConflict G).degree_compl x
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
  have hconflict :=
    degree_commonNeighborConflict_eq_sum_neighbor_degree_sub_one
      G hfree x
  have hterm : ∀ y : {z : V // z ∈ G.neighborSet x},
      G.degree y.1 - 1 = (d - 1) + (G.degree y.1 - d) := by
    intro y
    have := hmin y.1
    omega
  have hconflictSplit : (commonNeighborConflict G).degree x =
      G.degree x * (d - 1) + neighborDegreeExcess G d x := by
    rw [hconflict]
    calc
      (∑ y : {z : V // z ∈ G.neighborSet x},
          (G.degree y.1 - 1)) =
          ∑ y : {z : V // z ∈ G.neighborSet x},
            ((d - 1) + (G.degree y.1 - d)) := by
              apply Finset.sum_congr rfl
              intro y _
              exact hterm y
      _ = (∑ _y : {z : V // z ∈ G.neighborSet x}, (d - 1)) +
          ∑ y : {z : V // z ∈ G.neighborSet x},
            (G.degree y.1 - d) := by rw [Finset.sum_add_distrib]
      _ = G.degree x * (d - 1) + neighborDegreeExcess G d x := by
        rw [Finset.sum_const, Finset.card_univ,
          SimpleGraph.card_neighborSet_eq_degree]
        simp [neighborDegreeExcess]
  have hxlow := hmin x
  have hsplit : G.degree x = (G.degree x - d) + d := by omega
  have hprod : G.degree x * (d - 1) =
      d * (d - 1) + (G.degree x - d) * (d - 1) := by
    calc
      G.degree x * (d - 1) =
          ((G.degree x - d) + d) * (d - 1) :=
        congrArg (fun z : ℕ ↦ z * (d - 1)) hsplit
      _ = d * (d - 1) + (G.degree x - d) * (d - 1) := by ring
  rw [hconflictSplit, hprod, hcard] at hsum
  omega

/-- **Global excess conservation.**  Summing the local law counts neighbor
excess by incidences: every unit at `x` is seen once for each of its
`degree x` neighbors. -/
theorem sum_defectDegree_add_sum_weightedDegreeExcess_eq_card_mul_orderExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ} (hd : 1 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q) :
    (∑ x : V, (secondOrderDefectGraph G).degree x) +
        ∑ x : V, ((G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d)) = Fintype.card V * q := by
  have hneighbor : (∑ x : V, neighborDegreeExcess G d x) =
      ∑ x : V, G.degree x * (G.degree x - d) := by
    simp_rw [neighborDegreeExcess_eq_sum_neighborFinset]
    exact sum_neighbor_weight_eq_sum_degree_mul G
      (fun x ↦ G.degree x - d)
  calc
    (∑ x : V, (secondOrderDefectGraph G).degree x) +
          ∑ x : V, ((G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d)) =
        ∑ x : V, ((secondOrderDefectGraph G).degree x +
          (G.degree x - d) * (d - 1) + neighborDegreeExcess G d x) := by
            simp only [Finset.sum_add_distrib]
            rw [hneighbor]
            ac_rfl
    _ = ∑ _x : V, q := by
      apply Finset.sum_congr rfl
      intro x _
      exact secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
        G hfree hd hmin hcard x
    _ = Fintype.card V * q := by simp

/-- **Quadratic global normal form.**  Writing `s(x) = degree x - d`, the
global conservation law is

`2|E(D)| + (2d-1) ∑ s(x) + ∑ s(x)^2 = |V|q`.

The square term is the precise variance penalty hidden by the coarser total
irregularity estimate. -/
theorem two_mul_defectEdges_add_linearExcess_add_squareExcess_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ} (hd : 1 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q) :
    2 * (secondOrderDefectGraph G).edgeFinset.card +
        (2 * d - 1) * (∑ x : V, (G.degree x - d)) +
        ∑ x : V, (G.degree x - d) * (G.degree x - d) =
      Fintype.card V * q := by
  have hglobal :=
    sum_defectDegree_add_sum_weightedDegreeExcess_eq_card_mul_orderExcess
      G hfree hd hmin hcard
  have hedge :
      (∑ x : V, (secondOrderDefectGraph G).degree x) =
        2 * (secondOrderDefectGraph G).edgeFinset.card :=
    (secondOrderDefectGraph G).sum_degrees_eq_twice_card_edges
  have hpoint : ∀ x : V,
      (G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d) =
        (2 * d - 1) * (G.degree x - d) +
          (G.degree x - d) * (G.degree x - d) := by
    intro x
    have hx := hmin x
    have hdeg : G.degree x = (G.degree x - d) + d := by omega
    have hcoeff : (d - 1) + d = 2 * d - 1 := by omega
    calc
      (G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d) =
        (G.degree x - d) * (d - 1) +
          ((G.degree x - d) + d) * (G.degree x - d) := by rw [← hdeg]
      _ = ((d - 1) + d) * (G.degree x - d) +
          (G.degree x - d) * (G.degree x - d) := by ring
      _ = (2 * d - 1) * (G.degree x - d) +
          (G.degree x - d) * (G.degree x - d) := by rw [hcoeff]
  rw [hedge] at hglobal
  have hsum :
      (2 * d - 1) * (∑ x : V, (G.degree x - d)) +
          ∑ x : V, (G.degree x - d) * (G.degree x - d) =
        ∑ x : V, ((G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact (hpoint x).symm
  calc
    2 * (secondOrderDefectGraph G).edgeFinset.card +
          (2 * d - 1) * (∑ x : V, (G.degree x - d)) +
          ∑ x : V, (G.degree x - d) * (G.degree x - d) =
        2 * (secondOrderDefectGraph G).edgeFinset.card +
          ∑ x : V, ((G.degree x - d) * (d - 1) +
            G.degree x * (G.degree x - d)) := by
              rw [Nat.add_assoc, hsum]
    _ = Fintype.card V * q := hglobal

/-- **Triangular irregularity conservation.**  The quadratic normal form has
an exact halved interpretation: a vertex of excess `s` spends
`d*s + choose s 2` units in addition to each defect edge. -/
theorem two_mul_defectEdges_add_degreeExcess_add_chooseExcess_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ} (hd : 1 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q) :
    2 * ((secondOrderDefectGraph G).edgeFinset.card +
      d * (∑ x : V, (G.degree x - d)) +
      ∑ x : V, (G.degree x - d).choose 2) = Fintype.card V * q := by
  have hquad :=
    two_mul_defectEdges_add_linearExcess_add_squareExcess_eq
      G hfree hd hmin hcard
  have hlocal : ∀ s : ℕ,
      2 * (d * s + s.choose 2) = (2 * d - 1) * s + s * s := by
    intro s
    by_cases hs : s = 0
    · simp [hs]
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have hchoose := two_mul_choose_two (t + 1)
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.succ_sub_one] at hchoose
    have hcoeff : 2 * (d' + 1) - 1 = 2 * d' + 1 := by omega
    rw [hcoeff]
    calc
      2 * ((d' + 1) * (t + 1) + (t + 1).choose 2) =
          2 * ((d' + 1) * (t + 1)) + 2 * (t + 1).choose 2 := by ring
      _ = 2 * ((d' + 1) * (t + 1)) + (t + 1) * t := by rw [hchoose]
      _ = (2 * d' + 1) * (t + 1) + (t + 1) * (t + 1) := by ring
  have hsum :
      2 * (d * (∑ x : V, (G.degree x - d)) +
          ∑ x : V, (G.degree x - d).choose 2) =
        (2 * d - 1) * (∑ x : V, (G.degree x - d)) +
          ∑ x : V, (G.degree x - d) * (G.degree x - d) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact hlocal (G.degree x - d)
  calc
    2 * ((secondOrderDefectGraph G).edgeFinset.card +
        d * (∑ x : V, (G.degree x - d)) +
        ∑ x : V, (G.degree x - d).choose 2) =
      2 * (secondOrderDefectGraph G).edgeFinset.card +
        2 * (d * (∑ x : V, (G.degree x - d)) +
          ∑ x : V, (G.degree x - d).choose 2) := by ring
    _ = 2 * (secondOrderDefectGraph G).edgeFinset.card +
        (2 * d - 1) * (∑ x : V, (G.degree x - d)) +
        ∑ x : V, (G.degree x - d) * (G.degree x - d) := by
          rw [Nat.add_assoc, hsum]
    _ = Fintype.card V * q := hquad

/-- **Total irregularity bound.**  Every unit of degree excess consumes at
least `2d` units of the global order-excess budget. -/
theorem two_mul_degree_mul_sum_degreeExcess_le_card_mul_orderExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ} (hd : 1 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q) :
    2 * d * (∑ x : V, (G.degree x - d)) ≤ Fintype.card V * q := by
  have hglobal :=
    sum_defectDegree_add_sum_weightedDegreeExcess_eq_card_mul_orderExcess
      G hfree hd hmin hcard
  have hweighted :
      (∑ x : V, ((G.degree x - d) * (d - 1) +
        G.degree x * (G.degree x - d))) ≤ Fintype.card V * q := by
    omega
  have hpoint : ∀ x : V,
      2 * d * (G.degree x - d) ≤
        (G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d) := by
    intro x
    let s := G.degree x - d
    have hx := hmin x
    have hdeg : G.degree x = s + d := by
      dsimp [s]
      omega
    by_cases hs : s = 0
    · simp [s, hs]
    obtain ⟨d', hdEq⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨s', hsEq⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [show G.degree x - d = s by rfl, hdeg, hdEq, hsEq]
    simp only [Nat.add_sub_cancel]
    nlinarith [Nat.zero_le (s' * s')]
  calc
    2 * d * (∑ x : V, (G.degree x - d)) =
        ∑ x : V, 2 * d * (G.degree x - d) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ x : V, ((G.degree x - d) * (d - 1) +
        G.degree x * (G.degree x - d)) :=
      Finset.sum_le_sum fun x _ ↦ hpoint x
    _ ≤ Fintype.card V * q := hweighted

/-- **Defect-edge/irregular-vertex tradeoff.**  Each defect edge consumes two
units of the global excess budget, while every vertex above the target degree
consumes at least `2d`.  Thus irregularity and residual defect structure cannot
both be large. -/
theorem two_mul_defectEdges_add_two_mul_degree_mul_card_aboveMin_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d q : ℕ} (hd : 1 ≤ d)
    (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * (d - 1) + 1 + q) :
    2 * (secondOrderDefectGraph G).edgeFinset.card +
        2 * d * (aboveMinVertices G d).card ≤ Fintype.card V * q := by
  classical
  have hglobal :=
    sum_defectDegree_add_sum_weightedDegreeExcess_eq_card_mul_orderExcess
      G hfree hd hmin hcard
  have hedge :
      (∑ x : V, (secondOrderDefectGraph G).degree x) =
        2 * (secondOrderDefectGraph G).edgeFinset.card :=
    (secondOrderDefectGraph G).sum_degrees_eq_twice_card_edges
  have hpoint : ∀ x : V,
      2 * d * (G.degree x - d) ≤
        (G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d) := by
    intro x
    let s := G.degree x - d
    have hx := hmin x
    have hdeg : G.degree x = s + d := by
      dsimp [s]
      omega
    by_cases hs : s = 0
    · simp [s, hs]
    obtain ⟨d', hdEq⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨s', hsEq⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [show G.degree x - d = s by rfl, hdeg, hdEq, hsEq]
    simp only [Nat.add_sub_cancel]
    nlinarith [Nat.zero_le (s' * s')]
  have habove : (aboveMinVertices G d).card ≤
      ∑ x : V, (G.degree x - d) := by
    calc
      (aboveMinVertices G d).card =
          ∑ x ∈ aboveMinVertices G d, 1 := by simp
      _ ≤ ∑ x ∈ aboveMinVertices G d, (G.degree x - d) := by
        apply Finset.sum_le_sum
        intro x hx
        have hx' : d < G.degree x := by
          simpa [aboveMinVertices] using hx
        omega
      _ ≤ ∑ x : V, (G.degree x - d) := by
        exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hweighted :
      2 * d * (∑ x : V, (G.degree x - d)) ≤
        ∑ x : V, ((G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d)) := by
    calc
      2 * d * (∑ x : V, (G.degree x - d)) =
          ∑ x : V, 2 * d * (G.degree x - d) := by
            rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun x _ ↦ hpoint x
  have haboveWeighted :
      2 * d * (aboveMinVertices G d).card ≤
        ∑ x : V, ((G.degree x - d) * (d - 1) +
          G.degree x * (G.degree x - d)) :=
    (Nat.mul_le_mul_left (2 * d) habove).trans hweighted
  rw [hedge] at hglobal
  omega

end Erdos85

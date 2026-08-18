import Proofs.Erdos85HighRootZeroSlack

/-!
# The high-root incidence kernel at square order

At a saturated degree-`d+1` root `v` of a `d^2`-vertex `C4`-free graph,
every other vertex has exactly one neighbour in `N(v)`.  Consequently the
two-valued vector which is `1-d` on `N(v)` and `1` off `N(v)` is killed by
every adjacency row except the row at `v`.  This is the integral source of
the binary and `d`-modular kernels used in the square-order code approach.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The two-valued high-root incidence vector. -/
def squareOrderHighRootWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (v : V) : V → ℤ :=
  fun x => if G.Adj v x then 1 - (d : ℤ) else 1

/-- A saturated square-order high root has exactly one common neighbour
with every other vertex. -/
theorem squareOrder_card_common_highRoot_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d) {v x : V}
    (hv : G.degree v = d + 1) (hvx : v ≠ x) :
    (G.neighborFinset v ∩ G.neighborFinset x).card = 1 := by
  have hDzero :=
    (squareOrder_degree_succ_highRoot_structure
      G hfree hd hmin hcard hv).1
  have hDempty : (secondOrderDefectGraph G).neighborFinset v = ∅ := by
    rw [← Finset.card_eq_zero,
      (secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDzero]
  rw [card_common_eq_if_secondOrderDefect G hfree v x hvx]
  simp [hDempty]

/-- Weighted neighbour sum form of the high-root kernel identity. -/
theorem sum_squareOrderHighRootWeight_over_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1)
    (hdegree : ∀ {x : V}, x ≠ v → G.degree x = d) (x : V) :
    (∑ y ∈ G.neighborFinset x, squareOrderHighRootWeight G d v y) =
      if x = v then 1 - (d : ℤ) ^ 2 else 0 := by
  classical
  by_cases hxv : x = v
  · subst x
    rw [if_pos rfl]
    have hall : ∀ y ∈ G.neighborFinset v,
        squareOrderHighRootWeight G d v y = 1 - (d : ℤ) := by
      intro y hy
      simp [squareOrderHighRootWeight,
        (G.mem_neighborFinset v y).mp hy]
    calc
      (∑ y ∈ G.neighborFinset v, squareOrderHighRootWeight G d v y) =
          ∑ _y ∈ G.neighborFinset v, (1 - (d : ℤ)) := by
            apply Finset.sum_congr rfl
            exact hall
      _ = ((d + 1 : ℕ) : ℤ) * (1 - (d : ℤ)) := by
        rw [Finset.sum_const, G.card_neighborFinset_eq_degree, hv]
        simp
      _ = 1 - (d : ℤ) ^ 2 := by
        push_cast
        ring
  · rw [if_neg hxv]
    have hdeg : G.degree x = d := hdegree hxv
    have hcommon :
        (G.neighborFinset x ∩ G.neighborFinset v).card = 1 := by
      rw [Finset.inter_comm]
      exact squareOrder_card_common_highRoot_eq_one
        G hfree hd hmin hcard hv (Ne.symm hxv)
    simp only [squareOrderHighRootWeight]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := G.neighborFinset x) (p := fun y => G.Adj v y)]
    have hinter :
        (G.neighborFinset x).filter (fun y => G.Adj v y) =
          G.neighborFinset x ∩ G.neighborFinset v := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    have hfilterCard :
        ((G.neighborFinset x).filter fun y => G.Adj v y).card = 1 := by
      rw [hinter, hcommon]
    have hnotCard :
        ((G.neighborFinset x).filter fun y => ¬ G.Adj v y).card = d - 1 := by
      have hpartition := Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset x) (p := fun y => G.Adj v y)
      rw [hfilterCard, G.card_neighborFinset_eq_degree, hdeg] at hpartition
      omega
    have hsumPos :
        (∑ y ∈ (G.neighborFinset x).filter (fun y => G.Adj v y),
          if G.Adj v y then 1 - (d : ℤ) else 1) =
          ∑ _y ∈ (G.neighborFinset x).filter (fun y => G.Adj v y),
            (1 - (d : ℤ)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [if_pos (Finset.mem_filter.mp hy).2]
    have hsumNeg :
        (∑ y ∈ (G.neighborFinset x).filter (fun y => ¬ G.Adj v y),
          if G.Adj v y then 1 - (d : ℤ) else 1) =
          ∑ _y ∈ (G.neighborFinset x).filter (fun y => ¬ G.Adj v y),
            (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [if_neg (Finset.mem_filter.mp hy).2]
    rw [hsumPos, hsumNeg]
    rw [Finset.sum_const, Finset.sum_const, hfilterCard, hnotCard]
    simp only [nsmul_eq_mul]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    ring

/-- Matrix form: adjacency sends the high-root incidence vector to the
single coordinate `(1-d^2)e_v`. -/
theorem adjMatrix_mulVec_squareOrderHighRootWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1)
    (hdegree : ∀ {x : V}, x ≠ v → G.degree x = d) :
    (G.adjMatrix ℤ).mulVec (squareOrderHighRootWeight G d v) =
      fun x => if x = v then 1 - (d : ℤ) ^ 2 else 0 := by
  funext x
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  exact sum_squareOrderHighRootWeight_over_neighbors
    G hfree hd hmin hcard hv hdegree x

end

end Erdos85

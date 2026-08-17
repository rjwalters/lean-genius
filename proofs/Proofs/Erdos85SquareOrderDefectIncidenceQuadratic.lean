import Proofs.Erdos85SquareOrderDefectEigenvectors

/-!
# The two-dimensional defect-incidence quotient at square order

The low-sector indicator `ℓ` and the high-incidence vector `k` span an
invariant sector for the defect adjacency operator:

`Dℓ = (d - 1)ℓ - k` and `Dk = hℓ - k`.

Consequently `k` is killed by
`D² - (d - 2)D + (h - d + 1)I`, whose discriminant is `d² - 4h`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def squareOrderLowIndicatorRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : V → ℚ :=
  fun x => if G.degree x = d then 1 else 0

def squareOrderHighIncidenceRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : V → ℚ :=
  fun x => squareOrderHighIncidenceCount G d x

theorem squareOrder_defect_mulVec_highIncidenceRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec
        (squareOrderHighIncidenceRat G d) =
      (squareOrderHighVertices G d).card • squareOrderLowIndicatorRat G d -
        squareOrderHighIncidenceRat G d := by
  classical
  funext y
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard y with hy | hy
  · rw [SimpleGraph.adjMatrix_mulVec_apply]
    have hlocal := squareOrder_sum_highIncidence_over_defectNeighbors_add_self
      G hfree hd hmin hcard hy
    change
      (∑ x ∈ (secondOrderDefectGraph G).neighborFinset y,
          (squareOrderHighIncidenceCount G d x : ℚ)) =
        (squareOrderHighVertices G d).card *
            squareOrderLowIndicatorRat G d y -
          squareOrderHighIncidenceRat G d y
    simp only [squareOrderLowIndicatorRat, squareOrderHighIncidenceRat, hy,
      if_pos, mul_one]
    have hlocalQ := congrArg (fun n : ℕ => (n : ℚ)) hlocal
    push_cast at hlocalQ
    linarith
  · have hyDdegree : (secondOrderDefectGraph G).degree y = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree hd hmin hcard hy).1
    have hyD : (secondOrderDefectGraph G).neighborFinset y = ∅ := by
      rw [← Finset.card_eq_zero,
        (secondOrderDefectGraph G).card_neighborFinset_eq_degree, hyDdegree]
    have hyIncidence : squareOrderHighIncidenceCount G d y = 0 :=
      squareOrder_highNeighborCount_eq_zero_of_high G hcover
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    simp [hyD, squareOrderLowIndicatorRat, squareOrderHighIncidenceRat,
      hy, hyIncidence]

theorem squareOrder_defect_mulVec_lowIndicatorRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec
        (squareOrderLowIndicatorRat G d) =
      (d - 1 : ℕ) • squareOrderLowIndicatorRat G d -
        squareOrderHighIncidenceRat G d := by
  classical
  let D := secondOrderDefectGraph G
  funext y
  rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree hd hmin hcover hcard y with hy | hy
  · have hneighborLow : ∀ x ∈ D.neighborFinset y, G.degree x = d := by
      intro x hx
      rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
          G hfree hd hmin hcover hcard x with hxlow | hxhigh
      · exact hxlow
      · have hxzero : D.degree x = 0 :=
          (squareOrder_degree_succ_highRoot_structure
            G hfree hd hmin hcard hxhigh).1
        have hxy : D.Adj x y := by
          simpa [SimpleGraph.mem_neighborFinset, D.adj_comm] using hx
        have : 0 < D.degree x :=
          (D.degree_pos_iff_exists_adj x).mpr ⟨y, hxy⟩
        omega
    have hdegree := squareOrder_defectDegree_add_highIncidence_eq_pred
      G hfree hd hmin hcover hcard hy
    change D.degree y + squareOrderHighIncidenceCount G d y = d - 1 at hdegree
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    change
      (∑ x ∈ D.neighborFinset y, squareOrderLowIndicatorRat G d x) =
        (d - 1 : ℕ) * squareOrderLowIndicatorRat G d y -
          squareOrderHighIncidenceRat G d y
    have hsum :
        (∑ x ∈ D.neighborFinset y, squareOrderLowIndicatorRat G d x) =
          (D.degree y : ℚ) := by
      calc
        _ = ∑ _x ∈ D.neighborFinset y, (1 : ℚ) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [squareOrderLowIndicatorRat, hneighborLow x hx]
        _ = (D.degree y : ℚ) := by simp [D.card_neighborFinset_eq_degree]
    rw [hsum]
    simp only [squareOrderLowIndicatorRat, squareOrderHighIncidenceRat, hy,
      if_pos, Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one,
      mul_one]
    have hdegreeQ := congrArg (fun n : ℕ => (n : ℚ)) hdegree
    push_cast at hdegreeQ
    rw [Nat.cast_sub (by omega : 1 ≤ d)] at hdegreeQ
    norm_num at hdegreeQ
    linarith
  · have hyDdegree : D.degree y = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree hd hmin hcard hy).1
    have hyD : D.neighborFinset y = ∅ := by
      rw [← Finset.card_eq_zero, D.card_neighborFinset_eq_degree, hyDdegree]
    have hyIncidence : squareOrderHighIncidenceCount G d y = 0 :=
      squareOrder_highNeighborCount_eq_zero_of_high G hcover
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    change
      (∑ x ∈ D.neighborFinset y, squareOrderLowIndicatorRat G d x) =
        (d - 1 : ℕ) * squareOrderLowIndicatorRat G d y -
          squareOrderHighIncidenceRat G d y
    rw [hyD]
    simp [squareOrderLowIndicatorRat, squareOrderHighIncidenceRat,
      hy, hyIncidence]

theorem squareOrder_defect_incidence_quadratic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ y : V, d ≤ G.degree y)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let k := squareOrderHighIncidenceRat G d
    let h := (squareOrderHighVertices G d).card
    D.mulVec (D.mulVec k) - (d - 2 : ℕ) • D.mulVec k +
        (h + 1 - d : ℤ) • k = 0 := by
  classical
  let D := (secondOrderDefectGraph G).adjMatrix ℚ
  let ell := squareOrderLowIndicatorRat G d
  let k := squareOrderHighIncidenceRat G d
  let h := (squareOrderHighVertices G d).card
  dsimp only
  have hk := squareOrder_defect_mulVec_highIncidenceRat
    G hfree hd hmin hcover hcard
  have hell := squareOrder_defect_mulVec_lowIndicatorRat
    G hfree hd hmin hcover hcard
  change D.mulVec k = h • ell - k at hk
  change D.mulVec ell = (d - 1 : ℕ) • ell - k at hell
  rw [hk, Matrix.mulVec_sub, Matrix.mulVec_smul, hell, hk]
  funext x
  have hdq : ((d - 2 : ℕ) : ℚ) = (d : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ d)]
    norm_num
  have hd1q : ((d - 1 : ℕ) : ℚ) = (d : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  simp only [Pi.sub_apply, Pi.add_apply, nsmul_eq_mul, zsmul_eq_mul,
    Pi.mul_apply, Pi.natCast_apply, Pi.intCast_apply]
  rw [hdq, hd1q]
  push_cast
  simp only [k, h, Pi.zero_apply]
  ring

end

end Erdos85

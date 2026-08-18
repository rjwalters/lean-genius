import Proofs.Erdos85SquareOrderCommutatorRowCount

/-!
# The high-sector Gram matrix of the square-order commutator

For a high vertex, the commutator row is the indicator of its low
nonneighbors. Two distinct high vertices have exactly one common neighbor,
so their row inner product can also be counted exactly.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem squareOrder_sum_commutator_row_mul_of_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a b : V}
    (ha : a ∈ squareOrderHighVertices G d)
    (hb : b ∈ squareOrderHighVertices G d) :
    let H := squareOrderHighVertices G d
    let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
    (∑ y : V, C a y * C b y) =
      if a = b then ((d * d - H.card - (d + 1) : Nat) : ℤ)
      else ((d * d - H.card - (2 * d + 1) : Nat) : ℤ) := by
  classical
  let H := squareOrderHighVertices G d
  let C := G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ -
    (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ
  dsimp only
  by_cases hab : a = b
  · subst b
    rw [if_pos rfl]
    simpa [C, H, ha] using
      squareOrder_sum_commutator_entry_sq_row
        G hfree hd hmin hcover hcard a
  · rw [if_neg hab]
    have haDegree : G.degree a = d + 1 := (Finset.mem_filter.mp ha).2
    have hbDegree : G.degree b = d + 1 := (Finset.mem_filter.mp hb).2
    have hentry : ∀ x ∈ H, ∀ y : V, C x y =
        if y ∉ H ∧ ¬ G.Adj x y then 1 else 0 := by
      intro x hx y
      rw [show C x y = ((G.degree x : ℤ) - G.degree y) *
          (1 - G.adjMatrix ℤ x y) by
        simpa [C] using
          adjMatrix_secondOrderDefect_commutator_apply G hfree x y]
      have hxDegree : G.degree x = d + 1 := (Finset.mem_filter.mp hx).2
      by_cases hy : y ∈ H
      · have hyDegree : G.degree y = d + 1 := (Finset.mem_filter.mp hy).2
        simp [hy, hxDegree, hyDegree]
      · have hyDegree : G.degree y = d := by
          rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
              G hfree hd hmin hcover hcard y with hyd | hyd
          · exact hyd
          · exact (hy (Finset.mem_filter.mpr ⟨by simp, hyd⟩)).elim
        by_cases hxy : G.Adj x y
        · simp [hy, hxy, hxDegree, hyDegree, SimpleGraph.adjMatrix_apply]
        · simp [hy, hxy, hxDegree, hyDegree, SimpleGraph.adjMatrix_apply]
    have hsum : (∑ y : V, C a y * C b y) =
        (((Finset.univ : Finset V).filter
          fun y => y ∉ H ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y).card : ℤ) := by
      calc
        _ = ∑ y : V,
            if y ∉ H ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro y _hy
          rw [hentry a ha y, hentry b hb y]
          split_ifs <;> simp_all
        _ = _ := by
          simpa using
            (Finset.sum_boole (R := ℤ)
              (fun y : V => y ∉ H ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y)
              Finset.univ)
    rw [hsum]
    congr 1
    let L : Finset V := Finset.univ \ H
    let Na : Finset V := G.neighborFinset a
    let Nb : Finset V := G.neighborFinset b
    have haSub : Na ⊆ L := by
      intro y hy
      refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
      intro hyH
      exact squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
        haDegree (Finset.mem_filter.mp hyH).2
        ((G.mem_neighborFinset a y).mp hy)
    have hbSub : Nb ⊆ L := by
      intro y hy
      refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
      intro hyH
      exact squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
        hbDegree (Finset.mem_filter.mp hyH).2
        ((G.mem_neighborFinset b y).mp hy)
    have hunionSub : Na ∪ Nb ⊆ L := Finset.union_subset haSub hbSub
    have hfilter :
        (Finset.univ.filter
          fun y : V => y ∉ H ∧ ¬ G.Adj a y ∧ ¬ G.Adj b y) =
          L \ (Na ∪ Nb) := by
      ext y
      simp [L, Na, Nb, SimpleGraph.mem_neighborFinset]
    rw [hfilter, Finset.card_sdiff_of_subset hunionSub]
    have hLcard : L.card = d * d - H.card := by
      dsimp [L]
      rw [Finset.card_sdiff, Finset.card_univ, hcard]
      simp
    have hinter : (Na ∩ Nb).card = 1 := by
      simpa [Na, Nb] using
        squareOrder_card_common_degree_succ_eq_one
          G hfree hd hmin hcover hcard haDegree hbDegree hab
    have hNa : Na.card = d + 1 := by
      simpa [Na, G.card_neighborFinset_eq_degree] using haDegree
    have hNb : Nb.card = d + 1 := by
      simpa [Nb, G.card_neighborFinset_eq_degree] using hbDegree
    have hunion : (Na ∪ Nb).card = 2 * d + 1 := by
      have hcount := Finset.card_union_add_card_inter Na Nb
      omega
    rw [hLcard, hunion]

end

end Erdos85

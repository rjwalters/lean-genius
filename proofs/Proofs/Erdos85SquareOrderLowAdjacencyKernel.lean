import Proofs.Erdos85SquareOrderHighIncidence
import Proofs.Erdos85SquareOrderHighRootKernel

/-!
# High-incidence differences in the low adjacency kernel

For a square-order high vertex `a`, every distinct vertex has exactly one
common neighbor with `a`.  All neighbors of `a` are low under the tight edge
cover.  Hence the low adjacency matrix sends every high incidence column to
the all-ones vector, and kills every difference of two such columns.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The common neighbor of a high vertex and a low vertex is itself low. -/
theorem squareOrder_card_low_common_high_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a x : V} (ha : a ∈ squareOrderHighVertices G d)
    (hx : x ∉ squareOrderHighVertices G d) :
    let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
    (G.neighborFinset x ∩ G.neighborFinset a ∩ L).card = 1 := by
  classical
  let H := squareOrderHighVertices G d
  let L := (Finset.univ : Finset V) \ H
  have hadegree : G.degree a = d + 1 := (Finset.mem_filter.mp ha).2
  have hxa : x ≠ a := by
    intro h
    subst x
    exact hx ha
  have hcommon :
      (G.neighborFinset x ∩ G.neighborFinset a).card = 1 := by
    rw [Finset.inter_comm]
    exact squareOrder_card_common_highRoot_eq_one
      G hfree hd hmin hcard hadegree (Ne.symm hxa)
  have hneighborsLow : G.neighborFinset a ⊆ L := by
    intro y hy
    refine Finset.mem_sdiff.mpr ⟨by simp, ?_⟩
    intro hyhigh
    have hydegree : G.degree y = d + 1 :=
      (Finset.mem_filter.mp hyhigh).2
    have hn := squareOrder_not_adj_degree_succ_of_tightEdgeCover
      G hcover hadegree hydegree
    exact hn ((G.mem_neighborFinset a y).mp hy)
  have hinter :
      G.neighborFinset x ∩ G.neighborFinset a ∩ L =
        G.neighborFinset x ∩ G.neighborFinset a := by
    apply Finset.inter_eq_left.mpr
    intro y hy
    exact hneighborsLow (Finset.mem_inter.mp hy).2
  simpa [H, L, hinter] using hcommon

/-- Integral pointwise form of `L B = J`: summing the adjacency product over
the low sector gives one for every low row and high column. -/
theorem squareOrder_sum_low_adj_mul_high_incidence_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a x : V} (ha : a ∈ squareOrderHighVertices G d)
    (hx : x ∉ squareOrderHighVertices G d) :
    let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
    (∑ y ∈ L, G.adjMatrix ℤ x y * G.adjMatrix ℤ y a) = 1 := by
  classical
  let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
  have hc := squareOrder_card_low_common_high_eq_one
    G hfree hd hmin hcover hcard ha hx
  dsimp only at hc ⊢
  have hsets :
      ((Finset.univ : Finset V) \ squareOrderHighVertices G d).filter
          (fun y => G.Adj x y ∧ G.Adj y a) =
        G.neighborFinset x ∩ G.neighborFinset a ∩
          ((Finset.univ : Finset V) \ squareOrderHighVertices G d) := by
    ext y
    simp [G.adj_comm, and_comm, and_assoc]
  simp only [SimpleGraph.adjMatrix_apply]
  simp_rw [ite_mul, one_mul, zero_mul]
  have hterm : ∀ y : V,
      (if G.Adj x y then if G.Adj y a then (1 : ℤ) else 0 else 0) =
        if G.Adj x y ∧ G.Adj y a then 1 else 0 := by
    intro y
    split_ifs <;> simp_all
  simp_rw [hterm, Finset.sum_boole, hsets]
  exact_mod_cast hc

/-- Every difference of two high incidence columns is killed pointwise by
the low adjacency matrix. -/
theorem squareOrder_sum_low_adj_mul_high_incidence_sub_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a b x : V} (ha : a ∈ squareOrderHighVertices G d)
    (hb : b ∈ squareOrderHighVertices G d)
    (hx : x ∉ squareOrderHighVertices G d) :
    let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
    (∑ y ∈ L, G.adjMatrix ℤ x y *
      (G.adjMatrix ℤ y a - G.adjMatrix ℤ y b)) = 0 := by
  classical
  let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
  have haone := squareOrder_sum_low_adj_mul_high_incidence_eq_one
    G hfree hd hmin hcover hcard ha hx
  have hbone := squareOrder_sum_low_adj_mul_high_incidence_eq_one
    G hfree hd hmin hcover hcard hb hx
  dsimp only at haone hbone ⊢
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  omega

end

end Erdos85

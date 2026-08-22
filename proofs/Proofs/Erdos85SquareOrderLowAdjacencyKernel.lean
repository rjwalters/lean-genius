import Proofs.Erdos85SquareOrderHighIncidence
import Proofs.Erdos85SquareOrderHighRootKernel
import Proofs.Erdos85SquareOrderDefectEigenvectors

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

/-- Difference of two high-incidence columns, restricted to the low sector. -/
def squareOrderLowHighIncidenceDifference
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (a b : V) :
    (((Finset.univ : Finset V) \ squareOrderHighVertices G d : Finset V) :
      Set V) → ℤ :=
  fun x ↦ G.adjMatrix ℤ x.1 a - G.adjMatrix ℤ x.1 b

/-- Rational version of the low-sector high-incidence difference. -/
def squareOrderLowHighIncidenceDifferenceRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (a b : V) :
    (((Finset.univ : Finset V) \ squareOrderHighVertices G d : Finset V) :
      Set V) → ℚ :=
  fun x ↦ G.adjMatrix ℚ x.1 a - G.adjMatrix ℚ x.1 b

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

/-- Operator form: every high-incidence difference lies in the kernel of
the adjacency matrix induced on the low sector. -/
theorem squareOrder_lowAdjacency_mulVec_highIncidenceDifference_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a b : V} (ha : a ∈ squareOrderHighVertices G d)
    (hb : b ∈ squareOrderHighVertices G d) :
    let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
    ((G.induce (L : Set V)).adjMatrix ℤ).mulVec
      (squareOrderLowHighIncidenceDifference G d a b) = 0 := by
  classical
  let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
  funext x
  have hxlow : x.1 ∉ squareOrderHighVertices G d :=
    (Finset.mem_sdiff.mp x.2).2
  have hzero := squareOrder_sum_low_adj_mul_high_incidence_sub_eq_zero
    G hfree hd hmin hcover hcard ha hb hxlow
  dsimp only at hzero
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply,
    squareOrderLowHighIncidenceDifference]
  change (∑ y : (L : Set V),
      G.adjMatrix ℤ x.1 y.1 *
        (G.adjMatrix ℤ y.1 a - G.adjMatrix ℤ y.1 b)) = 0
  exact (Finset.sum_subtype L (fun _ ↦ Iff.rfl)
    (fun y : V ↦ G.adjMatrix ℤ x.1 y *
      (G.adjMatrix ℤ y a - G.adjMatrix ℤ y b))).symm.trans hzero

/-- Rational operator form of the low-adjacency kernel identity. -/
theorem squareOrder_lowAdjacency_mulVec_highIncidenceDifferenceRat_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a b : V} (ha : a ∈ squareOrderHighVertices G d)
    (hb : b ∈ squareOrderHighVertices G d) :
    let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
    ((G.induce (L : Set V)).adjMatrix ℚ).mulVec
      (squareOrderLowHighIncidenceDifferenceRat G d a b) = 0 := by
  classical
  let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
  funext x
  have hxlow : x.1 ∉ squareOrderHighVertices G d :=
    (Finset.mem_sdiff.mp x.2).2
  have hzero := squareOrder_sum_low_adj_mul_high_incidence_sub_eq_zero
    G hfree hd hmin hcover hcard ha hb hxlow
  dsimp only at hzero
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply,
    squareOrderLowHighIncidenceDifferenceRat]
  change (∑ y : (L : Set V),
      G.adjMatrix ℚ x.1 y.1 *
        (G.adjMatrix ℚ y.1 a - G.adjMatrix ℚ y.1 b)) = 0
  have hzeroQ : (∑ y ∈ L, G.adjMatrix ℚ x.1 y *
      (G.adjMatrix ℚ y a - G.adjMatrix ℚ y b)) = 0 := by
    have hc := congrArg (fun z : ℤ ↦ (z : ℚ)) hzero
    simpa [L, SimpleGraph.adjMatrix_apply] using hc
  exact (Finset.sum_subtype L (fun _ ↦ Iff.rfl)
    (fun y : V ↦ G.adjMatrix ℚ x.1 y *
      (G.adjMatrix ℚ y a - G.adjMatrix ℚ y b))).symm.trans hzeroQ

private def extendLowFunction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    ((((Finset.univ : Finset V) \ squareOrderHighVertices G d : Finset V) :
      Set V) → ℤ) →ₗ[ℤ] (V → ℤ) where
  toFun f x := if hx : x ∉ squareOrderHighVertices G d then
    f ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩ else 0
  map_add' f g := by
    funext x
    by_cases hx : x ∈ squareOrderHighVertices G d <;> simp [hx]
  map_smul' r f := by
    funext x
    by_cases hx : x ∈ squareOrderHighVertices G d <;> simp [hx]

private def extendLowFunctionRat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    ((((Finset.univ : Finset V) \ squareOrderHighVertices G d : Finset V) :
      Set V) → ℚ) →ₗ[ℚ] (V → ℚ) where
  toFun f x := if hx : x ∉ squareOrderHighVertices G d then
    f ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩⟩ else 0
  map_add' f g := by
    funext x
    by_cases hx : x ∈ squareOrderHighVertices G d <;> simp [hx]
  map_smul' r f := by
    funext x
    by_cases hx : x ∈ squareOrderHighVertices G d <;> simp [hx]

/-- The low-adjacency kernel contains `|H|-1` independent incidence
differences: after choosing a high base vertex, all other high columns give
an independent kernel family. -/
theorem squareOrder_lowHighIncidenceDifferences_linearIndependent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (a : ↥(squareOrderHighVertices G d)) :
    LinearIndependent ℤ
      (fun b : {x : ↥(squareOrderHighVertices G d) // x ≠ a} ↦
        squareOrderLowHighIncidenceDifference G d b.1.1 a.1) := by
  classical
  let E := extendLowFunction G d
  apply LinearIndependent.of_comp E
  have hfull := squareOrder_highRowDifferences_linearIndependent
    G hfree hd hmin hcover hcard a
  convert hfull using 1
  funext b
  ext x
  by_cases hxlow : x ∈ ((Finset.univ : Finset V) \
      squareOrderHighVertices G d)
  · have hxnot : x ∉ squareOrderHighVertices G d :=
      (Finset.mem_sdiff.mp hxlow).2
    simp [E, extendLowFunction, squareOrderLowHighIncidenceDifference,
      squareOrderHighRowDifference, hxnot, G.adj_comm]
  · have hxhigh : x ∈ squareOrderHighVertices G d := by
      simpa using hxlow
    have hbhigh : b.1.1 ∈ squareOrderHighVertices G d := b.1.2
    have habase : a.1 ∈ squareOrderHighVertices G d := a.2
    have hxb : ¬G.Adj x b.1.1 :=
      squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
        (Finset.mem_filter.mp hxhigh).2 (Finset.mem_filter.mp hbhigh).2
    have hxa : ¬G.Adj x a.1 :=
      squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
        (Finset.mem_filter.mp hxhigh).2 (Finset.mem_filter.mp habase).2
    simp [E, extendLowFunction, squareOrderHighRowDifference, hxhigh,
      SimpleGraph.adjMatrix_apply,
      hxb, hxa, G.adj_comm]

/-- The rational low-incidence differences based at a high vertex are
linearly independent. -/
theorem squareOrder_lowHighIncidenceDifferencesRat_linearIndependent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    LinearIndependent ℚ
      (fun b : {x // x ∈ (squareOrderHighVertices G d).erase a} ↦
        squareOrderLowHighIncidenceDifferenceRat G d b.1 a) := by
  classical
  let E := extendLowFunctionRat G d
  apply LinearIndependent.of_comp E
  have hfull := squareOrder_highRowDifferencesRat_linearIndependent
    G hfree hd hmin hcard ha
  convert hfull using 1
  funext b
  ext x
  by_cases hxlow : x ∈ ((Finset.univ : Finset V) \
      squareOrderHighVertices G d)
  · have hxnot : x ∉ squareOrderHighVertices G d :=
      (Finset.mem_sdiff.mp hxlow).2
    simp [E, extendLowFunctionRat, squareOrderLowHighIncidenceDifferenceRat,
      squareOrderHighRowDifferenceRat, hxnot, G.adj_comm]
  · have hxhigh : x ∈ squareOrderHighVertices G d := by
      simpa using hxlow
    have hbhigh : b.1 ∈ squareOrderHighVertices G d :=
      Finset.mem_of_mem_erase b.2
    have hxb : ¬G.Adj x b.1 :=
      squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
        (Finset.mem_filter.mp hxhigh).2 (Finset.mem_filter.mp hbhigh).2
    have hxa : ¬G.Adj x a :=
      squareOrder_not_adj_degree_succ_of_tightEdgeCover G hcover
        (Finset.mem_filter.mp hxhigh).2 (Finset.mem_filter.mp ha).2
    have hax : ¬G.Adj a x := fun hax => hxa ((G.adj_comm a x).mp hax)
    simp [E, extendLowFunctionRat, squareOrderHighRowDifferenceRat, hxhigh,
      SimpleGraph.adjMatrix_apply, hxb, hax, G.adj_comm]

/-- Quantitative low-block consequence: its rational adjacency nullity is at
least the number of high vertices minus one. -/
theorem squareOrder_high_card_sub_one_le_finrank_lowAdjacency_ker
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    {a : V} (ha : a ∈ squareOrderHighVertices G d) :
    let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
    (squareOrderHighVertices G d).card - 1 ≤ Module.finrank ℚ
      (LinearMap.ker ((G.induce (L : Set V)).adjMatrix ℚ).mulVecLin) := by
  classical
  let H := squareOrderHighVertices G d
  let L := (Finset.univ : Finset V) \ H
  let I := {x // x ∈ H.erase a}
  let rows : I → (↥(L : Set V) → ℚ) := fun b =>
    squareOrderLowHighIncidenceDifferenceRat G d b.1 a
  let rowsKer : I → LinearMap.ker
      ((G.induce (L : Set V)).adjMatrix ℚ).mulVecLin := fun b =>
    ⟨rows b, by
      change ((G.induce (L : Set V)).adjMatrix ℚ).mulVec (rows b) = 0
      simpa [H, L, I, rows] using
        squareOrder_lowAdjacency_mulVec_highIncidenceDifferenceRat_eq_zero
          G hfree hd hmin hcover hcard (Finset.mem_of_mem_erase b.2) ha⟩
  have hrows : LinearIndependent ℚ rows := by
    simpa [H, L, I, rows] using
      squareOrder_lowHighIncidenceDifferencesRat_linearIndependent
        G hfree hd hmin hcover hcard ha
  have hrowsKer : LinearIndependent ℚ rowsKer := by
    apply LinearIndependent.of_comp
      (LinearMap.ker ((G.induce (L : Set V)).adjMatrix ℚ).mulVecLin).subtype
    simpa [Function.comp_def, rowsKer] using hrows
  have hle := hrowsKer.fintype_card_le_finrank
  have hIcard : Fintype.card I = H.card - 1 := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem ha]
  simpa [H, hIcard] using hle

/-- In particular, two or more high vertices force the low-sector adjacency
matrix to be singular over the rationals. -/
theorem squareOrder_lowAdjacency_det_eq_zero_of_two_le_high_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : Nat} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hhigh : 2 ≤ (squareOrderHighVertices G d).card) :
    let L := (Finset.univ : Finset V) \ squareOrderHighVertices G d
    ((G.induce (L : Set V)).adjMatrix ℚ).det = 0 := by
  classical
  let H := squareOrderHighVertices G d
  let L := (Finset.univ : Finset V) \ H
  have hhighH : 2 ≤ H.card := by simpa [H] using hhigh
  have hHpos : 0 < H.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hHpos
  have herasepos : 0 < (H.erase a).card := by
    rw [Finset.card_erase_of_mem ha]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp herasepos
  let i : {x // x ∈ H.erase a} := ⟨b, hb⟩
  let v : ↥(L : Set V) → ℚ :=
    squareOrderLowHighIncidenceDifferenceRat G d b a
  have hvzero : ((G.induce (L : Set V)).adjMatrix ℚ).mulVec v = 0 := by
    simpa [H, L, i, v] using
      squareOrder_lowAdjacency_mulVec_highIncidenceDifferenceRat_eq_zero
        G hfree hd hmin hcover hcard (Finset.mem_of_mem_erase hb) ha
  have hli := squareOrder_lowHighIncidenceDifferencesRat_linearIndependent
    G hfree hd hmin hcover hcard ha
  have hvne : v ≠ 0 := by
    simpa [H, L, i, v] using hli.ne_zero i
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hvzero⟩

end

end Erdos85

#print axioms
  Erdos85.squareOrder_lowAdjacency_mulVec_highIncidenceDifference_eq_zero
#print axioms Erdos85.squareOrder_lowHighIncidenceDifferences_linearIndependent
#print axioms
  Erdos85.squareOrder_high_card_sub_one_le_finrank_lowAdjacency_ker
#print axioms
  Erdos85.squareOrder_lowAdjacency_det_eq_zero_of_two_le_high_card

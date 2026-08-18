import Proofs.Erdos85OrderFortyNineThreeHighScoutCnfSemantics

/-! # Semantics of the three-high matching geometry units -/

namespace Erdos85

open Std Sat

def OrderFortyNinePinnedMatchingRealized
    (edges : BitVec 1176) (vertices : List (Fin 49))
    (matching : List (Fin 49 × Fin 49)) : Prop :=
  ∀ ab ∈ orderFortyNineStrictPairs vertices,
    orderFortyNineBitAdj edges ab.1 ab.2 = decide (ab ∈ matching)

theorem orderFortyNinePinnedMatchingClauses_satisfied
    {edges : BitVec 1176} {vertices : List (Fin 49)}
    {matching : List (Fin 49 × Fin 49)}
    (hrealized : OrderFortyNinePinnedMatchingRealized edges vertices matching) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNinePinnedMatchingClauses vertices matching) := by
  intro clause hclause
  simp only [orderFortyNinePinnedMatchingClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  have hne : ab.1 ≠ ab.2 := by
    intro heq
    have hlt := orderFortyNineStrictPairs_lt hab
    rw [heq] at hlt
    omega
  by_cases hm : ab ∈ matching
  · refine ⟨orderFortyNineEdgeLiteral ab.1 ab.2, by simp [hm], ?_⟩
    rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges _ _ hne,
      hrealized ab hab]
    simp [hm]
  · refine ⟨-orderFortyNineEdgeLiteral ab.1 ab.2, by simp [hm], ?_⟩
    rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
      hrealized ab hab]
    simp [hm]

def orderFortyNineThreeHighDistTwoRootEmptyVertices : List (Fin 49) :=
  [13, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37,
    38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48]

def OrderFortyNineThreeHighDistTwoRootEmptyRealized
    (edges : BitVec 1176) : Prop :=
  ∀ z ∈ orderFortyNineThreeHighDistTwoRootEmptyVertices,
    orderFortyNineBitAdj edges 3 z = decide (z = 13)

theorem orderFortyNineThreeHighDistTwoRootEmptyClauses_satisfied
    {edges : BitVec 1176}
    (hrealized : OrderFortyNineThreeHighDistTwoRootEmptyRealized edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineThreeHighDistTwoRootEmptyClauses := by
  intro clause hclause
  simp only [orderFortyNineThreeHighDistTwoRootEmptyClauses,
    List.mem_toArray, List.mem_map] at hclause
  obtain ⟨z, hz, rfl⟩ := hclause
  have hne : (3 : Fin 49) ≠ z := by
    intro heq
    subst z
    norm_num [Fin.ext_iff] at hz
  by_cases h13 : z = 13
  · refine ⟨orderFortyNineEdgeLiteral 3 z, by simp [h13], ?_⟩
    rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges _ _ hne,
      hrealized z (by simpa [orderFortyNineThreeHighDistTwoRootEmptyVertices]
        using hz)]
    simp [h13]
  · refine ⟨-orderFortyNineEdgeLiteral 3 z, by simp [h13], ?_⟩
    rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
      hrealized z (by simpa [orderFortyNineThreeHighDistTwoRootEmptyVertices]
        using hz)]
    simp [h13]

theorem orderFortyNineThreeHighDistTwoGeometryClauses_satisfied
    {edges : BitVec 1176}
    (h0 : OrderFortyNinePinnedMatchingRealized edges
      [3, 4, 5, 6, 7, 8, 9, 10] [(3, 4), (5, 6), (7, 8), (9, 10)])
    (h1 : OrderFortyNinePinnedMatchingRealized edges
      [3, 11, 14, 15, 16, 17, 18, 19]
      [(3, 11), (14, 15), (16, 17), (18, 19)])
    (h2 : OrderFortyNinePinnedMatchingRealized edges
      [3, 12, 20, 21, 22, 23, 24, 25]
      [(3, 12), (20, 21), (22, 23), (24, 25)])
    (hroot : OrderFortyNineThreeHighDistTwoRootEmptyRealized edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineThreeHighDistTwoGeometryClauses := by
  exact dimacsFormulaSatisfied_append
    (dimacsFormulaSatisfied_append
      (dimacsFormulaSatisfied_append
        (orderFortyNinePinnedMatchingClauses_satisfied h0)
        (orderFortyNinePinnedMatchingClauses_satisfied h1))
      (orderFortyNinePinnedMatchingClauses_satisfied h2))
    (orderFortyNineThreeHighDistTwoRootEmptyClauses_satisfied hroot)

theorem orderFortyNineThreeHighDistOneC2GeometryClauses_satisfied
    {edges : BitVec 1176}
    (h0 : OrderFortyNinePinnedMatchingRealized edges
      [3, 4, 5, 6, 7, 8, 9, 10] [(3, 4), (5, 6), (7, 8), (9, 10)])
    (h1 : OrderFortyNinePinnedMatchingRealized edges
      [3, 12, 13, 14, 15, 16, 17, 25]
      [(3, 25), (12, 13), (14, 15), (16, 17)])
    (h2 : OrderFortyNinePinnedMatchingRealized edges
      [5, 18, 19, 20, 21, 22, 23, 25]
      [(5, 18), (19, 25), (20, 21), (22, 23)]) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineThreeHighDistOneC2GeometryClauses := by
  exact dimacsFormulaSatisfied_append
    (dimacsFormulaSatisfied_append
      (orderFortyNinePinnedMatchingClauses_satisfied h0)
      (orderFortyNinePinnedMatchingClauses_satisfied h1))
    (orderFortyNinePinnedMatchingClauses_satisfied h2)

end Erdos85

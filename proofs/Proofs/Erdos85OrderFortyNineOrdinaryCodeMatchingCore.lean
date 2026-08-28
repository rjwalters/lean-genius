import Proofs.Erdos85OrderFortyNineOrdinaryAdjacencyConnected
import Proofs.Erdos85OrderFortyNineOrdinaryCodePartitionIntersection

/-!
# Matching cores of the three ordinary perfect codes

The equation `C x_h = 1` says that every ordinary vertex has exactly one
ordinary neighbor in each high-neighborhood code.  In particular, the graph
induced by any one code is a perfect matching.  This file records the
combinatorial consequence used by the matching-holonomy route: two distinct
pairpoints in the same code are either matched to each other, or have two
distinct alternative mates.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

local instance ordinaryCodeGraphDecidableAdj
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] :
    DecidableRel (orderFortyNineOrdinaryGraph G).Adj :=
  Classical.decRel _

/-- The ordinary vertices adjacent to a fixed high root. -/
def orderFortyNineOrdinaryHighCode
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (h : Fin 49) : Finset (Fin 46) :=
  Finset.univ.filter fun i => G.Adj
    (orderFortyNineOrdinaryVertex i) h

/-- Each high-neighborhood column is an open perfect code in the ordinary
adjacency graph. -/
theorem orderFortyNineOrdinaryHighCode_neighbor_inter_card_eq_one
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {h : Fin 49} (hh : G.degree h = 8) (i : Fin 46) :
    ((orderFortyNineOrdinaryGraph G).neighborFinset i ∩
      orderFortyNineOrdinaryHighCode G h).card = 1 := by
  classical
  have hmul := congrFun
    (orderFortyNineOrdinaryAdjInt_mulVec_highIncidence
      G hfree hmin hhigh hh) i
  simp only [Matrix.mulVec, dotProduct,
    orderFortyNineOrdinaryAdjInt,
    orderFortyNineOrdinaryHighIncidenceInt] at hmul
  have hsum :
      (∑ j : Fin 46,
        if (orderFortyNineOrdinaryGraph G).Adj i j ∧
            G.Adj h (orderFortyNineOrdinaryVertex j)
        then (1 : ℤ) else 0) = 1 := by
    simp only [SimpleGraph.adjMatrix_apply] at hmul
    calc
      (∑ j : Fin 46,
        if (orderFortyNineOrdinaryGraph G).Adj i j ∧
            G.Adj h (orderFortyNineOrdinaryVertex j)
        then (1 : ℤ) else 0) =
          ∑ j : Fin 46,
            (if G.Adj (orderFortyNineOrdinaryVertex i)
                (orderFortyNineOrdinaryVertex j) then (1 : ℤ) else 0) *
              if G.Adj h (orderFortyNineOrdinaryVertex j) then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [orderFortyNineOrdinaryGraph]
        by_cases ha : G.Adj (orderFortyNineOrdinaryVertex i)
            (orderFortyNineOrdinaryVertex j)
        <;> by_cases hhj : G.Adj h (orderFortyNineOrdinaryVertex j)
        <;> simp [ha, hhj]
      _ = 1 := hmul
  have hfilter :
      (orderFortyNineOrdinaryGraph G).neighborFinset i ∩
          orderFortyNineOrdinaryHighCode G h =
        Finset.univ.filter fun j =>
          (orderFortyNineOrdinaryGraph G).Adj i j ∧
            G.Adj h (orderFortyNineOrdinaryVertex j) := by
    ext j
    simp [orderFortyNineOrdinaryHighCode,
      SimpleGraph.mem_neighborFinset, G.adj_comm]
  rw [hfilter]
  have hbool :
      (∑ j : Fin 46,
        if (orderFortyNineOrdinaryGraph G).Adj i j ∧
            G.Adj h (orderFortyNineOrdinaryVertex j)
        then (1 : ℤ) else 0) =
      ((Finset.univ.filter fun j =>
        (orderFortyNineOrdinaryGraph G).Adj i j ∧
          G.Adj h (orderFortyNineOrdinaryVertex j)).card : ℤ) := by
    simpa using (Finset.sum_boole (R := ℤ)
      (fun j : Fin 46 =>
        (orderFortyNineOrdinaryGraph G).Adj i j ∧
          G.Adj h (orderFortyNineOrdinaryVertex j)) Finset.univ)
  rw [hbool] at hsum
  exact_mod_cast hsum

/-- The concrete high code satisfies the abstract open-code interface used by
the two-partition intersection grid. -/
theorem orderFortyNineOrdinaryHighCode_isOpenCode
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {h : Fin 49} (hh : G.degree h = 8) :
    IsOpenCode (orderFortyNineOrdinaryGraph G)
      (orderFortyNineOrdinaryHighCode G h : Set (Fin 46)) := by
  intro z
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
    (orderFortyNineOrdinaryHighCode_neighbor_inter_card_eq_one
      G hfree hmin hhigh hh z)
  have haMem : a ∈
      (orderFortyNineOrdinaryGraph G).neighborFinset z ∩
        orderFortyNineOrdinaryHighCode G h := by
    simp [ha]
  have haParts := Finset.mem_inter.mp haMem
  refine ⟨a, ⟨haParts.2, ?_⟩, ?_⟩
  · simpa [SimpleGraph.mem_neighborFinset] using haParts.1
  · intro b hb
    have hbMem : b ∈
        (orderFortyNineOrdinaryGraph G).neighborFinset z ∩
          orderFortyNineOrdinaryHighCode G h := by
      exact Finset.mem_inter.mpr
        ⟨(by simpa [SimpleGraph.mem_neighborFinset] using hb.2), hb.1⟩
    rw [ha] at hbMem
    simpa using hbMem

/-- Abstract matching dichotomy for two marked vertices in an open perfect
code.  In the non-edge branch their unique code-neighbors are necessarily
distinct and different from the opposite marked vertex. -/
theorem openPerfectCode_marked_pair_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (S : Finset V)
    (hone : ∀ x, (H.neighborFinset x ∩ S).card = 1)
    {p q : V} (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    H.Adj p q ∨
      ∃ r t, r ∈ S ∧ t ∈ S ∧ H.Adj p r ∧ H.Adj q t ∧
        r ≠ t ∧ r ≠ q ∧ t ≠ p := by
  by_cases hadj : H.Adj p q
  · exact Or.inl hadj
  · right
    have hpOne := Finset.card_eq_one.mp (hone p)
    have hqOne := Finset.card_eq_one.mp (hone q)
    obtain ⟨r, hr⟩ := hpOne
    obtain ⟨t, ht⟩ := hqOne
    have hrMem : r ∈ H.neighborFinset p ∩ S := by simp [hr]
    have htMem : t ∈ H.neighborFinset q ∩ S := by simp [ht]
    have hrParts := Finset.mem_inter.mp hrMem
    have htParts := Finset.mem_inter.mp htMem
    refine ⟨r, t, hrParts.2, htParts.2, ?_, ?_, ?_, ?_⟩
    · simpa [SimpleGraph.mem_neighborFinset] using hrParts.1
    · simpa [SimpleGraph.mem_neighborFinset] using htParts.1
    · intro hrt
      subst t
      have hpr : H.Adj p r := by
        simpa [SimpleGraph.mem_neighborFinset] using hrParts.1
      have hqr : H.Adj q r := by
        simpa [SimpleGraph.mem_neighborFinset] using htParts.1
      have hpMem : p ∈ H.neighborFinset r ∩ S := by
        simp [(H.adj_comm p r).mp hpr, hp]
      have hqMem : q ∈ H.neighborFinset r ∩ S := by
        simp [(H.adj_comm q r).mp hqr, hq]
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (hone r)
      rw [hu] at hpMem hqMem
      simp only [Finset.mem_singleton] at hpMem hqMem
      exact hpq (hpMem.trans hqMem.symm)
    · constructor
      · intro hrq
        subst r
        exact hadj (by
          simpa [SimpleGraph.mem_neighborFinset] using hrParts.1)
      · intro htp
        subst t
        exact hadj ((H.adj_comm q p).mp (by
          simpa [SimpleGraph.mem_neighborFinset] using htParts.1))

/-- Graph-facing form of the marked-pair dichotomy for one high code. -/
theorem orderFortyNineOrdinaryHighCode_pair_dichotomy
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {h : Fin 49} (hh : G.degree h = 8)
    {p q : Fin 46}
    (hp : p ∈ orderFortyNineOrdinaryHighCode G h)
    (hq : q ∈ orderFortyNineOrdinaryHighCode G h)
    (hpq : p ≠ q) :
    (orderFortyNineOrdinaryGraph G).Adj p q ∨
      ∃ r t,
        r ∈ orderFortyNineOrdinaryHighCode G h ∧
        t ∈ orderFortyNineOrdinaryHighCode G h ∧
        (orderFortyNineOrdinaryGraph G).Adj p r ∧
        (orderFortyNineOrdinaryGraph G).Adj q t ∧
        r ≠ t ∧ r ≠ q ∧ t ≠ p := by
  apply openPerfectCode_marked_pair_dichotomy
    (orderFortyNineOrdinaryGraph G)
    (orderFortyNineOrdinaryHighCode G h)
    (orderFortyNineOrdinaryHighCode_neighbor_inter_card_eq_one
      G hfree hmin hhigh hh)
    hp hq hpq

/-- Among the three edges joining three pairpoints of three open codes, at
most one can occur.  Any two such edges share a pairpoint; their other
endpoints both belong to the remaining code, contradicting its unique-owner
property. -/
theorem threeOpenCodes_pairpoint_edges_atMostOne
    {V : Type*} (H : SimpleGraph V)
    {A B C : Set V}
    (hA : IsOpenCode H A) (hB : IsOpenCode H B) (hC : IsOpenCode H C)
    {pAB pAC pBC : V}
    (hpAB_A : pAB ∈ A) (hpAB_B : pAB ∈ B)
    (hpAC_A : pAC ∈ A) (hpAC_C : pAC ∈ C)
    (hpBC_B : pBC ∈ B) (hpBC_C : pBC ∈ C)
    (hneAB_AC : pAB ≠ pAC)
    (hneAB_BC : pAB ≠ pBC)
    (hneAC_BC : pAC ≠ pBC) :
    ¬ ((H.Adj pAB pAC ∧ H.Adj pAB pBC) ∨
       (H.Adj pAB pAC ∧ H.Adj pAC pBC) ∨
       (H.Adj pAB pBC ∧ H.Adj pAC pBC)) := by
  intro hedges
  rcases hedges with hAtC | hAtB | hAtA
  · obtain ⟨owner, howner, hunique⟩ := hC pAB
    have hAC : pAC = owner := hunique pAC ⟨hpAC_C, hAtC.1⟩
    have hBC : pBC = owner := hunique pBC ⟨hpBC_C, hAtC.2⟩
    exact hneAC_BC (hAC.trans hBC.symm)
  · obtain ⟨owner, howner, hunique⟩ := hB pAC
    have hAB : pAB = owner := hunique pAB
      ⟨hpAB_B, (H.adj_comm pAB pAC).mp hAtB.1⟩
    have hBC : pBC = owner := hunique pBC ⟨hpBC_B, hAtB.2⟩
    exact hneAB_BC (hAB.trans hBC.symm)
  · obtain ⟨owner, howner, hunique⟩ := hA pBC
    have hAB : pAB = owner := hunique pAB
      ⟨hpAB_A, (H.adj_comm pAB pBC).mp hAtA.1⟩
    have hAC : pAC = owner := hunique pAC
      ⟨hpAC_A, (H.adj_comm pAC pBC).mp hAtA.2⟩
    exact hneAB_AC (hAB.trans hAC.symm)

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryHighCode_neighbor_inter_card_eq_one
#print axioms Erdos85.orderFortyNineOrdinaryHighCode_isOpenCode
#print axioms Erdos85.openPerfectCode_marked_pair_dichotomy
#print axioms Erdos85.orderFortyNineOrdinaryHighCode_pair_dichotomy
#print axioms Erdos85.threeOpenCodes_pairpoint_edges_atMostOne

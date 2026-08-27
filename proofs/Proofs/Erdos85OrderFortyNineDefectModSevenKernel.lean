import Proofs.Erdos85OrderFortyNineAutomaticDefectNonsingular
import Proofs.Erdos85OrderFortyNineDefectEigenvectors

/-! # Canonical mod-seven kernel vectors of the ordinary defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

def orderFortyNineOrdinaryDefectLInt
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix (Fin 46) (Fin 46) ℤ :=
  fun i j => 6 * (1 : Matrix (Fin 46) (Fin 46) ℤ) i j -
    (secondOrderDefectGraph G).adjMatrix ℤ
      (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j)

def orderFortyNineOrdinaryHighRowDifference
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (x z : Fin 49) : Fin 46 → ℤ :=
  fun i => orderFortyNineHighRowDifference G x z
    (orderFortyNineOrdinaryVertex i)

private theorem orderFortyNine_not_defectAdj_of_high
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    {x y : Fin 49} (hx : G.degree x = 8) :
    ¬ (secondOrderDefectGraph G).Adj x y := by
  intro hxy
  have hzero := (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
    G hfree hmin (by decide) hx).1
  have hy : y ∈ (secondOrderDefectGraph G).neighborFinset x := by
    simpa [SimpleGraph.mem_neighborFinset] using hxy
  have hpos : 0 < (secondOrderDefectGraph G).degree x := by
    rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨y, hy⟩
  omega

/-- An ordinary restriction of a high-row difference is an exact
eigenvector of the integral defect block with eigenvalue seven.  Reduction
modulo seven therefore gives a kernel vector. -/
theorem orderFortyNineOrdinaryDefectLInt_mulVec_highRowDifference
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {x z : Fin 49} (hx : G.degree x = 8) (hz : G.degree z = 8) :
    (orderFortyNineOrdinaryDefectLInt G).mulVec
        (orderFortyNineOrdinaryHighRowDifference G x z) =
      7 • orderFortyNineOrdinaryHighRowDifference G x z := by
  funext i
  have hfull := congrFun (orderFortyNine_defect_mulVec_highRowDifference
    G hfree hmin (by decide) hx hz) (orderFortyNineOrdinaryVertex i)
  simp only [Matrix.mulVec, dotProduct] at hfull ⊢
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ] at hfull
  have h0 : ¬ (secondOrderDefectGraph G).Adj (orderFortyNineOrdinaryVertex i) 0 := by
    simpa [(secondOrderDefectGraph G).adj_comm] using
      (orderFortyNine_not_defectAdj_of_high G hfree hmin
        (y := orderFortyNineOrdinaryVertex i) ((hhigh (0 : Fin 49)).2 (by decide)))
  have h1 : ¬ (secondOrderDefectGraph G).Adj (orderFortyNineOrdinaryVertex i) 1 := by
    simpa [(secondOrderDefectGraph G).adj_comm] using
      (orderFortyNine_not_defectAdj_of_high G hfree hmin
        (y := orderFortyNineOrdinaryVertex i) ((hhigh (1 : Fin 49)).2 (by decide)))
  have h2 : ¬ (secondOrderDefectGraph G).Adj (orderFortyNineOrdinaryVertex i) 2 := by
    simpa [(secondOrderDefectGraph G).adj_comm] using
      (orderFortyNine_not_defectAdj_of_high G hfree hmin
        (y := orderFortyNineOrdinaryVertex i) ((hhigh (2 : Fin 49)).2 (by decide)))
  have hm0 : (secondOrderDefectGraph G).adjMatrix ℤ
      (orderFortyNineOrdinaryVertex i) 0 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, h0]
  have hm1 : (secondOrderDefectGraph G).adjMatrix ℤ
      (orderFortyNineOrdinaryVertex i) 1 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, h1]
  have hm2 : (secondOrderDefectGraph G).adjMatrix ℤ
      (orderFortyNineOrdinaryVertex i) 2 = 0 := by
    simp [SimpleGraph.adjMatrix_apply, h2]
  have he1 : (Fin.succ 0 : Fin 49) = 1 := by decide
  have he2 : ((Fin.succ 0).succ : Fin 49) = 2 := by decide
  rw [he1, he2] at hfull
  rw [hm0, hm1, hm2] at hfull
  simp only [zero_mul, zero_add] at hfull
  have hsucc (j : Fin 46) : j.succ.succ.succ = orderFortyNineOrdinaryVertex j := by
    apply Fin.ext
    simp [orderFortyNineOrdinaryVertex]
    omega
  simp_rw [hsucc] at hfull
  have hsum : (∑ j : Fin 46,
      (secondOrderDefectGraph G).adjMatrix ℤ
          (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j) *
        orderFortyNineOrdinaryHighRowDifference G x z j) =
      - orderFortyNineOrdinaryHighRowDifference G x z i := by
    simpa [orderFortyNineOrdinaryHighRowDifference,
      SimpleGraph.adjMatrix_apply] using hfull
  calc
    (∑ j, orderFortyNineOrdinaryDefectLInt G i j *
        orderFortyNineOrdinaryHighRowDifference G x z j) =
        6 * orderFortyNineOrdinaryHighRowDifference G x z i -
          ∑ j, (secondOrderDefectGraph G).adjMatrix ℤ
              (orderFortyNineOrdinaryVertex i) (orderFortyNineOrdinaryVertex j) *
            orderFortyNineOrdinaryHighRowDifference G x z j := by
      simp only [orderFortyNineOrdinaryDefectLInt, sub_mul,
        Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hbi
        simp [Matrix.one_apply, Ne.symm hbi]
      · simp
    _ = 7 * orderFortyNineOrdinaryHighRowDifference G x z i := by rw [hsum]; ring
    _ = (7 • orderFortyNineOrdinaryHighRowDifference G x z) i := by simp

def orderFortyNineOrdinaryDefectLModSeven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix (Fin 46) (Fin 46) (ZMod 7) :=
  (Int.castRingHom (ZMod 7)).mapMatrix (orderFortyNineOrdinaryDefectLInt G)

def orderFortyNineOrdinaryHighRowDifferenceModSeven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (x z : Fin 49) : Fin 46 → ZMod 7 :=
  fun i => (orderFortyNineOrdinaryHighRowDifference G x z i : ZMod 7)

theorem orderFortyNineOrdinaryDefectLModSeven_mulVec_highRowDifference_eq_zero
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {x z : Fin 49} (hx : G.degree x = 8) (hz : G.degree z = 8) :
    (orderFortyNineOrdinaryDefectLModSeven G).mulVec
        (orderFortyNineOrdinaryHighRowDifferenceModSeven G x z) = 0 := by
  have hint := orderFortyNineOrdinaryDefectLInt_mulVec_highRowDifference
    G hfree hmin hhigh hx hz
  funext i
  have hi := congrFun hint i
  have hi' := congrArg (Int.castRingHom (ZMod 7)) hi
  simp [orderFortyNineOrdinaryDefectLModSeven,
    orderFortyNineOrdinaryHighRowDifferenceModSeven,
    Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply] at hi' ⊢
  have hseven : (7 : ZMod 7) = 0 := by decide
  rw [hseven, zero_mul] at hi'
  exact hi'

private theorem orderFortyNine_exists_ordinary_neighbor_exclusive_of_three_high
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    {a b c : Fin 49}
    (ha : G.degree a = 8) (hb : G.degree b = 8) (hc : G.degree c = 8)
    (hab : a ≠ b) (hac : a ≠ c) :
    ∃ j : Fin 46, G.Adj a (orderFortyNineOrdinaryVertex j) ∧
      ¬ G.Adj b (orderFortyNineOrdinaryVertex j) ∧
      ¬ G.Adj c (orderFortyNineOrdinaryVertex j) := by
  let Na := G.neighborFinset a
  let Nb := G.neighborFinset b
  let Nc := G.neighborFinset c
  let B := (Na ∩ Nb) ∪ (Na ∩ Nc)
  have hNa : Na.card = 8 := by
    dsimp [Na]
    exact ha
  have habCard : (Na ∩ Nb).card = 1 := by
    dsimp [Na, Nb]
    exact orderFortyNine_card_common_degreeEight_eq_one
      G hfree hmin (by decide) ha hb hab
  have hacCard : (Na ∩ Nc).card = 1 := by
    dsimp [Na, Nc]
    exact orderFortyNine_card_common_degreeEight_eq_one
      G hfree hmin (by decide) ha hc hac
  have hB : B.card ≤ 2 := by
    calc
      B.card ≤ (Na ∩ Nb).card + (Na ∩ Nc).card := by
        dsimp [B]
        exact Finset.card_union_le _ _
      _ = 2 := by rw [habCard, hacCard]
  have hex : ∃ y ∈ Na, y ∉ B := by
    by_contra hnone
    push_neg at hnone
    have hsub : Na ⊆ B := fun y hy => hnone y hy
    have := Finset.card_le_card hsub
    omega
  obtain ⟨y, hya, hyB⟩ := hex
  have hyb : y ∉ Nb := by
    intro hy
    apply hyB
    exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hya, hy⟩)
  have hyc : y ∉ Nc := by
    intro hy
    apply hyB
    exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hya, hy⟩)
  have hay : G.Adj a y := by simpa [Na, SimpleGraph.mem_neighborFinset] using hya
  have hby : ¬ G.Adj b y := by simpa [Nb, SimpleGraph.mem_neighborFinset] using hyb
  have hcy : ¬ G.Adj c y := by simpa [Nc, SimpleGraph.mem_neighborFinset] using hyc
  have hy7 : G.degree y = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin (by decide) y with h | h
    · exact h
    · exact False.elim ((orderFortyNine_not_adj_degreeEight_degreeEight
        G hfree hmin (by decide) ha h) hay)
  have hyge : 3 ≤ y.val := by
    by_contra hlt
    have hylt : y.val < 3 := by omega
    have hy8 : G.degree y = 8 := (hhigh y).2 hylt
    omega
  let j : Fin 46 := ⟨y.val - 3, by omega⟩
  have hj : orderFortyNineOrdinaryVertex j = y := by
    apply Fin.ext
    simp [orderFortyNineOrdinaryVertex, j]
    omega
  exact ⟨j, by simpa [hj] using hay, by simpa [hj] using hby,
    by simpa [hj] using hcy⟩

/-- The two canonical high-row differences are independent modulo seven.
This is the concrete two-dimensional kernel certificate used by the order-49
terminal. -/
theorem orderFortyNine_two_ordinaryHighRowDifferencesModSeven_independent
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3)
    (α β : ZMod 7)
    (hlin : α • orderFortyNineOrdinaryHighRowDifferenceModSeven G 0 2 +
        β • orderFortyNineOrdinaryHighRowDifferenceModSeven G 1 2 = 0) :
    α = 0 ∧ β = 0 := by
  have h0 : G.degree (0 : Fin 49) = 8 := (hhigh 0).2 (by decide)
  have h1 : G.degree (1 : Fin 49) = 8 := (hhigh 1).2 (by decide)
  have h2 : G.degree (2 : Fin 49) = 8 := (hhigh 2).2 (by decide)
  obtain ⟨j0, hj00, hj01, hj02⟩ :=
    orderFortyNine_exists_ordinary_neighbor_exclusive_of_three_high
      G hfree hmin hhigh h0 h1 h2 (by decide) (by decide)
  obtain ⟨j1, hj11, hj10, hj12⟩ :=
    orderFortyNine_exists_ordinary_neighbor_exclusive_of_three_high
      G hfree hmin hhigh h1 h0 h2 (by decide) (by decide)
  have hj0 := congrFun hlin j0
  have hj1 := congrFun hlin j1
  simp [orderFortyNineOrdinaryHighRowDifferenceModSeven,
    orderFortyNineOrdinaryHighRowDifference, orderFortyNineHighRowDifference,
    SimpleGraph.adjMatrix_apply, hj00, hj01, hj02,
    Pi.smul_apply, smul_eq_mul] at hj0
  simp [orderFortyNineOrdinaryHighRowDifferenceModSeven,
    orderFortyNineOrdinaryHighRowDifference, orderFortyNineHighRowDifference,
    SimpleGraph.adjMatrix_apply, hj11, hj10, hj12,
    Pi.smul_apply, smul_eq_mul] at hj1
  exact ⟨hj0, hj1⟩

def orderFortyNineTwoHighRowDifferenceFamilyModSeven
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj] :
    Bool → (Fin 46 → ZMod 7)
  | false => orderFortyNineOrdinaryHighRowDifferenceModSeven G 0 2
  | true => orderFortyNineOrdinaryHighRowDifferenceModSeven G 1 2

theorem orderFortyNineTwoHighRowDifferenceFamilyModSeven_linearIndependent
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3) :
    LinearIndependent (ZMod 7)
      (orderFortyNineTwoHighRowDifferenceFamilyModSeven G) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fintype.sum_bool] at hg
  have hcoeff := orderFortyNine_two_ordinaryHighRowDifferencesModSeven_independent
    G hfree hmin hhigh (g false) (g true) (by
      simpa [orderFortyNineTwoHighRowDifferenceFamilyModSeven, add_comm] using hg)
  cases i with
  | false => exact hcoeff.1
  | true => exact hcoeff.2

theorem orderFortyNineTwoHighRowDifferenceFamilyModSeven_mem_kernel
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x, 7 ≤ G.degree x)
    (hhigh : ∀ y : Fin 49, G.degree y = 8 ↔ y.val < 3) (b : Bool) :
    (orderFortyNineOrdinaryDefectLModSeven G).mulVec
        (orderFortyNineTwoHighRowDifferenceFamilyModSeven G b) = 0 := by
  cases b with
  | false =>
      exact orderFortyNineOrdinaryDefectLModSeven_mulVec_highRowDifference_eq_zero
        G hfree hmin hhigh ((hhigh 0).2 (by decide)) ((hhigh 2).2 (by decide))
  | true =>
      exact orderFortyNineOrdinaryDefectLModSeven_mulVec_highRowDifference_eq_zero
        G hfree hmin hhigh ((hhigh 1).2 (by decide)) ((hhigh 2).2 (by decide))

end

end Erdos85

#print axioms Erdos85.orderFortyNineOrdinaryDefectLInt_mulVec_highRowDifference
#print axioms Erdos85.orderFortyNineOrdinaryDefectLModSeven_mulVec_highRowDifference_eq_zero
#print axioms Erdos85.orderFortyNine_two_ordinaryHighRowDifferencesModSeven_independent
#print axioms Erdos85.orderFortyNineTwoHighRowDifferenceFamilyModSeven_linearIndependent
#print axioms Erdos85.orderFortyNineTwoHighRowDifferenceFamilyModSeven_mem_kernel

import Proofs.Erdos85OrderSixtyFourExteriorPairGraph
import Proofs.Erdos85ComponentGramCommutation
import Proofs.Erdos85LambdaSixGraphFourFactorization
import Proofs.Erdos85OrderSixtyFourTenSixComponentLabeling
import Proofs.Erdos85LambdaSixFiveFiveThreeThreeLabeling

/-! # The exterior-pair graph is an admissible lambda-six correction -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- Relabeled support of the square of a graph adjacency relation. -/
def relabeledCommonNeighborBool {V : Type*} [Fintype V]
    (e : V ≃ Fin 16) (H : SimpleGraph V) [DecidableRel H.Adj] :
    Fin 16 → Fin 16 → Bool :=
  fun x y => decide (∃ z : V, H.Adj (e.symm x) z ∧ H.Adj (e.symm y) z)

private theorem relabeled_filter_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (e : V ≃ Fin 16) (p : V → Bool) :
    (Finset.univ.filter fun y : Fin 16 => p (e.symm y)).card =
      (Finset.univ.filter fun y : V => p y).card := by
  apply Finset.card_bij (fun y _ => e.symm y)
  · intro y hy
    simpa using hy
  · intro y₁ hy₁ y₂ hy₂ h
    exact e.symm.injective h
  · intro y hy
    exact ⟨e y, by simpa using hy, by simp⟩

/-- A pair cannot have both an internal and an external common neighbor in
a `C₄`-free ambient graph. -/
theorem exteriorPairGraph_not_commonNeighbor_of_noC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (hfree : ¬ containsC4 V G) {u v : s}
    (hR : (exteriorPairGraph G s).Adj u v) :
    ¬ ∃ z : s, (G.induce s).Adj u z ∧ (G.induce s).Adj v z := by
  rintro ⟨z, huz, hvz⟩
  obtain ⟨huv, w, hwout, huw, hvw⟩ := hR
  have huvval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  have hzw : z.1 ≠ w := fun h => hwout (h ▸ z.2)
  have hC4 := (not_containsC4_iff_forall_common_le_one G).mp hfree
    u.1 v.1 huvval
  have hzmem : z.1 ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 := by
    simp only [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨huz, hvz⟩
  have hwmem : w ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 := by
    simp only [Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨huw, hvw⟩
  have htwo : 2 ≤ (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card := by
    have hsub : ({z.1, w} : Finset V) ⊆
        G.neighborFinset u.1 ∩ G.neighborFinset v.1 := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hzmem
      · exact hwmem
    calc
      2 = ({z.1, w} : Finset V).card := by simp [hzw]
      _ ≤ _ := Finset.card_le_card hsub
  omega

/-- Graph-facing bridge from the five structural conditions to the exact
bit-vector admissibility predicate used by the finite lambda-six census. -/
theorem graph_lambdaSixAdmissibleR_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (e : V ≃ Fin 16) (H R : SimpleGraph V)
    [DecidableRel H.Adj] [DecidableRel R.Adj]
    (hdeg : ∀ x, R.degree x = 6)
    (hdisjoint : ∀ x y, R.Adj x y →
      ¬ ∃ z, H.Adj x z ∧ H.Adj y z)
    (hcomm : R.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * R.adjMatrix ℤ) :
    lambdaSixAdmissibleR
      (matrixBV (relabeledGraphBool e H))
      (matrixBV (relabeledCommonNeighborBool e H))
      (matrixBV (relabeledGraphBool e R)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [bitAdj_matrixBV, relabeledGraphBool]
  · intro x y
    simp only [bitAdj_matrixBV, relabeledGraphBool, decide_eq_decide]
    exact R.adj_comm _ _
  · intro x
    apply BitVec.eq_of_toNat_eq
    rw [cpop16_eq_filter_card]
    simp only [row256_matrixBV_getLsbD, relabeledGraphBool]
    rw [relabeled_filter_card e (fun y => decide (R.Adj (e.symm x) y))]
    calc
      (Finset.univ.filter fun y : V => decide (R.Adj (e.symm x) y)).card =
          (R.neighborFinset (e.symm x)).card := by congr 1 <;> ext y <;> simp
      _ = R.degree (e.symm x) := R.card_neighborFinset_eq_degree _
      _ = 6 := hdeg _
  · intro x y hxy
    simp only [bitAdj_matrixBV, relabeledGraphBool, decide_eq_true_eq] at hxy
    simp only [bitAdj_matrixBV, relabeledCommonNeighborBool]
    exact decide_eq_false_iff_not.mpr (hdisjoint _ _ hxy)
  · intro x y
    apply BitVec.eq_of_toNat_eq
    rw [cpop16_eq_filter_card, cpop16_eq_filter_card]
    simp only [BitVec.getLsbD_and, row256_matrixBV_getLsbD,
      relabeledGraphBool]
    rw [relabeled_filter_card e (fun z =>
      decide (R.Adj (e.symm x) z) && decide (H.Adj (e.symm y) z))]
    rw [relabeled_filter_card e (fun z =>
      decide (H.Adj (e.symm x) z) && decide (R.Adj (e.symm y) z))]
    have hc := congrFun (congrFun hcomm (e.symm x)) (e.symm y)
    norm_num [Matrix.mul_apply, SimpleGraph.adjMatrix_apply] at hc ⊢
    have hleft :
        (((Finset.univ.filter fun z : V =>
          R.Adj (e.symm x) z ∧ H.Adj (e.symm y) z).card : ℕ) : ℤ) =
        ∑ z : V, if H.Adj z (e.symm y) then
          if R.Adj (e.symm x) z then 1 else 0 else 0 := by
      rw [Finset.natCast_card_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hR : R.Adj (e.symm x) z <;>
        by_cases hH : H.Adj (e.symm y) z <;> simp_all [H.adj_comm]
    have hright :
        (((Finset.univ.filter fun z : V =>
          H.Adj (e.symm x) z ∧ R.Adj (e.symm y) z).card : ℕ) : ℤ) =
        ∑ z : V, if R.Adj z (e.symm y) then
          if H.Adj (e.symm x) z then 1 else 0 else 0 := by
      rw [Finset.natCast_card_filter]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hH : H.Adj (e.symm x) z <;>
        by_cases hR : R.Adj (e.symm y) z <;> simp_all [R.adj_comm]
    exact_mod_cast hleft.trans (hc.trans hright.symm)

/-- Every sixteen-point, internally two-regular defect component at order 64
has an exterior-pair graph satisfying the complete relation-level
lambda-six admissibility predicate, in arbitrary component coordinates. -/
theorem orderSixtyFour_exteriorPair_lambdaSixAdmissibleR
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc16 : c.supp.ncard = 16)
    (hlocal : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (e : c.supp ≃ Fin 16) :
    lambdaSixAdmissibleR
      (matrixBV (relabeledGraphBool e (G.induce c.supp)))
      (matrixBV (relabeledCommonNeighborBool e (G.induce c.supp)))
      (matrixBV (relabeledGraphBool e (exteriorPairGraph G c.supp))) := by
  classical
  let H := G.induce c.supp
  let R := exteriorPairGraph G c.supp
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let A := H.adjMatrix ℂ
  have hdiag : ∀ u : c.supp,
      (Finset.univ.filter fun z : {z // z ∉ c.supp} ↦
        G.Adj u.1 z.1 ∧ G.Adj u.1 z.1).card = 6 := by
    intro u
    let D := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ
    have hid := orderSixtyFour_defectComponent_internal_sq_add_exteriorGram_complex
      G hfree hmin hcover c
    change A * A + B * Matrix.conjTranspose B =
      (7 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
        (FriendshipTheoremOQ01.onesMatrix c.supp).map
          (Int.castRingHom ℂ) - D at hid
    have hAii : (A * A) u u = 2 := by
      dsimp [A, H]
      rw [(G.induce c.supp).adjMatrix_mul_self_apply_self]
      exact_mod_cast hlocal u
    have he := congrArg (fun M ↦ M u u) hid
    have hDii : D u u = 0 := by
      simp [D, SimpleGraph.adjMatrix_apply]
    have hQii : (B * Matrix.conjTranspose B) u u = 6 := by
      simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.one_apply, FriendshipTheoremOQ01.onesMatrix,
        SimpleGraph.adjMatrix_apply, hAii, hDii] at he
      linear_combination he
    have hc := exteriorGram_apply_eq_card G c.supp u u
    change (B * Matrix.conjTranspose B) u u = _ at hc
    rw [hQii] at hc
    exact_mod_cast hc.symm
  have hle : ∀ u v : c.supp, u ≠ v →
      (Finset.univ.filter fun z : {z // z ∉ c.supp} ↦
        G.Adj u.1 z.1 ∧ G.Adj v.1 z.1).card ≤ 1 := by
    intro u v huv
    exact exterior_common_card_le_one_of_noC4 G c.supp hfree u v huv
  have hQ := exteriorGram_eq_six_add_pairGraph G c.supp hdiag hle
  change B * Matrix.conjTranspose B =
      (6 : ℂ) • (1 : Matrix c.supp c.supp ℂ) + R.adjMatrix ℂ at hQ
  have hQone := orderSixtyFour_sixteenBlock_exteriorGram_mulVec_one
    G hfree hmin hcover c hc16 hlocal
  change (B * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
    (12 : ℂ) • (fun _ ↦ 1) at hQone
  have hRdeg : ∀ x : c.supp, R.degree x = 6 := by
    intro x
    have he := congrArg (fun M ↦ M.mulVec (fun _ ↦ (1 : ℂ)) x) hQ
    have hx := congrFun hQone x
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at he
    have hRadj : (R.adjMatrix ℂ).mulVec (fun _ ↦ 1) x =
        (R.degree x : ℂ) := by
      simpa using (SimpleGraph.adjMatrix_mulVec_const_apply
        (G := R) (α := ℂ) (a := 1) (v := x))
    simp only [Pi.add_apply, Pi.smul_apply] at he hx
    rw [hRadj] at he
    simp at he
    norm_num at hx
    rw [hx] at he
    have hre := congrArg Complex.re he
    norm_num at hre
    have : 12 = 6 + R.degree x := by exact_mod_cast hre
    omega
  have hGramComm := (orderSixtyFour_defectComponent_exteriorGram_comm
    G hfree hmin hcover c hlocal).1
  change A * (B * Matrix.conjTranspose B) =
    (B * Matrix.conjTranspose B) * A at hGramComm
  have hcommC : R.adjMatrix ℂ * A = A * R.adjMatrix ℂ := by
    rw [hQ] at hGramComm
    ext x y
    have hxy := congrFun (congrFun hGramComm x) y
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
      Matrix.smul_apply] at hxy
    linear_combination -hxy
  have hcommZ : R.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * R.adjMatrix ℤ := by
    ext x y
    have hcxy := congrFun (congrFun hcommC x) y
    norm_num [Matrix.mul_apply, SimpleGraph.adjMatrix_apply, A, H] at hcxy ⊢
    exact_mod_cast hcxy
  apply graph_lambdaSixAdmissibleR_relabel e H R hRdeg
  · intro x y hR
    exact exteriorPairGraph_not_commonNeighbor_of_noC4
      G c.supp hfree hR
  · exact hcommZ

private def tenSixCommonNeighborBool : Fin 16 → Fin 16 → Bool :=
  fun x y => decide (∃ z : Fin 16,
    tenSixCycleGraph.Adj x z ∧ tenSixCycleGraph.Adj y z)

private def fiveFiveThreeThreeCommonNeighborBool : Fin 16 → Fin 16 → Bool :=
  fun x y => decide (∃ z : Fin 16,
    fiveFiveThreeThreeCycleGraph.Adj x z ∧
      fiveFiveThreeThreeCycleGraph.Adj y z)

private theorem tenSix_fixed_encodings :
    matrixBV (fun x y => decide (tenSixCycleGraph.Adj x y)) =
        lambdaSixTenSixH256 ∧
      matrixBV tenSixCommonNeighborBool = lambdaSixTenSixH2Support256 := by
  native_decide

private theorem fiveFiveThreeThree_fixed_encodings :
    matrixBV (fun x y => decide (fiveFiveThreeThreeCycleGraph.Adj x y)) =
        lambdaSixFiveFiveThreeThreeH256 ∧
      matrixBV fiveFiveThreeThreeCommonNeighborBool =
        lambdaSixFiveFiveThreeThreeH2Support256 := by
  native_decide

private theorem relabeledGraphBool_eq_of_tenSixLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : TenSixComponentLabeling H) :
    relabeledGraphBool label.toEquiv H =
      fun x y => decide (tenSixCycleGraph.Adj x y) := by
  funext x y
  simp only [relabeledGraphBool, decide_eq_decide]
  simpa using (label.map_adj_iff (label.toEquiv.symm x)
    (label.toEquiv.symm y))

private theorem relabeledCommonNeighborBool_eq_of_tenSixLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : TenSixComponentLabeling H) :
    relabeledCommonNeighborBool label.toEquiv H =
      tenSixCommonNeighborBool := by
  funext x y
  simp only [relabeledCommonNeighborBool, tenSixCommonNeighborBool,
    decide_eq_decide]
  constructor
  · rintro ⟨z, hxz, hyz⟩
    exact ⟨label.toEquiv z,
      by simpa using (label.map_adj_iff _ _).mp hxz,
      by simpa using (label.map_adj_iff _ _).mp hyz⟩
  · rintro ⟨z, hxz, hyz⟩
    exact ⟨label.toEquiv.symm z,
      (label.map_adj_iff _ _).mpr (by simpa using hxz),
      (label.map_adj_iff _ _).mpr (by simpa using hyz)⟩

private theorem relabeledGraphBool_eq_of_fiveFiveThreeThreeLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : FiveFiveThreeThreeComponentLabeling H) :
    relabeledGraphBool label.toEquiv H =
      fun x y => decide (fiveFiveThreeThreeCycleGraph.Adj x y) := by
  funext x y
  simp only [relabeledGraphBool, decide_eq_decide]
  simpa using (label.map_adj_iff (label.toEquiv.symm x)
    (label.toEquiv.symm y))

private theorem relabeledCommonNeighborBool_eq_of_fiveFiveThreeThreeLabeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : FiveFiveThreeThreeComponentLabeling H) :
    relabeledCommonNeighborBool label.toEquiv H =
      fiveFiveThreeThreeCommonNeighborBool := by
  funext x y
  simp only [relabeledCommonNeighborBool,
    fiveFiveThreeThreeCommonNeighborBool, decide_eq_decide]
  constructor
  · rintro ⟨z, hxz, hyz⟩
    exact ⟨label.toEquiv z,
      by simpa using (label.map_adj_iff _ _).mp hxz,
      by simpa using (label.map_adj_iff _ _).mp hyz⟩
  · rintro ⟨z, hxz, hyz⟩
    exact ⟨label.toEquiv.symm z,
      (label.map_adj_iff _ _).mpr (by simpa using hxz),
      (label.map_adj_iff _ _).mpr (by simpa using hyz)⟩

/-- Both fixed bit-vector encodings transported by a `[10,6]` component
labeling. -/
theorem tenSixComponentLabeling_matrixBV_encodings
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : TenSixComponentLabeling H) :
    matrixBV (relabeledGraphBool label.toEquiv H) = lambdaSixTenSixH256 ∧
      matrixBV (relabeledCommonNeighborBool label.toEquiv H) =
        lambdaSixTenSixH2Support256 := by
  rw [relabeledGraphBool_eq_of_tenSixLabeling,
    relabeledCommonNeighborBool_eq_of_tenSixLabeling]
  exact tenSix_fixed_encodings

/-- Both fixed bit-vector encodings transported by a `[5,5,3,3]` component
labeling. -/
theorem fiveFiveThreeThreeComponentLabeling_matrixBV_encodings
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : FiveFiveThreeThreeComponentLabeling H) :
    matrixBV (relabeledGraphBool label.toEquiv H) =
        lambdaSixFiveFiveThreeThreeH256 ∧
      matrixBV (relabeledCommonNeighborBool label.toEquiv H) =
        lambdaSixFiveFiveThreeThreeH2Support256 := by
  rw [relabeledGraphBool_eq_of_fiveFiveThreeThreeLabeling,
    relabeledCommonNeighborBool_eq_of_fiveFiveThreeThreeLabeling]
  exact fiveFiveThreeThree_fixed_encodings

/-- Exact census-coordinate admissibility for a `[10,6]` component. -/
theorem orderSixtyFour_tenSix_exteriorPair_lambdaSixAdmissibleR
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc16 : c.supp.ncard = 16)
    (hlocal : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (label : TenSixComponentLabeling (G.induce c.supp)) :
    lambdaSixAdmissibleR lambdaSixTenSixH256
      lambdaSixTenSixH2Support256
      (matrixBV (relabeledGraphBool label.toEquiv
        (exteriorPairGraph G c.supp))) := by
  have h := orderSixtyFour_exteriorPair_lambdaSixAdmissibleR
    G hfree hmin hcover c hc16 hlocal label.toEquiv
  rw [relabeledGraphBool_eq_of_tenSixLabeling, tenSix_fixed_encodings.1,
    relabeledCommonNeighborBool_eq_of_tenSixLabeling,
    tenSix_fixed_encodings.2] at h
  exact h

/-- Exact census-coordinate admissibility for a `[5,5,3,3]` component. -/
theorem orderSixtyFour_fiveFiveThreeThree_exteriorPair_lambdaSixAdmissibleR
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc16 : c.supp.ncard = 16)
    (hlocal : ∀ x : c.supp, (G.induce c.supp).degree x = 2)
    (label : FiveFiveThreeThreeComponentLabeling (G.induce c.supp)) :
    lambdaSixAdmissibleR lambdaSixFiveFiveThreeThreeH256
      lambdaSixFiveFiveThreeThreeH2Support256
      (matrixBV (relabeledGraphBool label.toEquiv
        (exteriorPairGraph G c.supp))) := by
  have h := orderSixtyFour_exteriorPair_lambdaSixAdmissibleR
    G hfree hmin hcover c hc16 hlocal label.toEquiv
  rw [relabeledGraphBool_eq_of_fiveFiveThreeThreeLabeling,
    fiveFiveThreeThree_fixed_encodings.1,
    relabeledCommonNeighborBool_eq_of_fiveFiveThreeThreeLabeling,
    fiveFiveThreeThree_fixed_encodings.2] at h
  exact h

end

end Erdos85

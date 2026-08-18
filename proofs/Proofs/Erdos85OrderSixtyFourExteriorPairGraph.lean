import Proofs.Erdos85ExteriorGramSecondMoment
import Proofs.Erdos85OrderSixtyFourSixteenBlockGramTrace
import Proofs.Erdos85GadgetExtension

/-! # The exterior-pair graph on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two vertices of `s` are joined when they have a common ambient neighbor
outside `s`. -/
def exteriorPairGraph {V : Type*} (G : SimpleGraph V) (s : Set V) :
    SimpleGraph s where
  Adj u v := u ≠ v ∧ ∃ z : V, z ∉ s ∧ G.Adj u.1 z ∧ G.Adj v.1 z
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    obtain ⟨z, hz, huz, hvz⟩ := h.2
    exact ⟨z, hz, hvz, huz⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

instance exteriorPairGraph_adjDecidable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Set V)
    [DecidablePred (· ∈ s)] : DecidableRel (exteriorPairGraph G s).Adj :=
  by
    classical
    exact fun _ _ ↦ inferInstance

/-- An entry of the exterior incidence Gram matrix counts common ambient
neighbors outside the cut. -/
theorem exteriorGram_apply_eq_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)] (u v : s) :
    let p : V → Prop := fun x ↦ x ∈ s
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
    (B * Matrix.conjTranspose B) u v =
      ((Finset.univ.filter fun z : {z // z ∉ s} ↦
        G.Adj u.1 z.1 ∧ G.Adj v.1 z.1).card : ℂ) := by
  classical
  simp only [Matrix.mul_apply, Matrix.toBlock_apply,
    Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply,
    Complex.star_def]
  calc
    (∑ x : {z // z ∉ s},
        (if G.Adj u.1 x.1 then (1 : ℂ) else 0) *
          (starRingEnd ℂ) (if G.Adj v.1 x.1 then 1 else 0)) =
        ∑ x : {z // z ∉ s}, if G.Adj v.1 x.1 then
          if G.Adj u.1 x.1 then 1 else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hu : G.Adj u.1 x.1 <;>
        by_cases hv : G.Adj v.1 x.1 <;> simp [hu, hv]
    _ = ∑ x : {z // z ∉ s},
          if G.Adj u.1 x.1 ∧ G.Adj v.1 x.1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hu : G.Adj u.1 x.1 <;>
        by_cases hv : G.Adj v.1 x.1 <;> simp [hu, hv]
    _ = _ := by rw [Finset.sum_boole]

/-- If exterior common neighbors are unique and every diagonal exterior
count is six, the incidence Gram matrix is `6I` plus the exterior-pair
adjacency matrix. -/
theorem exteriorGram_eq_six_add_pairGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (hdiag : ∀ u : s,
      (Finset.univ.filter fun z : {z // z ∉ s} ↦
        G.Adj u.1 z.1 ∧ G.Adj u.1 z.1).card = 6)
    (hle : ∀ u v : s, u ≠ v →
      (Finset.univ.filter fun z : {z // z ∉ s} ↦
        G.Adj u.1 z.1 ∧ G.Adj v.1 z.1).card ≤ 1) :
    let p : V → Prop := fun x ↦ x ∈ s
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
    B * Matrix.conjTranspose B =
      (6 : ℂ) • (1 : Matrix s s ℂ) +
        (exteriorPairGraph G s).adjMatrix ℂ := by
  classical
  ext u v
  rw [exteriorGram_apply_eq_card]
  by_cases huv : u = v
  · subst v
    have hd := hdiag u
    simp only [and_self] at hd
    simp [hd, exteriorPairGraph]
  · have hc := hle u v huv
    by_cases hadj : (exteriorPairGraph G s).Adj u v
    · have hpos : 0 < (Finset.univ.filter fun z : {z // z ∉ s} ↦
          G.Adj u.1 z.1 ∧ G.Adj v.1 z.1).card := by
        obtain ⟨_huv, z, hzout, huz, hvz⟩ := hadj
        apply Finset.card_pos.mpr
        refine ⟨⟨z, hzout⟩, ?_⟩
        simp [huz, hvz]
      have hone : (Finset.univ.filter fun z : {z // z ∉ s} ↦
          G.Adj u.1 z.1 ∧ G.Adj v.1 z.1).card = 1 := by omega
      simp [hone, huv, hadj, SimpleGraph.adjMatrix_apply]
    · have hzero : (Finset.univ.filter fun z : {z // z ∉ s} ↦
          G.Adj u.1 z.1 ∧ G.Adj v.1 z.1).card = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        apply hadj
        exact ⟨huv, z.1, z.2, hz.1, hz.2⟩
      simp [hzero, huv, hadj, SimpleGraph.adjMatrix_apply]

/-- C4-freeness makes exterior common neighbors unique. -/
theorem exterior_common_card_le_one_of_noC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidablePred (· ∈ s)]
    (hfree : ¬ containsC4 V G) (u v : s) (huv : u ≠ v) :
    (Finset.univ.filter fun z : {z // z ∉ s} ↦
      G.Adj u.1 z.1 ∧ G.Adj v.1 z.1).card ≤ 1 := by
  classical
  let E : Finset {z // z ∉ s} :=
    Finset.univ.filter fun z ↦ G.Adj u.1 z.1 ∧ G.Adj v.1 z.1
  let e : {z // z ∉ s} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hsub : E.map e ⊆ G.neighborFinset u.1 ∩ G.neighborFinset v.1 := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact Finset.mem_inter.mpr ⟨
      (G.mem_neighborFinset u.1 w.1).mpr hw.1,
      (G.mem_neighborFinset v.1 w.1).mpr hw.2⟩
  calc
    E.card = (E.map e).card := (Finset.card_map e).symm
    _ ≤ (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card :=
      Finset.card_le_card hsub
    _ ≤ 1 := (not_containsC4_iff_forall_common_le_one G).mp hfree
      u.1 v.1 (fun h ↦ huv (Subtype.ext h))

/-- The actual exterior Gram matrix in the seven-component order-64 branch
is `6I` plus a six-regular simple graph on H16. -/
theorem orderSixtyFour_seven_components_exteriorGram_eq_six_add_sixRegular
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
      B * Matrix.conjTranspose B =
          (6 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
            (exteriorPairGraph G c.supp).adjMatrix ℂ ∧
        (∀ x : c.supp,
          (exteriorPairGraph G c.supp).degree x = 6) := by
  classical
  obtain ⟨c, hc16, htwo⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let A := (G.induce c.supp).adjMatrix ℂ
  let D := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ
  have hid :=
    orderSixtyFour_defectComponent_internal_sq_add_exteriorGram_complex
      G hfree hmin hcover c
  change A * A + B * Matrix.conjTranspose B =
      (7 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
        (FriendshipTheoremOQ01.onesMatrix c.supp).map
          (Int.castRingHom ℂ) - D at hid
  have hdiag : ∀ u : c.supp,
      (Finset.univ.filter fun z : {z // z ∉ c.supp} ↦
        G.Adj u.1 z.1 ∧ G.Adj u.1 z.1).card = 6 := by
    intro u
    have hAii : (A * A) u u = 2 := by
      dsimp [A]
      rw [(G.induce c.supp).adjMatrix_mul_self_apply_self]
      exact_mod_cast htwo u
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
      (6 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
        (exteriorPairGraph G c.supp).adjMatrix ℂ at hQ
  refine ⟨hQ, ?_⟩
  have hQone := orderSixtyFour_sixteenBlock_exteriorGram_mulVec_one
    G hfree hmin hcover c hc16 htwo
  change (B * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (12 : ℂ) • (fun _ ↦ 1) at hQone
  intro x
  have he := congrArg (fun M ↦ M.mulVec (fun _ ↦ (1 : ℂ)) x) hQ
  have hx := congrFun hQone x
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at he
  have hRadj : ((exteriorPairGraph G c.supp).adjMatrix ℂ).mulVec
      (fun _ ↦ 1) x =
      ((exteriorPairGraph G c.supp).degree x : ℂ) := by
    simpa using
      (SimpleGraph.adjMatrix_mulVec_const_apply
        (G := exteriorPairGraph G c.supp) (α := ℂ) (a := 1) (v := x))
  simp only [Pi.add_apply, Pi.smul_apply] at he hx
  rw [hRadj] at he
  simp at he
  norm_num at hx
  rw [hx] at he
  have hre := congrArg Complex.re he
  norm_num at hre
  have hnEq : 12 = 6 + (exteriorPairGraph G c.supp).degree x := by
    exact_mod_cast hre
  omega

/-- Consequently the actual H16 exterior Gram matrix has exact first and
second moments `96` and `672`. -/
theorem orderSixtyFour_seven_components_exteriorGram_moments
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
      let Q := B * Matrix.conjTranspose B
      Matrix.trace Q = 96 ∧ Matrix.trace (Q * Q) = 672 := by
  classical
  obtain ⟨c, hc16, hQ, hreg⟩ :=
    orderSixtyFour_seven_components_exteriorGram_eq_six_add_sixRegular
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  have hcard : Fintype.card c.supp = 16 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp)
      _ = 16 := hc16
  dsimp only
  rw [hQ]
  exact six_add_sixRegularAdj_trace_and_secondMoment
    (exteriorPairGraph G c.supp) hcard hreg

end

end Erdos85

import Proofs.Erdos85LambdaSixExteriorAdmissibility
import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85LambdaSixRestrictedOwnerFactorization
import Proofs.Erdos85OrderSixtyFourTriangleFreeColorOrder

/-! # The graph defect is the forced lambda-six defect -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- On a component with positive internal degree, the induced second-order
defect is exactly the complement of the union of the internal and exterior
common-neighbor supports. -/
theorem inducedSecondOrderDefect_adj_iff_not_internal_or_exterior
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpos : ∀ x : c.supp, 0 < (G.induce c.supp).degree x)
    (x y : c.supp) :
    ((secondOrderDefectGraph G).induce c.supp).Adj x y ↔
      ¬ ((∃ z : c.supp,
          (G.induce c.supp).Adj x z ∧ (G.induce c.supp).Adj y z) ∨
        (exteriorPairGraph G c.supp).Adj x y) := by
  by_cases hxy : x = y
  · subst y
    constructor
    · intro hD
      exact (((secondOrderDefectGraph G).induce c.supp).loopless.irrefl x hD).elim
    · intro hnone
      exfalso
      apply hnone
      left
      have hcard : 0 < ((G.induce c.supp).neighborFinset x).card := by
        rw [(G.induce c.supp).card_neighborFinset_eq_degree]
        exact hpos x
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
      exact ⟨z, ((G.induce c.supp).mem_neighborFinset x z).mp hz,
        ((G.induce c.supp).mem_neighborFinset x z).mp hz⟩
  · have hxyVal : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    change (secondOrderDefectGraph G).Adj x.1 y.1 ↔ _
    rw [secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hxyVal]
    constructor
    · intro hzero
      rintro (hint | hext)
      · obtain ⟨z, hxz, hyz⟩ := hint
        have hz : z.1 ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
          simp only [Finset.mem_inter, G.mem_neighborFinset]
          exact ⟨hxz, hyz⟩
        have : 0 < (G.neighborFinset x.1 ∩ G.neighborFinset y.1).card :=
          Finset.card_pos.mpr ⟨z.1, hz⟩
        omega
      · obtain ⟨_, z, hzout, hxz, hyz⟩ := hext
        have hz : z ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
          simp only [Finset.mem_inter, G.mem_neighborFinset]
          exact ⟨hxz, hyz⟩
        have : 0 < (G.neighborFinset x.1 ∩ G.neighborFinset y.1).card :=
          Finset.card_pos.mpr ⟨z, hz⟩
        omega
    · intro hnone
      apply Nat.eq_zero_of_not_pos
      intro hcard
      obtain ⟨z, hz⟩ := Finset.card_pos.mp hcard
      simp only [Finset.mem_inter, G.mem_neighborFinset] at hz
      by_cases hzin : z ∈ c.supp
      · apply hnone
        left
        exact ⟨⟨z, hzin⟩, hz.1, hz.2⟩
      · apply hnone
        right
        exact ⟨hxy, z, hzin, hz.1, hz.2⟩

/-- Boolean-coordinate version of the forced-defect identity. -/
theorem relabeled_inducedSecondOrderDefect_eq_forcedRelation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpos : ∀ x : c.supp, 0 < (G.induce c.supp).degree x)
    (e : c.supp ≃ Fin 16) (x y : Fin 16) :
    relabeledGraphBool e ((secondOrderDefectGraph G).induce c.supp) x y =
      !(relabeledCommonNeighborBool e (G.induce c.supp) x y ||
        relabeledGraphBool e (exteriorPairGraph G c.supp) x y) := by
  have hiff := inducedSecondOrderDefect_adj_iff_not_internal_or_exterior
    G hfree c hpos (e.symm x) (e.symm y)
  simp only [relabeledGraphBool, relabeledCommonNeighborBool]
  rw [← Bool.decide_or, ← decide_not]
  exact decide_eq_decide.mpr hiff

/-- Bit-vector form consumed verbatim by the lambda-six classification
terminal. -/
theorem relabeled_inducedSecondOrderDefect_matrixBV_eq_forcedDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpos : ∀ x : c.supp, 0 < (G.induce c.supp).degree x)
    (e : c.supp ≃ Fin 16) :
    matrixBV (relabeledGraphBool e
        ((secondOrderDefectGraph G).induce c.supp)) =
      lambdaSixForcedDefect
        (matrixBV (relabeledCommonNeighborBool e (G.induce c.supp)))
        (matrixBV (relabeledGraphBool e
          (exteriorPairGraph G c.supp))) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let x : Fin 16 := ⟨i / 16, by omega⟩
  let y : Fin 16 := ⟨i % 16, Nat.mod_lt _ (by omega)⟩
  have hrel := relabeled_inducedSecondOrderDefect_eq_forcedRelation
    G hfree c hpos e x y
  have hiEq : x.val * 16 + y.val = i := by
    dsimp [x, y]
    omega
  rw [← hiEq]
  change bitAdj256
      (matrixBV (relabeledGraphBool e
        ((secondOrderDefectGraph G).induce c.supp))) x y =
    bitAdj256
      (lambdaSixForcedDefect
        (matrixBV (relabeledCommonNeighborBool e (G.induce c.supp)))
        (matrixBV (relabeledGraphBool e
          (exteriorPairGraph G c.supp)))) x y
  rw [bitAdj_matrixBV]
  have hidx : x.val * 16 + y.val < 256 := by omega
  simp only [lambdaSixForcedDefect, bitAdj256, BitVec.getLsbD_not,
    BitVec.getLsbD_or, hidx, decide_true, true_and]
  have hh2 :
      (matrixBV (relabeledCommonNeighborBool e (G.induce c.supp))).getLsbD
          (x.val * 16 + y.val) =
        relabeledCommonNeighborBool e (G.induce c.supp) x y := by
    simpa [bitAdj256] using
      bitAdj_matrixBV (relabeledCommonNeighborBool e (G.induce c.supp)) x y
  have hR :
      (matrixBV (relabeledGraphBool e
        (exteriorPairGraph G c.supp))).getLsbD (x.val * 16 + y.val) =
        relabeledGraphBool e (exteriorPairGraph G c.supp) x y := by
    simpa [bitAdj256] using
      bitAdj_matrixBV
        (relabeledGraphBool e (exteriorPairGraph G c.supp)) x y
  rw [hh2, hR]
  simpa [Bool.not_or] using hrel

/-- Exact forced-defect identity in the canonical `[10,6]` coordinates. -/
theorem tenSixComponentLabeling_inducedDefect_matrixBV_eq_forcedDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpos : ∀ x : c.supp, 0 < (G.induce c.supp).degree x)
    (label : TenSixComponentLabeling (G.induce c.supp)) :
    matrixBV (relabeledGraphBool label.toEquiv
        ((secondOrderDefectGraph G).induce c.supp)) =
      lambdaSixForcedDefect lambdaSixTenSixH2Support256
        (matrixBV (relabeledGraphBool label.toEquiv
          (exteriorPairGraph G c.supp))) := by
  rw [← (tenSixComponentLabeling_matrixBV_encodings
    (G.induce c.supp) label).2]
  exact relabeled_inducedSecondOrderDefect_matrixBV_eq_forcedDefect
    G hfree c hpos label.toEquiv

/-- Exact forced-defect identity in the canonical `[5,5,3,3]` coordinates. -/
theorem fiveFiveThreeThreeComponentLabeling_inducedDefect_matrixBV_eq_forcedDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hpos : ∀ x : c.supp, 0 < (G.induce c.supp).degree x)
    (label : FiveFiveThreeThreeComponentLabeling (G.induce c.supp)) :
    matrixBV (relabeledGraphBool label.toEquiv
        ((secondOrderDefectGraph G).induce c.supp)) =
      lambdaSixForcedDefect lambdaSixFiveFiveThreeThreeH2Support256
        (matrixBV (relabeledGraphBool label.toEquiv
          (exteriorPairGraph G c.supp))) := by
  rw [← (fiveFiveThreeThreeComponentLabeling_matrixBV_encodings
    (G.induce c.supp) label).2]
  exact relabeled_inducedSecondOrderDefect_matrixBV_eq_forcedDefect
    G hfree c hpos label.toEquiv

/-- The all-sixteen partition canonically has enough cardinality information
to enumerate its four components by `Fin 4`. -/
theorem orderSixtyFour_exists_finFour_equiv_components_of_allSixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    Nonempty (Fin 4 ≃ (secondOrderDefectGraph G).ConnectedComponent) := by
  have hcount := orderSixtyFour_defectComponent_count_eq_four_of_allSixteen
    G hsize
  exact ⟨(Fintype.equivFinOfCardEq hcount).symm⟩

/-- The complete structural lambda-six pipeline for a `[10,6]` source:
classification and the four owner factors force the bipartite defect tag. -/
theorem orderSixtyFour_tenSix_ownerFactors_force_bipartite
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (owners : Fin 4 ≃ (secondOrderDefectGraph G).ConnectedComponent)
    (source : (secondOrderDefectGraph G).ConnectedComponent)
    (label : TenSixComponentLabeling (G.induce source.supp)) :
    ∃ p : Fin 16 → Fin 16,
      lambdaSixRelabelsTo
        (matrixBV (relabeledGraphBool label.toEquiv
          ((secondOrderDefectGraph G).induce source.supp)))
        lambdaSixTenSixBipartiteD p := by
  have hlocal : ∀ x : source.supp,
      (G.induce source.supp).degree x = 2 := fun x =>
    binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (q := 8) (by omega) hreg (by simp) source (hsize source) x
  let r := matrixBV (relabeledGraphBool label.toEquiv
    (exteriorPairGraph G source.supp))
  have hr : lambdaSixAdmissibleR lambdaSixTenSixH256
      lambdaSixTenSixH2Support256 r := by
    exact orderSixtyFour_tenSix_exteriorPair_lambdaSixAdmissibleR
      G hfree (fun x => by rw [hreg])
        (fun {_ _} _ => Or.inl (hreg _)) source (hsize source) hlocal label
  have hd := tenSixComponentLabeling_inducedDefect_matrixBV_eq_forcedDefect
    G hfree source (fun x => by rw [hlocal]; omega) label
  have hf := orderSixtyFour_restrictedOwners_lambdaSixBoolFourFactorization
    G hfree hreg hsize owners source label.toEquiv
  exact lambdaSixTenSix_admissible_fourFactorization_forces_bipartite
    hr hd hf

/-- The complete structural lambda-six pipeline for a `[5,5,3,3]` source:
classification and the four owner factors force the bipartite defect tag. -/
theorem orderSixtyFour_fiveFiveThreeThree_ownerFactors_force_bipartite
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (owners : Fin 4 ≃ (secondOrderDefectGraph G).ConnectedComponent)
    (source : (secondOrderDefectGraph G).ConnectedComponent)
    (label : FiveFiveThreeThreeComponentLabeling
      (G.induce source.supp)) :
    ∃ p : Fin 16 → Fin 16,
      lambdaSixRelabelsTo
        (matrixBV (relabeledGraphBool label.toEquiv
          ((secondOrderDefectGraph G).induce source.supp)))
        lambdaSixFiveFiveThreeThreeBipartiteD p := by
  have hlocal : ∀ x : source.supp,
      (G.induce source.supp).degree x = 2 := fun x =>
    binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (q := 8) (by omega) hreg (by simp) source (hsize source) x
  let r := matrixBV (relabeledGraphBool label.toEquiv
    (exteriorPairGraph G source.supp))
  have hr : lambdaSixAdmissibleR lambdaSixFiveFiveThreeThreeH256
      lambdaSixFiveFiveThreeThreeH2Support256 r := by
    exact orderSixtyFour_fiveFiveThreeThree_exteriorPair_lambdaSixAdmissibleR
      G hfree (fun x => by rw [hreg])
        (fun {_ _} _ => Or.inl (hreg _)) source (hsize source) hlocal label
  have hd :=
    fiveFiveThreeThreeComponentLabeling_inducedDefect_matrixBV_eq_forcedDefect
      G hfree source (fun x => by rw [hlocal]; omega) label
  have hf := orderSixtyFour_restrictedOwners_lambdaSixBoolFourFactorization
    G hfree hreg hsize owners source label.toEquiv
  exact lambdaSixFiveFiveThreeThree_admissible_fourFactorization_forces_bipartite
    hr hd hf

end

end Erdos85

import Proofs.Erdos85OneHighGraphPairingRefinement
import Proofs.Erdos85OneHighOddProfileSlotVariantCoverage
import Proofs.Erdos85OneHighRefinementPinnedCnfSatisfaction
import Proofs.Erdos85OneHighV2GraphLedgers

/-! # The graph pairing in canonical CNF edge slots

`oneHighGraphPairingRefinement` sorts matching edges by their full pair code,
which is the right representation for the finite table inventory.  Pinned CNF
units instead refer to the literal canonical leaf slots `01` and `23`.  This
file records that second representation directly, before proving that its
rowwise sort is the inventory refinement.
-/

namespace Erdos85

noncomputable section

/-- Unique missed branch label at one canonical leaf coordinate.  Callers use
this only at the matched offsets `0,1` and, in a two-edge row, `2,3`. -/
def oneHighGraphCanonicalSlotLabel
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) (offset : Fin 5) : Fin 8 :=
  let s := p.branchLabel.symm source
  p.branchLabel (oneHighMissingBranch G v p.mate s
    ((p.leafLabel s).symm offset).1)

/-- Reverse transport for miss literals: a zero original neighbor intersection
with branch `u` gives the corresponding true relabeled miss predicate. -/
theorem oneHighFamilyMissesBlock_of_original_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s u : {z : V // z ∈ G.neighborSet v}) (offset : Fin 5)
    (hzero : (G.neighborFinset ((leafLabel s).symm offset).1 ∩
      secondLayerBranch G v u).card = 0) :
    oneHighFamilyMissesBlock
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel))
      (oneHighFamilyVertex (branchLabel s) offset) (branchLabel u) := by
  intro target hadj
  let targetLocal : secondLayerBranch G v u :=
    (leafLabel u).symm target
  have hxdecode := oneHighLeafFinFortyEquiv_symm_familyVertex
    G hfree branchLabel leafLabel s offset
  have htdecode := oneHighLeafFinFortyEquiv_symm_familyVertex
    G hfree branchLabel leafLabel u target
  have hadjG : G.Adj ((leafLabel s).symm offset).1 targetLocal.1 := by
    have h := (oneHighRelabeledLeafGraph_adj G v
      (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel) _ _).mp hadj
    rw [hxdecode, htdecode] at h
    exact h
  have hmem : targetLocal.1 ∈
      G.neighborFinset ((leafLabel s).symm offset).1 ∩
        secondLayerBranch G v u := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr hadjG, targetLocal.2⟩
  have hpos : 0 < (G.neighborFinset ((leafLabel s).symm offset).1 ∩
      secondLayerBranch G v u).card :=
    Finset.card_pos.mpr ⟨targetLocal.1, hmem⟩
  omega

/-- Every coordinate marked matched by the family profile really has one
neighbor inside its original five-vertex branch. -/
theorem card_oneHighCanonicalSlot_internal_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) (offset : Fin 5)
    (hmatched : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source offset).val = true) :
    (G.neighborFinset
        ((p.leafLabel (p.branchLabel.symm source)).symm offset).1 ∩
      secondLayerBranch G v (p.branchLabel.symm source)).card = 1 := by
  let R := oneHighRelabeledLeafGraph G v
    (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)
  let x := oneHighFamilyVertex source offset
  let partner : Fin 40 := oneHighFamilyV2PartnerFin p.profile x hmatched
  let targetOffset : Fin 5 := Fin.modNat (m := 8) (n := 5) partner
  have hpartnerAdj : R.Adj x partner := by
    exact oneHighFamilyV2PartnerVertex_adj p.profile R p.constraints
      x.isLt hmatched
  have hpartnerDiv : Fin.divNat (m := 8) (n := 5) partner = source := by
    apply Fin.ext
    exact (oneHighFamilyV2PartnerVertex_div x.isLt).trans
      (congrArg Fin.val (oneHighFamilyVertex_divNat source offset))
  have hpartnerVertex : partner = oneHighFamilyVertex source targetOffset := by
    apply Fin.ext
    have hdiv := congrArg Fin.val hpartnerDiv
    have hmod := Nat.mod_add_div partner.val 5
    have hoffset : targetOffset.val = partner.val % 5 := rfl
    change partner.val = targetOffset.val + 5 * source.val
    change partner.val / 5 = source.val at hdiv
    omega
  have hadjR : R.Adj (oneHighFamilyVertex source offset)
      (oneHighFamilyVertex source targetOffset) := by
    simpa [x, hpartnerVertex] using hpartnerAdj
  have hxdecode := oneHighLeafFinFortyEquiv_symm_familyVertex
    G hfree p.branchLabel p.leafLabel
      (p.branchLabel.symm source) offset
  have htdecode := oneHighLeafFinFortyEquiv_symm_familyVertex
    G hfree p.branchLabel p.leafLabel
      (p.branchLabel.symm source) targetOffset
  have hadjG : G.Adj
      ((p.leafLabel (p.branchLabel.symm source)).symm offset).1
      ((p.leafLabel (p.branchLabel.symm source)).symm targetOffset).1 := by
    have h := (oneHighRelabeledLeafGraph_adj G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel) _ _).mp
        hadjR
    simp only [p.branchLabel.apply_symm_apply] at hxdecode htdecode
    rw [hxdecode, htdecode] at h
    exact h
  have hpos : 0 < (G.neighborFinset
        ((p.leafLabel (p.branchLabel.symm source)).symm offset).1 ∩
      secondLayerBranch G v (p.branchLabel.symm source)).card := by
    apply Finset.card_pos.mpr
    refine ⟨((p.leafLabel (p.branchLabel.symm source)).symm targetOffset).1,
      Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · exact (G.mem_neighborFinset _ _).mpr hadjG
    · exact ((p.leafLabel (p.branchLabel.symm source)).symm targetOffset).2
  have hle := degree_induce_secondLayerBranch_le_one G hfree v
    (p.branchLabel.symm source)
    ⟨((p.leafLabel (p.branchLabel.symm source)).symm offset).1,
      ((p.leafLabel (p.branchLabel.symm source)).symm offset).2⟩
  rw [degree_induce_secondLayerBranch_eq_card_inter] at hle
  have hle' : (G.neighborFinset
        ((p.leafLabel (p.branchLabel.symm source)).symm offset).1 ∩
      secondLayerBranch G v (p.branchLabel.symm source)).card ≤ 1 := by
    exact hle
  omega

/-- The graph-defined label at a matched canonical slot is a genuine miss
literal in the relabeled forty-vertex graph. -/
theorem oneHighGraphCanonicalSlotLabel_missesBlock
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) (offset : Fin 5)
    (hmatched : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source offset).val = true) :
    oneHighFamilyMissesBlock
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
      (oneHighFamilyVertex source offset)
      (oneHighGraphCanonicalSlotLabel G hfree p source offset) := by
  let s := p.branchLabel.symm source
  let x := ((p.leafLabel s).symm offset).1
  let u := oneHighMissingBranch G v p.mate s x
  have hxMatched : (G.neighborFinset x ∩
      secondLayerBranch G v s).card = 1 := by
    simpa [s, x] using card_oneHighCanonicalSlot_internal_eq_one
      G hfree p source offset hmatched
  have hu := oneHighMissingBranch_mem_of_matched
    G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj
      s x ((p.leafLabel s).symm offset).2 hxMatched
  have hzero : (G.neighborFinset x ∩ secondLayerBranch G v u).card = 0 :=
    (Finset.mem_filter.mp hu).2
  simpa [oneHighGraphCanonicalSlotLabel, s, x, u] using
    oneHighFamilyMissesBlock_of_original_zero
      G hfree p.branchLabel p.leafLabel s u offset hzero

/-- Boolean named-atom form of the preceding graph miss fact. -/
theorem oneHighGraphCanonicalSlotLabel_atomValue
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) (offset : Fin 5)
    (hmatched : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source offset).val = true) :
    oneHighFamilyAtomValue
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
      (.miss (oneHighFamilyVertex source offset).val
        (oneHighGraphCanonicalSlotLabel G hfree p source offset).val) = true := by
  classical
  have hmiss := oneHighGraphCanonicalSlotLabel_missesBlock
    G hfree hv p source offset hmatched
  simp [oneHighFamilyAtomValue, hmiss]

/-- Miss-label pairs in the literal canonical matching-edge order. -/
def oneHighGraphCanonicalSlotRow
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) : List OneHighLabelPair :=
  let label := oneHighGraphCanonicalSlotLabel G hfree p source
  if oneHighFamilyInternalEdges p.profile source = 1 then
    [(label 0, label 1)]
  else
    [(label 0, label 1), (label 2, label 3)]

/-- The eight canonical-slot rows that the refinement-pinned CNF sees. -/
def oneHighGraphCanonicalSlotRefinement
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) :
    List (List OneHighLabelPair) :=
  List.ofFn fun source : Fin 8 =>
    oneHighGraphCanonicalSlotRow G hfree p source

@[simp] theorem oneHighGraphCanonicalSlotRefinement_length
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) :
    (oneHighGraphCanonicalSlotRefinement G hfree p).length = 8 := by
  simp [oneHighGraphCanonicalSlotRefinement]

theorem oneHighGraphCanonicalSlotRow_length
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    (oneHighGraphCanonicalSlotRow G hfree p source).length =
      oneHighFamilyInternalEdges p.profile source := by
  rw [oneHighGraphCanonicalSlotRow]
  by_cases h : oneHighFamilyInternalEdges p.profile source = 1
  · simp [h]
  · have htwo : oneHighFamilyInternalEdges p.profile source = 2 := by
      unfold oneHighFamilyInternalEdges at h ⊢
      split <;> simp_all
    simp [htwo]

/-- Fin-indexed form of the pin payload, convenient for the structural graph
proof before transporting through the outer eight-row `List.ofFn`. -/
def OneHighCanonicalSlotPinSemanticsFin
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) : Prop :=
  let R := oneHighRelabeledLeafGraph G v
    (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)
  ∀ source : Fin 8, ∀ edge,
    edge < (oneHighGraphCanonicalSlotRow G hfree p source).length →
    let pair := (oneHighGraphCanonicalSlotRow G hfree p source).getD edge (0, 0)
    oneHighFamilyAtomValue R (.miss (5 * source.val + 2 * edge) pair.1.val) = true ∧
      oneHighFamilyAtomValue R
        (.miss (5 * source.val + 2 * edge + 1) pair.2.val) = true

theorem oneHighGraphCanonicalSlotPinSemanticsFin
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) :
    OneHighCanonicalSlotPinSemanticsFin G hfree p := by
  intro source edge hedge
  by_cases hone : oneHighFamilyInternalEdges p.profile source = 1
  · have hedge0 : edge = 0 := by
      simpa [oneHighGraphCanonicalSlotRow, hone] using hedge
    subst edge
    have hm0 : oneHighFamilyVertexMatched p.profile
        (oneHighFamilyVertex source 0).val = true := by
      simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
    have hm1 : oneHighFamilyVertexMatched p.profile
        (oneHighFamilyVertex source 1).val = true := by
      simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
    simpa [oneHighGraphCanonicalSlotRow, hone, oneHighFamilyVertex_val] using And.intro
      (oneHighGraphCanonicalSlotLabel_atomValue
        G hfree hv p source 0 hm0)
      (oneHighGraphCanonicalSlotLabel_atomValue
        G hfree hv p source 1 hm1)
  · have htwo : oneHighFamilyInternalEdges p.profile source = 2 := by
      unfold oneHighFamilyInternalEdges at hone ⊢
      split <;> simp_all
    have htwoCond : source.val % 2 = 1 ∨ p.profile ≤ source.val / 2 := by
      unfold oneHighFamilyInternalEdges at htwo
      split at htwo
      · omega
      · have hmod := Nat.mod_lt source.val (by omega : 0 < 2)
        omega
    have hedgeCases : edge = 0 ∨ edge = 1 := by
      have : edge < 2 := by
        simpa [oneHighGraphCanonicalSlotRow, hone] using hedge
      omega
    rcases hedgeCases with rfl | rfl
    · have hm0 : oneHighFamilyVertexMatched p.profile
          (oneHighFamilyVertex source 0).val = true := by
        simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
      have hm1 : oneHighFamilyVertexMatched p.profile
          (oneHighFamilyVertex source 1).val = true := by
        simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
      simpa [oneHighGraphCanonicalSlotRow, hone, oneHighFamilyVertex_val] using And.intro
        (oneHighGraphCanonicalSlotLabel_atomValue
          G hfree hv p source 0 hm0)
        (oneHighGraphCanonicalSlotLabel_atomValue
          G hfree hv p source 1 hm1)
    · have hm2 : oneHighFamilyVertexMatched p.profile
          (oneHighFamilyVertex source 2).val = true := by
        simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
        omega
      have hm3 : oneHighFamilyVertexMatched p.profile
          (oneHighFamilyVertex source 3).val = true := by
        simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
        omega
      simpa [oneHighGraphCanonicalSlotRow, hone, oneHighFamilyVertex_val] using And.intro
        (oneHighGraphCanonicalSlotLabel_atomValue
          G hfree hv p source 2 hm2)
        (oneHighGraphCanonicalSlotLabel_atomValue
          G hfree hv p source 3 hm3)

/-- The actual eight-row graph slot refinement satisfies the generic semantic
payload consumed by the refinement-pinned CNF soundness theorem. -/
theorem oneHighGraphCanonicalSlotRefinement_pinSemantics
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) :
    OneHighRefinementPinSemantics
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
      (oneHighGraphCanonicalSlotRefinement G hfree p) := by
  intro source edge hedge
  by_cases hsource : source < 8
  · let sourceFin : Fin 8 := ⟨source, hsource⟩
    have hrow :
        (oneHighGraphCanonicalSlotRefinement G hfree p).getD source [] =
          oneHighGraphCanonicalSlotRow G hfree p sourceFin := by
      have hlength : source <
          (oneHighGraphCanonicalSlotRefinement G hfree p).length := by
        simpa using hsource
      rw [List.getD_eq_getElem
        (l := oneHighGraphCanonicalSlotRefinement G hfree p)
        (d := []) hlength]
      change (List.ofFn fun c : Fin 8 =>
        oneHighGraphCanonicalSlotRow G hfree p c).get
          ⟨source, by simpa using hsource⟩ = _
      rw [List.get_ofFn]
      congr
    have hfin := oneHighGraphCanonicalSlotPinSemanticsFin
      G hfree hv p sourceFin edge
    rw [hrow] at hedge ⊢
    simpa [sourceFin] using hfin hedge
  · have hrow :
        (oneHighGraphCanonicalSlotRefinement G hfree p).getD source [] = [] := by
      simp [oneHighGraphCanonicalSlotRefinement, hsource]
    rw [hrow] at hedge
    simp at hedge

end

end Erdos85

#print axioms Erdos85.oneHighGraphCanonicalSlotRow_length
#print axioms Erdos85.oneHighGraphCanonicalSlotPinSemanticsFin
#print axioms Erdos85.oneHighGraphCanonicalSlotRefinement_pinSemantics

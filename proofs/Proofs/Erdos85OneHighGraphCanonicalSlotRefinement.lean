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

/-- A matched canonical slot's selected missing label is genuinely far from
its source block and the source's standard mate block. -/
theorem oneHighGraphCanonicalSlotLabel_far
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) (offset : Fin 5)
    (hmatched : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source offset).val = true) :
    oneHighGraphCanonicalSlotLabel G hfree p source offset ≠ source ∧
      oneHighGraphCanonicalSlotLabel G hfree p source offset ≠
        oneHighStandardMate source := by
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
  have huBase := (Finset.mem_filter.mp hu).1
  have hum : u ≠ p.mate s := (Finset.mem_erase.mp huBase).1
  have hus : u ≠ s := (Finset.mem_erase.mp
    (Finset.mem_erase.mp huBase).2).1
  constructor
  · intro h
    apply hus
    apply p.branchLabel.injective
    simpa [oneHighGraphCanonicalSlotLabel, s, x, u] using h
  · intro h
    apply hum
    apply p.branchLabel.injective
    rw [p.branch_mate s]
    simpa [oneHighGraphCanonicalSlotLabel, s, x, u] using h

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

theorem oneHighGraphCanonicalSlotLabel_zero_le_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    oneHighGraphCanonicalSlotLabel G hfree p source 0 ≤
      oneHighGraphCanonicalSlotLabel G hfree p source 1 := by
  let R := oneHighRelabeledLeafGraph G v
    (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)
  let l0 := oneHighGraphCanonicalSlotLabel G hfree p source 0
  let l1 := oneHighGraphCanonicalSlotLabel G hfree p source 1
  have hm0 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 0).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
  have hm1 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 1).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
  have hf0 := oneHighGraphCanonicalSlotLabel_far
    G hfree hv p source 0 hm0
  have hf1 := oneHighGraphCanonicalSlotLabel_far
    G hfree hv p source 1 hm1
  have hmiss0 := oneHighGraphCanonicalSlotLabel_missesBlock
    G hfree hv p source 0 hm0
  have hmiss1 := oneHighGraphCanonicalSlotLabel_missesBlock
    G hfree hv p source 1 hm1
  by_contra hle
  have hgt : l0.val > l1.val := by omega
  have hlex := p.constraints.lex source l0 l1
    hf0.1 hf0.2 hf1.1 hf1.2 hgt
  exact hlex.1 ⟨hmiss0, hmiss1⟩

theorem oneHighGraphCanonicalSlotLabel_two_le_three
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8)
    (htwo : oneHighFamilyInternalEdges p.profile source = 2) :
    oneHighGraphCanonicalSlotLabel G hfree p source 2 ≤
      oneHighGraphCanonicalSlotLabel G hfree p source 3 := by
  let l2 := oneHighGraphCanonicalSlotLabel G hfree p source 2
  let l3 := oneHighGraphCanonicalSlotLabel G hfree p source 3
  have hcond : source.val % 2 = 1 ∨ p.profile ≤ source.val / 2 := by
    unfold oneHighFamilyInternalEdges at htwo
    split at htwo
    · omega
    · have hmod := Nat.mod_lt source.val (by omega : 0 < 2)
      omega
  have hm2 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 2).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
    omega
  have hm3 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 3).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
    omega
  have hf2 := oneHighGraphCanonicalSlotLabel_far
    G hfree hv p source 2 hm2
  have hf3 := oneHighGraphCanonicalSlotLabel_far
    G hfree hv p source 3 hm3
  have hmiss2 := oneHighGraphCanonicalSlotLabel_missesBlock
    G hfree hv p source 2 hm2
  have hmiss3 := oneHighGraphCanonicalSlotLabel_missesBlock
    G hfree hv p source 3 hm3
  by_contra hle
  have hgt : l2.val > l3.val := by omega
  have hlex := p.constraints.lex source l2 l3
    hf2.1 hf2.2 hf3.1 hf3.2 hgt
  exact (hlex.2 htwo).1 ⟨hmiss2, hmiss3⟩

theorem oneHighGraphCanonicalSlotLabel_zero_le_two
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8)
    (htwo : oneHighFamilyInternalEdges p.profile source = 2) :
    oneHighGraphCanonicalSlotLabel G hfree p source 0 ≤
      oneHighGraphCanonicalSlotLabel G hfree p source 2 := by
  let l0 := oneHighGraphCanonicalSlotLabel G hfree p source 0
  let l2 := oneHighGraphCanonicalSlotLabel G hfree p source 2
  have hcond : source.val % 2 = 1 ∨ p.profile ≤ source.val / 2 := by
    unfold oneHighFamilyInternalEdges at htwo
    split at htwo
    · omega
    · have hmod := Nat.mod_lt source.val (by omega : 0 < 2)
      omega
  have hm0 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 0).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
  have hm2 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 2).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
    omega
  have hf0 := oneHighGraphCanonicalSlotLabel_far
    G hfree hv p source 0 hm0
  have hf2 := oneHighGraphCanonicalSlotLabel_far
    G hfree hv p source 2 hm2
  have hmiss0 := oneHighGraphCanonicalSlotLabel_missesBlock
    G hfree hv p source 0 hm0
  have hmiss2 := oneHighGraphCanonicalSlotLabel_missesBlock
    G hfree hv p source 2 hm2
  by_contra hle
  have hgt : l0.val > l2.val := by omega
  have hlex := p.constraints.lex source l0 l2
    hf0.1 hf0.2 hf2.1 hf2.2 hgt
  exact (hlex.2 htwo).2 ⟨hmiss0, hmiss2⟩

set_option maxHeartbeats 800000 in
/-- Any literal canonical internal edge contributes its oriented miss-label
pair to the graph's full-code-sorted source pairing. -/
theorem oneHighGraphCanonicalSlotPair_mem_sourcePairing
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (source : Fin 8) (left right : Fin 5)
    (hmleft : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source left).val = true)
    (hmright : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source right).val = true)
    (hadjR : (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)).Adj
        (oneHighFamilyVertex source left)
        (oneHighFamilyVertex source right))
    (hlabels : oneHighGraphCanonicalSlotLabel G hfree p source left ≤
      oneHighGraphCanonicalSlotLabel G hfree p source right) :
    (oneHighGraphCanonicalSlotLabel G hfree p source left,
      oneHighGraphCanonicalSlotLabel G hfree p source right) ∈
        oneHighGraphSourcePairing G hfree hv p source := by
  let s := p.branchLabel.symm source
  let H := G.induce (secondLayerBranch G v s)
  let xLocal := (p.leafLabel s).symm left
  let yLocal := (p.leafLabel s).symm right
  have hxDegree : H.degree xLocal = 1 := by
    rw [degree_induce_secondLayerBranch_eq_card_inter]
    simpa [H, s, xLocal] using card_oneHighCanonicalSlot_internal_eq_one
      G hfree p source left hmleft
  have hyDegree : H.degree yLocal = 1 := by
    rw [degree_induce_secondLayerBranch_eq_card_inter]
    simpa [H, s, yLocal] using card_oneHighCanonicalSlot_internal_eq_one
      G hfree p source right hmright
  let xm : OneHighMatchedBranchVertices G v s := ⟨xLocal, hxDegree⟩
  let ym : OneHighMatchedBranchVertices G v s := ⟨yLocal, hyDegree⟩
  have hxdecode := oneHighLeafFinFortyEquiv_symm_familyVertex
    G hfree p.branchLabel p.leafLabel s left
  have hydecode := oneHighLeafFinFortyEquiv_symm_familyVertex
    G hfree p.branchLabel p.leafLabel s right
  have hadjG : G.Adj xLocal.1 yLocal.1 := by
    have h := (oneHighRelabeledLeafGraph_adj G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel) _ _).mp
        hadjR
    have hs : p.branchLabel s = source := p.branchLabel.apply_symm_apply source
    rw [hs] at hxdecode hydecode
    rw [hxdecode, hydecode] at h
    exact h
  have hadjH : H.Adj xLocal yLocal := hadjG
  let M := oneHighInternalMate G hfree v s
  have hMym : M xm = ym := by
    apply Subtype.ext
    have hMmem : (M xm).1 ∈ H.neighborFinset xm.1 :=
      (H.mem_neighborFinset _ _).mpr (by
        simpa [M, oneHighInternalMate, H] using degreeOneMate_adj H
          (degree_induce_secondLayerBranch_le_one G hfree v s) xm)
    have hymem : ym.1 ∈ H.neighborFinset xm.1 :=
      (H.mem_neighborFinset _ _).mpr (by simpa [xm, ym] using hadjH)
    have hone : (H.neighborFinset xm.1).card = 1 := by
      simpa [H.card_neighborFinset_eq_degree] using xm.2
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hone
    rw [hz] at hMmem hymem
    have hMz : (M xm).1 = z := by simpa using hMmem
    have hyz : ym.1 = z := by simpa using hymem
    exact hMz.trans hyz.symm
  let rootLabel := oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj s
  let label := fun z => p.branchLabel (rootLabel z)
  have hlabelX : label xm =
      oneHighGraphCanonicalSlotLabel G hfree p source left := by
    rfl
  have hlabelY : label ym =
      oneHighGraphCanonicalSlotLabel G hfree p source right := by
    rfl
  have hinv : Function.Involutive M := degreeOneMate_involutive _ _
  have hne : M xm ≠ xm := degreeOneMate_ne _ _ xm
  have hmem : (min (label xm) (label (M xm)),
      max (label xm) (label (M xm))) ∈
      matchingPairingListSorted M label := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm : M xm ∈ matchingEdgeSources M := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change M xm < M (M xm)
        rw [hinv xm]
        exact hlt
      have hc := canonicalPair_mem_matchingPairingListSorted_of_mem_source
        M label hm
      rw [hinv xm, min_comm (label (M xm)) (label xm),
        max_comm (label (M xm)) (label xm)] at hc
      exact hc
    · exact canonicalPair_mem_matchingPairingListSorted_of_mem_source M label
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
  rw [hMym, hlabelX, hlabelY, min_eq_left hlabels,
    max_eq_right hlabels] at hmem
  rw [oneHighGraphSourcePairing]
  change _ ∈ matchingPairingListSorted M label
  exact hmem

theorem oneHighGraphCanonicalSlotPair_zero_one_mem_sourcePairing
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8) :
    (oneHighGraphCanonicalSlotLabel G hfree p source 0,
      oneHighGraphCanonicalSlotLabel G hfree p source 1) ∈
        oneHighGraphSourcePairing G hfree hv p source := by
  have hm0 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 0).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
  have hm1 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 1).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
  have hadj : (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)).Adj
        (oneHighFamilyVertex source 0) (oneHighFamilyVertex source 1) := by
    apply of_decide_eq_true
    rw [p.constraints.relation.1 _ _ (by simp)]
    simp [oneHighCanonicalBranchAdj]
  exact oneHighGraphCanonicalSlotPair_mem_sourcePairing
    G hfree hv p source 0 1 hm0 hm1 hadj
      (oneHighGraphCanonicalSlotLabel_zero_le_one G hfree hv p source)

theorem oneHighGraphCanonicalSlotPair_two_three_mem_sourcePairing
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8)
    (htwo : oneHighFamilyInternalEdges p.profile source = 2) :
    (oneHighGraphCanonicalSlotLabel G hfree p source 2,
      oneHighGraphCanonicalSlotLabel G hfree p source 3) ∈
        oneHighGraphSourcePairing G hfree hv p source := by
  have hcond : source.val % 2 = 1 ∨ p.profile ≤ source.val / 2 := by
    unfold oneHighFamilyInternalEdges at htwo
    split at htwo
    · omega
    · have hmod := Nat.mod_lt source.val (by omega : 0 < 2)
      omega
  have hm2 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 2).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
    omega
  have hm3 : oneHighFamilyVertexMatched p.profile
      (oneHighFamilyVertex source 3).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
    omega
  have hflag : oneHighFamilyTwoEdges p.profile source = true := by
    simp [oneHighFamilyTwoEdges, hcond]
  have hadj : (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)).Adj
        (oneHighFamilyVertex source 2) (oneHighFamilyVertex source 3) := by
    apply of_decide_eq_true
    rw [p.constraints.relation.1 _ _ (by simp)]
    simp [oneHighCanonicalBranchAdj, hflag]
  exact oneHighGraphCanonicalSlotPair_mem_sourcePairing
    G hfree hv p source 2 3 hm2 hm3 hadj
      (oneHighGraphCanonicalSlotLabel_two_le_three
        G hfree hv p source htwo)

/-- A one-edge graph row is already the unique sorted inventory row and hence
its sole canonical-slot variant. -/
theorem oneHighGraphCanonicalSlotRow_mem_variants_of_internalEdges_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8)
    (hone : oneHighFamilyInternalEdges p.profile source = 1) :
    oneHighGraphCanonicalSlotRow G hfree p source ∈
      oneHighPairingRowSlotVariants
        (oneHighGraphSourcePairing G hfree hv p source) := by
  let pair : OneHighLabelPair :=
    (oneHighGraphCanonicalSlotLabel G hfree p source 0,
      oneHighGraphCanonicalSlotLabel G hfree p source 1)
  have hlen := oneHighGraphSourcePairing_length G hfree hv p source
  rw [hone] at hlen
  obtain ⟨stored, hstored⟩ := List.length_eq_one_iff.mp hlen
  have hmem := oneHighGraphCanonicalSlotPair_zero_one_mem_sourcePairing
    G hfree hv p source
  rw [hstored] at hmem
  have heq : stored = pair := (by simpa [pair] using hmem : pair = stored).symm
  subst stored
  rw [hstored]
  simp [oneHighGraphCanonicalSlotRow, hone,
    oneHighPairingRowSlotVariants, pair]

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

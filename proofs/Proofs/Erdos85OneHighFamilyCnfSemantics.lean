import Proofs.Erdos85OneHighCanonicalMate
import Proofs.Erdos85SequentialCounterReification

/-!
# Semantic atoms for the one-high family CNF

This file isolates the family-specific input to the generic Tseitin and
sequential-counter machinery.  In particular, it proves that the generator's
paired-product atom `c(x,z)` is precisely the disjunction of its midpoint
atoms `t(x,w,z)` over the six blocks outside the paired endpoint blocks.
-/

namespace Erdos85

/-- Literal block/offset coordinate used by the Python generator. -/
def oneHighFamilyVertex (b : Fin 8) (r : Fin 5) : Fin 40 :=
  finProdFinEquiv (b, r)

@[simp] theorem oneHighFamilyVertex_divNat (b : Fin 8) (r : Fin 5) :
    Fin.divNat (m := 8) (n := 5) (oneHighFamilyVertex b r) = b := by
  exact congrArg Prod.fst
    ((finProdFinEquiv : Fin 8 × Fin 5 ≃ Fin 40).symm_apply_apply (b, r))

@[simp] theorem oneHighFamilyVertex_modNat (b : Fin 8) (r : Fin 5) :
    Fin.modNat (m := 8) (n := 5) (oneHighFamilyVertex b r) = r := by
  exact congrArg Prod.snd
    ((finProdFinEquiv : Fin 8 × Fin 5 ≃ Fin 40).symm_apply_apply (b, r))

/-- The midpoint domain used verbatim by `family_gen.py` for a standard-mate
pair of blocks. -/
def oneHighFamilyMidpoints (b : Fin 8) : Finset (Fin 40) :=
  Finset.univ.filter fun w =>
    Fin.divNat (m := 8) (n := 5) w ≠ b ∧
    Fin.divNat (m := 8) (n := 5) w ≠ oneHighStandardMate b

/-- Semantic value of the generator's Tseitin atom `t(x,w,z)`. -/
def oneHighFamilyTAtom (R : SimpleGraph (Fin 40))
    (x w z : Fin 40) : Prop :=
  R.Adj x w ∧ R.Adj w z

/-- Semantic value of the generator's paired-product atom `c(x,z)`. -/
def oneHighFamilyCAtom (R : SimpleGraph (Fin 40))
    [DecidableRel R.Adj] (b : Fin 8) (x z : Fin 40) : Prop :=
  (x, z) ∈ oneHighEncodedCommonPairBlock R b (oneHighStandardMate b)

/-- The 25 paired-product inputs counted by one generator equality block. -/
def oneHighFamilyCAtoms (R : SimpleGraph (Fin 40))
    [DecidableRel R.Adj] (b : Fin 8) : Finset (Fin 40 × Fin 40) :=
  oneHighEncodedCommonPairBlock R b (oneHighStandardMate b)

/-- Semantic value assigned to `missvar(w,b)`: all five edge variables from
`w` into block `b` are false. -/
def oneHighFamilyMissesBlock (R : SimpleGraph (Fin 40))
    (w : Fin 40) (b : Fin 8) : Prop :=
  ∀ r : Fin 5, ¬ R.Adj w (oneHighFamilyVertex b r)

/-- The three lexicographic symmetry-breaking clause families emitted for
each canonical matching block.  Writing them as forbidden inversions makes
the correspondence with Python's clauses `[-missvar(x,j),-missvar(y,k)]`
literal. -/
def OneHighPureFamilyLexConstraints
    (a : Nat) (R : SimpleGraph (Fin 40)) : Prop :=
  ∀ c j k : Fin 8,
    j ≠ c → j ≠ oneHighStandardMate c →
    k ≠ c → k ≠ oneHighStandardMate c → j.val > k.val →
    (¬(oneHighFamilyMissesBlock R (oneHighFamilyVertex c 0) j ∧
        oneHighFamilyMissesBlock R (oneHighFamilyVertex c 1) k)) ∧
    (oneHighFamilyInternalEdges a c = 2 →
      (¬(oneHighFamilyMissesBlock R (oneHighFamilyVertex c 2) j ∧
          oneHighFamilyMissesBlock R (oneHighFamilyVertex c 3) k)) ∧
      ¬(oneHighFamilyMissesBlock R (oneHighFamilyVertex c 0) j ∧
          oneHighFamilyMissesBlock R (oneHighFamilyVertex c 2) k))

/-- Complete semantic payload of the actual PURE CNF, including the lex WLOG
clauses that are deliberately absent from the label-invariant base relation
predicate. -/
structure OneHighPureFamilyCnfConstraints
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] : Prop where
  relation : OneHighPureFamilyRelationConstraints a R
  lex : OneHighPureFamilyLexConstraints a R

/-- The literal `(block,offset)` coordinate decodes to the corresponding
branch-local leaf. -/
theorem oneHighLeafFinFortyEquiv_symm_familyVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s : {z : V // z ∈ G.neighborSet v}) (r : Fin 5) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    (E.symm (oneHighFamilyVertex (branchLabel s) r)).1 =
      ((leafLabel s).symm r).1 := by
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let xLocal := (leafLabel s).symm r
  have hxSecond : xLocal.1 ∈ secondLayer G v := by
    rw [secondLayer]
    exact Finset.mem_biUnion.mpr
      ⟨s, Finset.mem_univ _, xLocal.2⟩
  let x : {z : V // z ∈ secondLayer G v} := ⟨xLocal.1, hxSecond⟩
  have howner : oneHighBranchOwner G v x = s :=
    oneHighBranchOwner_eq_of_mem G hfree v x s xLocal.2
  have hb := oneHighLeafFinFortyEquiv_divNat
    G hfree v branchLabel leafLabel x
  have hr := oneHighLeafFinFortyEquiv_modNat
    G hfree v branchLabel leafLabel x
  rw [howner] at hb
  have htransport := finsetEquiv_apply_transport
    (fun u => secondLayerBranch G v u) leafLabel howner xLocal
  have hr' : Fin.modNat (m := 8) (n := 5) (E x) = r := by
    calc
      _ = leafLabel (oneHighBranchOwner G v x)
          ⟨x.1, oneHighBranchOwner_mem G v x⟩ := by simpa [E] using hr
      _ = leafLabel s xLocal := by
        simpa [x] using htransport
      _ = r := (leafLabel s).apply_symm_apply r
  have hcoord : E x = oneHighFamilyVertex (branchLabel s) r := by
    apply Fin.ext
    change (E x).val = r.val + 5 * (branchLabel s).val
    have hbv := congrArg Fin.val hb
    have hrv := congrArg Fin.val hr'
    change (E x).val / 5 = (branchLabel s).val at hbv
    change (E x).val % 5 = r.val at hrv
    omega
  have := congrArg (fun y => y.1) (E.symm_apply_eq.mpr hcoord.symm)
  simpa [x, xLocal] using this

/-- A literal `missvar` truth value transports back to a zero-neighbor
intersection with the corresponding original second-layer branch. -/
theorem oneHighFamilyMissesBlock_original_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s : {z : V // z ∈ G.neighborSet v}) (r : Fin 5) (b : Fin 8)
    (hmiss : oneHighFamilyMissesBlock
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel))
      (oneHighFamilyVertex (branchLabel s) r) b) :
    (G.neighborFinset ((leafLabel s).symm r).1 ∩
      secondLayerBranch G v (branchLabel.symm b)).card = 0 := by
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let xLocal := (leafLabel s).symm r
  apply Finset.card_eq_zero.mpr
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨q, hq⟩
  have hq' := Finset.mem_inter.mp hq
  let u := branchLabel.symm b
  let qLocal : secondLayerBranch G v u := ⟨q, hq'.2⟩
  have hxdecode := oneHighLeafFinFortyEquiv_symm_familyVertex
    G hfree branchLabel leafLabel s r
  have hqdecode := oneHighLeafFinFortyEquiv_symm_familyVertex
    G hfree branchLabel leafLabel u (leafLabel u qLocal)
  have hadjR : (oneHighRelabeledLeafGraph G v E).Adj
      (oneHighFamilyVertex (branchLabel s) r)
      (oneHighFamilyVertex b (leafLabel u qLocal)) := by
    apply (oneHighRelabeledLeafGraph_adj G v E _ _).mpr
    rw [hxdecode]
    have hbu : branchLabel u = b := branchLabel.apply_symm_apply b
    rw [← hbu]
    rw [hqdecode]
    simpa [xLocal] using hq'.1
  exact hmiss (leafLabel u qLocal) hadjR

/-- For a matched canonical leaf, any true literal `missvar(w,b)` names its
unique graph-side missing branch. -/
theorem oneHighFamilyMissesBlock_eq_missingBranchLabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s : {z : V // z ∈ G.neighborSet v}) (r : Fin 5) (b : Fin 8)
    (hbne : b ≠ branchLabel s)
    (hbm : b ≠ oneHighStandardMate (branchLabel s))
    (hmatched : (G.neighborFinset ((leafLabel s).symm r).1 ∩
      secondLayerBranch G v s).card = 1)
    (hmiss : oneHighFamilyMissesBlock
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel))
      (oneHighFamilyVertex (branchLabel s) r) b) :
    b = branchLabel (oneHighMissingBranch G v mate s
      ((leafLabel s).symm r).1) := by
  let u := branchLabel.symm b
  have hus : u ≠ s := by
    intro hus
    apply hbne
    exact (branchLabel.apply_symm_apply b).symm.trans
      (congrArg branchLabel hus)
  have hum : u ≠ mate s := by
    intro hum
    apply hbm
    exact (branchLabel.apply_symm_apply b).symm.trans
      ((congrArg branchLabel hum).trans (hbranchMate s))
  have hzero := oneHighFamilyMissesBlock_original_zero
    G hfree branchLabel leafLabel s r b hmiss
  have hu : u ∈ oneHighFarMissBranches G v mate s
      ((leafLabel s).symm r).1 := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hzero⟩
    exact Finset.mem_erase.mpr ⟨hum, Finset.mem_erase.mpr
      ⟨hus, Finset.mem_univ u⟩⟩
  have heq := eq_oneHighMissingBranch_of_matched_of_mem
    G hfree hv hexternal houterDegree mate hmateAdj s
      ((leafLabel s).symm r).1 ((leafLabel s).symm r).2 hmatched u hu
  simpa [u] using congrArg branchLabel heq

theorem card_neighbor_inter_branch_eq_one_of_canonicalMatched
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V}
    (s : {z : V // z ∈ G.neighborSet v})
    (twoEdges : Bool) (e : secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj twoEdges (e x) (e y))
    (r : Fin 5) (hr : oneHighCanonicalBranchMatched twoEdges r) :
    (G.neighborFinset ((e.symm r).1) ∩ secondLayerBranch G v s).card = 1 := by
  rw [card_neighbor_inter_branch_eq_canonicalMatched
    G s twoEdges e hcanonical (e.symm r)]
  simp [hr]

theorem oneHighFamilyTwoEdges_eq_true_of_internalEdges_eq_two
    (a : Nat) (c : Fin 8)
    (h : oneHighFamilyInternalEdges a c = 2) :
    oneHighFamilyTwoEdges a c = true := by
  unfold oneHighFamilyInternalEdges at h
  unfold oneHighFamilyTwoEdges
  by_cases hp : c.val % 2 = 0 ∧ c.val / 2 < a
  · simp [hp] at h
  · simp [hp]

/-- The simultaneous generator labeling satisfies every literal miss-variable
lex clause after transport to Fin40 coordinates. -/
theorem oneHighPureFamilyLexConstraints_of_generatorLabels
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7)
    (mate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hmateAdj : ∀ s, G.Adj s.1 (mate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s,
      branchLabel (mate s) = oneHighStandardMate (branchLabel s))
    (twoEdges : {z : V // z ∈ G.neighborSet v} → Bool)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ s x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj (twoEdges s)
        (leafLabel s x) (leafLabel s y))
    (a : Nat)
    (hword : ∀ i, twoEdges (branchLabel.symm i) =
      oneHighFamilyTwoEdges a i)
    (hlex : ∀ s,
      branchLabel (oneHighMissingBranch G v mate s
          ((leafLabel s).symm 0).1) ≤
        branchLabel (oneHighMissingBranch G v mate s
          ((leafLabel s).symm 1).1) ∧
      (twoEdges s = true →
        branchLabel (oneHighMissingBranch G v mate s
            ((leafLabel s).symm 2).1) ≤
          branchLabel (oneHighMissingBranch G v mate s
            ((leafLabel s).symm 3).1) ∧
        branchLabel (oneHighMissingBranch G v mate s
            ((leafLabel s).symm 0).1) ≤
          branchLabel (oneHighMissingBranch G v mate s
            ((leafLabel s).symm 2).1))) :
    OneHighPureFamilyLexConstraints a
      (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel)) := by
  intro c j k hjc hjm hkc hkm hjk
  let s := branchLabel.symm c
  have hs : branchLabel s = c := branchLabel.apply_symm_apply c
  have matched (r : Fin 5)
      (hr : oneHighCanonicalBranchMatched (twoEdges s) r) :
      (G.neighborFinset ((leafLabel s).symm r).1 ∩
        secondLayerBranch G v s).card = 1 :=
    card_neighbor_inter_branch_eq_one_of_canonicalMatched
      G s (twoEdges s) (leafLabel s) (hcanonical s) r hr
  have missEq (r : Fin 5) (b : Fin 8)
      (hbc : b ≠ c) (hbm : b ≠ oneHighStandardMate c)
      (hr : oneHighCanonicalBranchMatched (twoEdges s) r)
      (hmiss : oneHighFamilyMissesBlock
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel))
        (oneHighFamilyVertex c r) b) :
      b = branchLabel (oneHighMissingBranch G v mate s
        ((leafLabel s).symm r).1) := by
    have hmiss' : oneHighFamilyMissesBlock
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel))
        (oneHighFamilyVertex (branchLabel s) r) b := by simpa [hs] using hmiss
    exact oneHighFamilyMissesBlock_eq_missingBranchLabel
      G hfree hv hexternal houterDegree mate hmateAdj branchLabel hbranchMate
        leafLabel s r b (by simpa [hs] using hbc) (by simpa [hs] using hbm)
        (matched r hr) hmiss'
  constructor
  · rintro ⟨hj, hk⟩
    have hej := missEq 0 j hjc hjm (by
      simp [oneHighCanonicalBranchMatched]) hj
    have hek := missEq 1 k hkc hkm (by
      simp [oneHighCanonicalBranchMatched]) hk
    have hle := (hlex s).1
    have : j ≤ k := by simpa [hej, hek] using hle
    omega
  · intro htwo
    have htwoEdges : twoEdges s = true := by
      rw [hword c]
      exact oneHighFamilyTwoEdges_eq_true_of_internalEdges_eq_two a c htwo
    constructor
    · rintro ⟨hj, hk⟩
      have hej := missEq 2 j hjc hjm (by
        simp [oneHighCanonicalBranchMatched, htwoEdges]) hj
      have hek := missEq 3 k hkc hkm (by
        simp [oneHighCanonicalBranchMatched, htwoEdges]) hk
      have hle := (hlex s).2 htwoEdges |>.1
      have : j ≤ k := by simpa [hej, hek] using hle
      omega
    · rintro ⟨hj, hk⟩
      have hej := missEq 0 j hjc hjm (by
        simp [oneHighCanonicalBranchMatched]) hj
      have hek := missEq 2 k hkc hkm (by
        simp [oneHighCanonicalBranchMatched, htwoEdges]) hk
      have hle := (hlex s).2 htwoEdges |>.2
      have : j ≤ k := by simpa [hej, hek] using hle
      omega

/-- Every raw one-high graph produces the complete semantic payload of the
actual PURE family CNF, including its miss-variable lex clauses. -/
theorem orderFortyNine_exists_pureFamilyCnfConstraints_of_one_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 1)
    {v : V} (hv : G.degree v = 8) :
    ∃ (a : Nat) (R : SimpleGraph (Fin 40)) (_ : DecidableRel R.Adj),
      a ≤ 4 ∧ OneHighPureFamilyCnfConstraints a R := by
  classical
  obtain ⟨mate, branchLabel, twoEdges, leafLabel,
      hmateInv, hmateAdj, _haug, hbranchMate, hfamily, hword, hlabels⟩ :=
    orderFortyNine_exists_simultaneous_familyGeneratorLabels
      G hfree hmin hcard hHigh hv
  let a := ((Finset.univ :
    Finset {z : V // z ∈ G.neighborSet v}).filter fun s =>
      highBranchMatchedCount G v s = 2).card
  let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  have hunique : ∀ {w : V}, G.degree w = 8 → w = v := by
    intro w hw
    have hvMem : v ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hv]
    have hwMem : w ∈ orderFortyNineHighVertices G := by
      simp [orderFortyNineHighVertices, hw]
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hHigh
    have hvz : v = z := by simpa [hz] using hvMem
    have hwz : w = z := by simpa [hz] using hwMem
    exact hwz.trans hvz.symm
  have hexternal : externalRepairCandidates G v = ∅ :=
    orderFortyNine_externalRepairCandidates_degreeEight_eq_empty
      G hfree hmin hcard hv
  have houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7 := by
    intro x hx
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard x with hx7 | hx8
    · exact hx7
    · have hxv := hunique hx8
      rw [secondLayer] at hx
      rcases Finset.mem_biUnion.mp hx with ⟨s, _, hxs⟩
      exact ((Finset.mem_sdiff.mp hxs).2 (by simp [hxv])).elim
  have ha : a ≤ 4 := by
    simpa [a, oneHighAEndpointSet] using card_oneHighAEndpointSet_le_four
      G hfree hmin hcard hv hunique hexternal houterDegree
        mate hmateInv hmateAdj
  have hstates : ∀ i,
      highBranchMatchedCount G v (branchLabel.symm i) = 2 ∨
      highBranchMatchedCount G v (branchLabel.symm i) = 4 := by
    intro i
    rcases (hlabels (branchLabel.symm i)).1 with hs | hs
    · exact Or.inl hs.2
    · exact Or.inr hs.2
  have hIN : ∀ i, highBranchMatchedCount G v (branchLabel.symm i) =
      2 * oneHighFamilyInternalEdges a i :=
    highBranchMatchedCount_eq_two_mul_familyInternalEdges
      G branchLabel a hfamily hstates
  refine ⟨a, R, inferInstance, ha, ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact oneHighRelabeledLeafGraph_adj_eq_familyInternal
        G hfree branchLabel twoEdges leafLabel (fun s => (hlabels s).2.1)
          a hword i j hij
    · intro i j hij
      exact oneHighRelabeledLeafGraph_not_adj_of_standardMate_blocks
        G hfree mate hmateAdj branchLabel hbranchMate leafLabel i j hij
    · intro i j hij
      exact oneHighRelabeledLeafGraph_common_le_one G hfree E i j hij
    · intro i j hij hblock
      exact oneHighRelabeledLeafGraph_sameBlock_common_eq_zero
        G hfree branchLabel leafLabel i j hij hblock
    · intro i k l hkl hblock
      exact oneHighRelabeledLeafGraph_not_adj_two_in_sameBlock
        G hfree branchLabel leafLabel i k l hkl hblock
    · intro i
      exact card_oneHighEncodedFarNeighbors_eq_familyFarDegree
        G hfree hexternal mate hmateAdj branchLabel hbranchMate twoEdges
          leafLabel (fun s => (hlabels s).2.1) a hword i
          (houterDegree (E.symm i).2)
    · intro b
      have hledger := card_oneHighEncodedCommonPairBlock_add_familyIN_eq_thirty
        G hfree hmin hcard hv hunique hexternal houterDegree mate hmateInv
          hmateAdj branchLabel hbranchMate leafLabel a hIN (branchLabel.symm b)
      simpa [R, E] using hledger
  · apply oneHighPureFamilyLexConstraints_of_generatorLabels
      G hfree hv hexternal houterDegree mate hmateAdj branchLabel hbranchMate
        twoEdges leafLabel (fun s => (hlabels s).2.1) a hword
    intro s
    exact ⟨(hlabels s).2.2.1, (hlabels s).2.2.2⟩

theorem oneHighFamily_endpoint_ne
    (b : Fin 8) (x z : Fin 40)
    (hx : Fin.divNat (m := 8) (n := 5) x = b)
    (hz : Fin.divNat (m := 8) (n := 5) z = oneHighStandardMate b) :
    x ≠ z := by
  intro h
  subst z
  exact oneHighStandardMate_ne b (hx.symm.trans hz).symm

/-- A common neighbor of vertices in standard-mate blocks cannot lie in
either endpoint block, because all edges between those blocks are fixed to
zero by the PURE family constraints. -/
theorem oneHighFamily_commonNeighbor_mem_midpoints
    {a : Nat} {R : SimpleGraph (Fin 40)} [DecidableRel R.Adj]
    (h : OneHighPureFamilyRelationConstraints a R)
    (b : Fin 8) (x z w : Fin 40)
    (hx : Fin.divNat (m := 8) (n := 5) x = b)
    (hz : Fin.divNat (m := 8) (n := 5) z = oneHighStandardMate b)
    (hxw : R.Adj x w) (hwz : R.Adj w z) :
    w ∈ oneHighFamilyMidpoints b := by
  rcases h with ⟨_hint, hmate, _hcommon, _hsame, _hone, _hfar, _hledger⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ w, ?_, ?_⟩
  · intro hw
    have hzero := hmate z w
    have : Fin.divNat (m := 8) (n := 5) w =
        oneHighStandardMate (Fin.divNat (m := 8) (n := 5) z) := by
      rw [hw, hz, oneHighStandardMate_involutive b]
    exact (hzero this) ((R.adj_comm w z).mp hwz)
  · intro hw
    have hzero := hmate x w
    have : Fin.divNat (m := 8) (n := 5) w =
        oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x) := by
      simpa [hx] using hw
    exact (hzero this) hxw

/-- Exact semantic reification of the paired-product OR gate emitted by
`family_gen.py`.  This theorem supplies the input-row truth values for the
paired-product equality counter. -/
theorem oneHighFamily_cAtom_iff_exists_tAtom
    {a : Nat} {R : SimpleGraph (Fin 40)} [DecidableRel R.Adj]
    (h : OneHighPureFamilyRelationConstraints a R)
    (b : Fin 8) (x z : Fin 40)
    (hx : Fin.divNat (m := 8) (n := 5) x = b)
    (hz : Fin.divNat (m := 8) (n := 5) z = oneHighStandardMate b) :
    oneHighFamilyCAtom R b x z ↔
      ∃ w ∈ oneHighFamilyMidpoints b, oneHighFamilyTAtom R x w z := by
  rcases h with ⟨hint, hmate, hcommon, hsame, hone, hfar, hledger⟩
  have hpure : OneHighPureFamilyRelationConstraints a R :=
    ⟨hint, hmate, hcommon, hsame, hone, hfar, hledger⟩
  have hxz : x ≠ z := oneHighFamily_endpoint_ne b x z hx hz
  constructor
  · intro hc
    have hcard : (R.neighborFinset x ∩ R.neighborFinset z).card = 1 := by
      exact (Finset.mem_filter.mp hc).2
    have hne : (R.neighborFinset x ∩ R.neighborFinset z).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨w, hw⟩ := hne
    have hw' := Finset.mem_inter.mp hw
    have hxw : R.Adj x w := by simpa using hw'.1
    have hzw : R.Adj z w := by simpa using hw'.2
    exact ⟨w,
      oneHighFamily_commonNeighbor_mem_midpoints hpure b x z w hx hz hxw
        ((R.adj_comm z w).mp hzw),
      hxw, (R.adj_comm z w).mp hzw⟩
  · rintro ⟨w, _hwdom, hxw, hwz⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, hz⟩
    · have hwcommon : w ∈ R.neighborFinset x ∩ R.neighborFinset z := by
        apply Finset.mem_inter.mpr
        constructor
        · simpa using hxw
        · simpa using (R.adj_comm w z).mp hwz
      have hpos : 0 < (R.neighborFinset x ∩ R.neighborFinset z).card :=
        Finset.card_pos.mpr ⟨w, hwcommon⟩
      have hle := hcommon x z hxz
      exact Nat.le_antisymm hle hpos

/-- Exact `CardEnc.equals` target for a paired-product row, in the same
subtraction form used by `family_gen.py`. -/
theorem oneHighFamily_cAtoms_card_eq_generatorBound
    {a : Nat} {R : SimpleGraph (Fin 40)} [DecidableRel R.Adj]
    (h : OneHighPureFamilyRelationConstraints a R) (b : Fin 8) :
    (oneHighFamilyCAtoms R b).card =
      30 - 2 * oneHighFamilyInternalEdges a b -
        2 * oneHighFamilyInternalEdges a (oneHighStandardMate b) := by
  rcases h with ⟨_hint, _hmate, _hcommon, _hsame, _hone, _hfar, hledger⟩
  have heq := hledger b
  change (oneHighEncodedCommonPairBlock R b
      (oneHighStandardMate b)).card = _
  omega

end Erdos85

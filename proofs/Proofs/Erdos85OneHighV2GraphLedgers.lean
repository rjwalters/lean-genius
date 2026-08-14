import Proofs.Erdos85OneHighV2Satisfaction

/-!
# Graph-side ledgers for the exact fleet-v2 replay

This file discharges the combinatorial payloads kept deliberately separate
from the byte-exact generator and its valuation/state mechanics.
-/

namespace Erdos85

theorem oneHighFamilyTablePairs_mem_bounds
    {pair : Nat × Nat} (h : pair ∈ oneHighFamilyTablePairs) :
    pair.1 < 8 ∧ pair.2 < 8 ∧ pair.1 < pair.2 ∧
      pair.2 ≠ (pair.1 ^^^ 1) := by
  native_decide +revert

theorem oneHighFamilyV2PartnerVertex_lt
    {a x : Nat} (hx : x < 40)
    (_hm : oneHighFamilyVertexMatched a x = true) :
    oneHighFamilyV2PartnerVertex x < 40 := by
  unfold oneHighFamilyV2PartnerVertex
  split <;> omega

theorem oneHighFamilyV2PartnerVertex_div
    {x : Nat} (hx : x < 40) :
    oneHighFamilyV2PartnerVertex x / 5 = x / 5 := by
  unfold oneHighFamilyV2PartnerVertex
  split <;> omega

theorem oneHighFamilyV2PartnerVertex_canonicalAdj
    (a : Nat) {x : Nat} (hx : x < 40)
    (hm : oneHighFamilyVertexMatched a x = true) :
    oneHighCanonicalBranchAdj
      (oneHighFamilyTwoEdges a (⟨x / 5, by omega⟩ : Fin 8))
      (⟨x % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5)
      (⟨oneHighFamilyV2PartnerVertex x % 5,
        Nat.mod_lt _ (by omega)⟩ : Fin 5) = true := by
  simp only [oneHighFamilyVertexMatched] at hm
  unfold oneHighFamilyV2PartnerVertex oneHighCanonicalBranchAdj
    oneHighFamilyTwoEdges
  split <;> simp_all [Fin.ext_iff] <;> omega

theorem oneHighFamilyV2PartnerVertex_adj
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    {x : Nat} (hx : x < 40)
    (hm : oneHighFamilyVertexMatched a x = true) :
    R.Adj (⟨x, hx⟩ : Fin 40)
      ⟨oneHighFamilyV2PartnerVertex x,
        oneHighFamilyV2PartnerVertex_lt hx hm⟩ := by
  have hrel := hc.relation.1 (⟨x, hx⟩ : Fin 40)
    (⟨oneHighFamilyV2PartnerVertex x,
      oneHighFamilyV2PartnerVertex_lt hx hm⟩ : Fin 40)
  have hdiv := oneHighFamilyV2PartnerVertex_div hx
  have heqDiv : Fin.divNat (m := 8) (n := 5) (⟨x, hx⟩ : Fin 40) =
      Fin.divNat (m := 8) (n := 5)
        (⟨oneHighFamilyV2PartnerVertex x,
          oneHighFamilyV2PartnerVertex_lt hx hm⟩ : Fin 40) := by
    apply Fin.ext
    exact hdiv.symm
  specialize hrel heqDiv
  have hcanon : oneHighCanonicalBranchAdj
      (oneHighFamilyTwoEdges a
        (Fin.divNat (m := 8) (n := 5) (⟨x, hx⟩ : Fin 40)))
      (Fin.modNat (m := 8) (n := 5) (⟨x, hx⟩ : Fin 40))
      (Fin.modNat (m := 8) (n := 5)
        (⟨oneHighFamilyV2PartnerVertex x,
          oneHighFamilyV2PartnerVertex_lt hx hm⟩ : Fin 40)) = true := by
    simpa [Fin.divNat, Fin.modNat] using
      oneHighFamilyV2PartnerVertex_canonicalAdj a hx hm
  exact of_decide_eq_true (hrel.trans hcanon)

theorem oneHighFamilyCanonicalAdj_worker_partner
    (a : Nat) {x y : Nat} (hx : x < 40) (_hy : y < 40)
    (hdiv : y / 5 = x / 5)
    (hadj : oneHighCanonicalBranchAdj
      (oneHighFamilyTwoEdges a (⟨x / 5, by omega⟩ : Fin 8))
      (⟨x % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5)
      (⟨y % 5, Nat.mod_lt _ (by omega)⟩ : Fin 5) = true) :
    oneHighFamilyVertexMatched a x = true ∧
      y = oneHighFamilyV2PartnerVertex x := by
  unfold oneHighCanonicalBranchAdj oneHighFamilyTwoEdges at hadj
  unfold oneHighFamilyVertexMatched oneHighFamilyV2PartnerVertex
  simp only [decide_eq_true_eq] at hadj
  split <;> simp_all [Fin.ext_iff] <;> omega

theorem oneHighFamily_adj_sameBlock_eq_partner
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (x y : Fin 40)
    (hdiv : Fin.divNat (m := 8) (n := 5) y =
      Fin.divNat (m := 8) (n := 5) x)
    (hadj : R.Adj x y) :
    oneHighFamilyVertexMatched a x.val = true ∧
      y.val = oneHighFamilyV2PartnerVertex x.val := by
  have hrel := hc.relation.1 x y hdiv.symm
  have hdecide : decide (R.Adj x y) = true := decide_eq_true hadj
  rw [hdecide] at hrel
  apply oneHighFamilyCanonicalAdj_worker_partner a x.isLt y.isLt
  · exact congrArg Fin.val hdiv
  · simpa [Fin.divNat, Fin.modNat] using hrel.symm

/-- The five encoded vertices belonging to a branch. -/
def oneHighFamilyBlockFinset (b : Fin 8) : Finset (Fin 40) :=
  Finset.univ.filter fun x =>
    Fin.divNat (m := 8) (n := 5) x = b

theorem oneHighFamilyBlockFinset_card (b : Fin 8) :
    (oneHighFamilyBlockFinset b).card = 5 := by
  native_decide +revert

theorem oneHighFamilyBlockFinset_cross_degree_le_one
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (c j : Fin 8) (x : Fin 40) (_hx : x ∈ oneHighFamilyBlockFinset c) :
    (R.neighborFinset x ∩ oneHighFamilyBlockFinset j).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro y hy z hz
  have hy' := Finset.mem_inter.mp hy
  have hz' := Finset.mem_inter.mp hz
  have hyBlock := (Finset.mem_filter.mp hy'.2).2
  have hzBlock := (Finset.mem_filter.mp hz'.2).2
  by_contra hyz
  exact hc.relation.2.2.2.2.1 x y z hyz (hyBlock.trans hzBlock.symm)
    ⟨(R.mem_neighborFinset x y).mp hy'.1,
      (R.mem_neighborFinset x z).mp hz'.1⟩

/-- The full five-vertex directed miss deficit is symmetric.  This is the
encoded equal-shore bipartite incidence argument underlying F1. -/
theorem oneHighFamilyFullMissDeficit_symm
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R) (c j : Fin 8) :
    ((oneHighFamilyBlockFinset c).filter fun x =>
      (R.neighborFinset x ∩ oneHighFamilyBlockFinset j).card = 0).card =
    ((oneHighFamilyBlockFinset j).filter fun x =>
      (R.neighborFinset x ∩ oneHighFamilyBlockFinset c).card = 0).card := by
  apply card_filter_no_cross_neighbor_eq R
  · rw [oneHighFamilyBlockFinset_card, oneHighFamilyBlockFinset_card]
  · exact oneHighFamilyBlockFinset_cross_degree_le_one a R hc c j
  · exact oneHighFamilyBlockFinset_cross_degree_le_one a R hc j c

theorem oneHighFamilyFarDegree_eq_six_of_worker_unmatched
    (a : Nat) (c : Fin 8) (r : Fin 5)
    (h : oneHighFamilyVertexMatched a (oneHighFamilyVertex c r).val = false) :
    oneHighFamilyFarDegree a c r = 6 := by
  simp only [oneHighFamilyVertexMatched, oneHighFamilyVertex_val] at h
  simp only [oneHighFamilyFarDegree, oneHighFamilyInternalEdges]
  split <;> simp_all <;> omega

/-- A worker-unmatched vertex has one far neighbor in every one of the six
available non-self, non-mate blocks. -/
theorem oneHighFamilyUnmatched_not_misses_farBlock
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (c j : Fin 8) (r : Fin 5)
    (hmatch : oneHighFamilyVertexMatched a
      (oneHighFamilyVertex c r).val = false)
    (hjc : j ≠ c) (hjm : j ≠ oneHighStandardMate c) :
    ¬ oneHighFamilyMissesBlock R (oneHighFamilyVertex c r) j := by
  intro hmiss
  let x := oneHighFamilyVertex c r
  let N := oneHighEncodedFarNeighbors R x
  let blocks := N.image fun y => Fin.divNat (m := 8) (n := 5) y
  have hxdiv : Fin.divNat (m := 8) (n := 5) x = c := by
    exact oneHighFamilyVertex_divNat c r
  have hxmod : Fin.modNat (m := 8) (n := 5) x = r := by
    exact oneHighFamilyVertex_modNat c r
  have hNcard : N.card = 6 := by
    rw [hc.relation.2.2.2.2.2.1 x]
    rw [hxdiv, hxmod]
    exact oneHighFamilyFarDegree_eq_six_of_worker_unmatched a c r hmatch
  have hinj : Set.InjOn (fun y : Fin 40 =>
      Fin.divNat (m := 8) (n := 5) y) N := by
    intro y hy z hz hyz
    by_contra hne
    have hyAdj := (Finset.mem_filter.mp hy).2.1
    have hzAdj := (Finset.mem_filter.mp hz).2.1
    exact hc.relation.2.2.2.2.1 x y z hne hyz ⟨hyAdj, hzAdj⟩
  have hblocksCard : blocks.card = 6 := by
    rw [show blocks.card = N.card by
      simpa [blocks] using Finset.card_image_iff.mpr hinj]
    exact hNcard
  have hsubset : blocks ⊆
      ((Finset.univ.erase c).erase (oneHighStandardMate c)).erase j := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨y, hy, rfl⟩
    have hyParts := (Finset.mem_filter.mp hy).2
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      have hyBlock : y ∈ oneHighFamilyBlockFinset j := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
      have hyVertex : oneHighFamilyVertex j
          (Fin.modNat (m := 8) (n := 5) y) = y := by
        unfold oneHighFamilyVertex
        rw [← heq]
        exact finProdFinEquiv.apply_symm_apply y
      exact hmiss (Fin.modNat (m := 8) (n := 5) y) (by
        rw [hyVertex]
        exact hyParts.1)
    · apply Finset.mem_erase.mpr
      exact ⟨by simpa [hxdiv] using hyParts.2.2,
        Finset.mem_erase.mpr
          ⟨by simpa [hxdiv] using hyParts.2.1, Finset.mem_univ _⟩⟩
  have hle := Finset.card_le_card hsubset
  have htarget :
      ((((Finset.univ : Finset (Fin 8)).erase c).erase
        (oneHighStandardMate c)).erase j).card = 5 := by
    simp [hjc, hjm, oneHighStandardMate_ne]
  rw [hblocksCard, htarget] at hle
  omega

theorem oneHighFamilyTableMissAtoms_eq_filter_map (a c j : Nat) :
    oneHighFamilyTableMissAtoms a c j =
      ((oneHighFamilyBlockVertices c).filter fun w =>
        oneHighFamilyVertexMatched a w).map fun w => .miss w j := by
  unfold oneHighFamilyTableMissAtoms
  induction oneHighFamilyBlockVertices c with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.filterMap_cons, List.filter_cons]
      cases oneHighFamilyVertexMatched a w <;> simp [ih]

theorem oneHighFamilyFilteredBlockVertices_nodup (a c : Nat) :
    ((oneHighFamilyBlockVertices c).filter fun w =>
      oneHighFamilyVertexMatched a w).Nodup :=
  (oneHighFamilyBlockVertices_nodup c).filter _

noncomputable def oneHighFamilyWorkerMissFinset
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (c j : Fin 8) : Finset Nat :=
  (((oneHighFamilyBlockVertices c.val).filter fun w =>
    oneHighFamilyVertexMatched a w).toFinset).filter fun w =>
      oneHighFamilyAtomValue R (.miss w j.val) = true

theorem oneHighFamilyGraphTable_eq_workerMissFinset_card
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (c j : Fin 8) :
    oneHighFamilyGraphTable R a c.val j.val =
      (oneHighFamilyWorkerMissFinset a R c j).card := by
  classical
  rw [oneHighFamilyGraphTable, oneHighFamilyTableMissAtoms_eq_filter_map]
  rw [List.map_map]
  rw [List.count_map_true_eq_filter_toFinset_card _
    (oneHighFamilyFilteredBlockVertices_nodup a c.val)]
  rfl

theorem oneHighFamilyWorkerMissFinset_mem_lt
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (c j : Fin 8) {w : Nat}
    (hw : w ∈ oneHighFamilyWorkerMissFinset a R c j) : w < 40 := by
  have hwOuter := (Finset.mem_filter.mp hw).1
  have hwList : w ∈ (oneHighFamilyBlockVertices c.val).filter fun w =>
      oneHighFamilyVertexMatched a w := by simpa using hwOuter
  exact (oneHighFamilyBlockVertices_mem c.isLt
    (List.mem_filter.mp hwList).1).1

theorem oneHighFamilyMissesBlock_iff_blockFinset_card_zero
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Fin 40) (j : Fin 8) :
    oneHighFamilyMissesBlock R x j ↔
      (R.neighborFinset x ∩ oneHighFamilyBlockFinset j).card = 0 := by
  rw [Finset.card_eq_zero]
  constructor
  · intro h
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    have hzParts := Finset.mem_inter.mp hz
    have hzDiv := (Finset.mem_filter.mp hzParts.2).2
    have hzVertex : oneHighFamilyVertex j
        (Fin.modNat (m := 8) (n := 5) z) = z := by
      unfold oneHighFamilyVertex
      rw [← hzDiv]
      exact (finProdFinEquiv : Fin 8 × Fin 5 ≃ Fin 40).apply_symm_apply z
    exact h (Fin.modNat (m := 8) (n := 5) z) (by
      rw [hzVertex]
      exact (R.mem_neighborFinset x z).mp hzParts.1)
  · intro h r hadj
    have hz : oneHighFamilyVertex j r ∈
        R.neighborFinset x ∩ oneHighFamilyBlockFinset j := by
      exact Finset.mem_inter.mpr ⟨(R.mem_neighborFinset _ _).mpr hadj,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          oneHighFamilyVertex_divNat j r⟩⟩
    rw [h] at hz
    simp at hz

theorem oneHighFamilyWorkerMissFinset_card_eq_fullMissDeficit
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R)
    (c j : Fin 8) (hjc : j ≠ c)
    (hjm : j ≠ oneHighStandardMate c) :
    (oneHighFamilyWorkerMissFinset a R c j).card =
      ((oneHighFamilyBlockFinset c).filter fun x =>
        (R.neighborFinset x ∩ oneHighFamilyBlockFinset j).card = 0).card := by
  classical
  apply Finset.card_bij (fun w hw =>
    (⟨w, oneHighFamilyWorkerMissFinset_mem_lt a R c j hw⟩ : Fin 40))
  · intro w hw
    have hwParts := Finset.mem_filter.mp hw
    have hwMemList : w ∈ (oneHighFamilyBlockVertices c.val).filter fun w =>
        oneHighFamilyVertexMatched a w := by simpa using hwParts.1
    have hwList := List.mem_filter.mp hwMemList
    have hwBound := oneHighFamilyBlockVertices_mem c.isLt hwList.1
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        apply Fin.ext
        simpa [Fin.divNat] using hwBound.2⟩
    · rw [← oneHighFamilyMissesBlock_iff_blockFinset_card_zero]
      simpa [oneHighFamilyAtomValue, hwBound.1, j.isLt] using hwParts.2
  · intro w hw z hz heq
    exact congrArg Fin.val heq
  · intro x hx
    have hxParts := Finset.mem_filter.mp hx
    have hxDiv := (Finset.mem_filter.mp hxParts.1).2
    have hmiss : oneHighFamilyMissesBlock R x j :=
      (oneHighFamilyMissesBlock_iff_blockFinset_card_zero R x j).2 hxParts.2
    have hxWorker : oneHighFamilyVertexMatched a x.val = true := by
      cases hwm : oneHighFamilyVertexMatched a x.val with
      | true => rfl
      | false =>
          have hxVertex : oneHighFamilyVertex c
              (Fin.modNat (m := 8) (n := 5) x) = x := by
            unfold oneHighFamilyVertex
            rw [← hxDiv]
            exact (finProdFinEquiv : Fin 8 × Fin 5 ≃ Fin 40).apply_symm_apply x
          exact False.elim (oneHighFamilyUnmatched_not_misses_farBlock
            a R hc c j (Fin.modNat (m := 8) (n := 5) x)
            (by simpa [hxVertex] using hwm) hjc hjm (by
              simpa [hxVertex] using hmiss))
    refine ⟨x.val, ?_, Fin.ext rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · show x.val ∈ ((oneHighFamilyBlockVertices c.val).filter fun w =>
        oneHighFamilyVertexMatched a w).toFinset
      simpa using (List.mem_filter.mpr ⟨
        (oneHighFamilyBlockVertices_mem_iff c.isLt).mpr
          ⟨x.isLt, by simpa [Fin.divNat] using congrArg Fin.val hxDiv⟩,
        hxWorker⟩)
    · simp [oneHighFamilyAtomValue, x.isLt, j.isLt, hmiss]

theorem oneHighFamilyV2F1Ledger_of_constraints
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R) :
    OneHighFamilyV2F1Ledger a R := by
  constructor
  intro c j hjc hjm
  have hcj : c ≠ j := Ne.symm hjc
  have hcm : c ≠ oneHighStandardMate j := by
    intro h
    apply hjm
    rw [h, oneHighStandardMate_involutive j]
  rw [oneHighFamilyGraphTable_eq_workerMissFinset_card,
    oneHighFamilyGraphTable_eq_workerMissFinset_card]
  rw [oneHighFamilyWorkerMissFinset_card_eq_fullMissDeficit
      a R hc c j hjc hjm,
    oneHighFamilyWorkerMissFinset_card_eq_fullMissDeficit
      a R hc j c hcj hcm]
  exact oneHighFamilyFullMissDeficit_symm a R hc c j

noncomputable def oneHighFamilyF2SaverFinset
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Fin 40) : Finset (Fin 40) := by
  classical
  exact (oneHighEncodedFarNeighbors R x).filter fun w =>
    oneHighFamilyVertexMatched a w.val = true ∧
      oneHighFamilyMissesBlock R w
        (oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x))

theorem oneHighFamilyV2SaverVertices_nodup (a x : Nat) :
    (oneHighFamilyV2SaverVertices a x).Nodup := by
  exact List.nodup_range.filter _

theorem oneHighFamilyV2SaverVertices_mem_lt
    (a x : Nat) {w : Nat} (hw : w ∈ oneHighFamilyV2SaverVertices a x) :
    w < 40 := by
  exact List.mem_range.mp (List.mem_filter.mp hw).1

theorem oneHighFamily_xor_one_lt_eight {n : Nat} (h : n < 8) :
    n ^^^ 1 < 8 := by
  native_decide +revert

/-- The worker's true saver atoms are exactly matched far neighbors which
miss the mate block.  This is the saver half of the F2 partition. -/
theorem oneHighFamilyV2SaverAtoms_count_eq_saverFinset_card
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Fin 40) :
    ((oneHighFamilyV2SaverAtoms a x.val).map
      (oneHighFamilyAtomValue R)).count true =
      (oneHighFamilyF2SaverFinset a R x).card := by
  classical
  rw [oneHighFamilyV2SaverAtoms, List.map_map]
  rw [List.count_map_true_eq_filter_toFinset_card _
    (oneHighFamilyV2SaverVertices_nodup a x.val)]
  apply Finset.card_bij (fun w hw =>
    (⟨w, oneHighFamilyV2SaverVertices_mem_lt a x.val
      (by simpa using (Finset.mem_filter.mp hw).1)⟩ : Fin 40))
  · intro w hw
    have hwParts := Finset.mem_filter.mp hw
    have hwSaver : w ∈ oneHighFamilyV2SaverVertices a x.val := by
      simpa using hwParts.1
    have hw40 := oneHighFamilyV2SaverVertices_mem_lt a x.val hwSaver
    have hwCond : oneHighFamilyVertexMatched a w = true ∧
        w / 5 ≠ x.val / 5 ∧ w / 5 ≠ (x.val / 5 ^^^ 1) := by
      have h := (by simpa [oneHighFamilyV2SaverVertices] using hwSaver :
        w < 40 ∧ oneHighFamilyVertexMatched a w = true ∧
          w / 5 ≠ x.val / 5 ∧ w / 5 ≠ (x.val / 5 ^^^ 1))
      exact h.2
    have hwValue := hwParts.2
    have hxBlockLt : x.val / 5 < 8 := by omega
    have hmateLt : (x.val / 5 ^^^ 1) < 8 :=
      oneHighFamily_xor_one_lt_eight hxBlockLt
    have hmateEq : (⟨x.val / 5 ^^^ 1, hmateLt⟩ : Fin 8) =
        oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x) := by
      apply Fin.ext
      rw [oneHighStandardMate_val_eq_xor]
      rfl
    have hwSem : R.Adj x ⟨w, hw40⟩ ∧
        oneHighFamilyMissesBlock R ⟨w, hw40⟩
          ⟨x.val / 5 ^^^ 1, hmateLt⟩ := by
      simpa [oneHighFamilyAtomValue, x.isLt, hw40, hmateLt,
        Bool.and_eq_true] using hwValue
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hwSem.1, ?_, ?_⟩
      · simpa [Fin.divNat] using hwCond.2.1
      · intro h
        apply hwCond.2.2
        have hv := congrArg Fin.val h
        rw [oneHighStandardMate_val_eq_xor] at hv
        exact hv
    · refine ⟨hwCond.1, ?_⟩
      simpa [hmateEq] using hwSem.2
  · intro w hw z hz heq
    exact congrArg Fin.val heq
  · intro w hw
    rw [oneHighFamilyF2SaverFinset] at hw
    have hwParts := Finset.mem_filter.mp hw
    have hwFar := Finset.mem_filter.mp hwParts.1
    have hwDivSelf : w.val / 5 ≠ x.val / 5 := by
      simpa [Fin.divNat] using hwFar.2.2.1
    have hwDivMate : w.val / 5 ≠ (x.val / 5 ^^^ 1) := by
      intro h
      apply hwFar.2.2.2
      apply Fin.ext
      rw [oneHighStandardMate_val_eq_xor]
      simpa [Fin.divNat] using h
    refine ⟨w.val, ?_, Fin.ext rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · show w.val ∈ (oneHighFamilyV2SaverVertices a x.val).toFinset
      simp [oneHighFamilyV2SaverVertices, w.isLt, hwParts.2.1,
        hwDivSelf, hwDivMate]
    · have hxBlockLt : x.val / 5 < 8 := by omega
      have hmateLt : (x.val / 5 ^^^ 1) < 8 :=
        oneHighFamily_xor_one_lt_eight hxBlockLt
      have hmateEq : (⟨x.val / 5 ^^^ 1, hmateLt⟩ : Fin 8) =
          oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x) := by
        apply Fin.ext
        rw [oneHighStandardMate_val_eq_xor]
        rfl
      simp [oneHighFamilyAtomValue, x.isLt, w.isLt, hmateLt,
        hwFar.2.1, hmateEq, hwParts.2.2]

noncomputable def oneHighFamilyF2CommonFinset
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Fin 40) : Finset (Fin 40) := by
  classical
  exact (oneHighFamilyBlockFinset
    (oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x))).filter fun z =>
      (R.neighborFinset x ∩ R.neighborFinset z).card = 1

noncomputable def oneHighFamilyF2ContinuingFinset
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Fin 40) : Finset (Fin 40) := by
  classical
  exact (oneHighEncodedFarNeighbors R x).filter fun w =>
    ¬ oneHighFamilyMissesBlock R w
      (oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x))

theorem oneHighFamily_common_min_max_card
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Fin 40) :
    (R.neighborFinset (⟨min x.val z.val, by omega⟩ : Fin 40) ∩
      R.neighborFinset (⟨max x.val z.val, by omega⟩ : Fin 40)).card =
      (R.neighborFinset x ∩ R.neighborFinset z).card := by
  by_cases h : x.val ≤ z.val
  · have hmin : (⟨min x.val z.val, by omega⟩ : Fin 40) = x := by
      apply Fin.ext
      simp [Nat.min_eq_left h]
    have hmax : (⟨max x.val z.val, by omega⟩ : Fin 40) = z := by
      apply Fin.ext
      simp [Nat.max_eq_right h]
    rw [hmin, hmax]
  · have hle : z.val ≤ x.val := by omega
    have hmin : (⟨min x.val z.val, by omega⟩ : Fin 40) = z := by
      apply Fin.ext
      simp [Nat.min_eq_right hle]
    have hmax : (⟨max x.val z.val, by omega⟩ : Fin 40) = x := by
      apply Fin.ext
      simp [Nat.max_eq_left hle]
    rw [hmin, hmax, Finset.inter_comm]

theorem oneHighFamilyV2PairedCommonAtoms_count_eq_commonFinset_card
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Fin 40) :
    ((oneHighFamilyV2PairedCommonAtoms x.val).map
      (oneHighFamilyAtomValue R)).count true =
      (oneHighFamilyF2CommonFinset R x).card := by
  classical
  rw [oneHighFamilyV2PairedCommonAtoms, List.map_map]
  rw [List.count_map_true_eq_filter_toFinset_card _
    (oneHighFamilyBlockVertices_nodup _)]
  apply Finset.card_bij (fun z hz =>
    (⟨z, (oneHighFamilyBlockVertices_mem
      (oneHighFamily_xor_one_lt_eight (by omega : x.val / 5 < 8))
      (by
        have h : z ∈ oneHighFamilyBlockVertices (x.val / 5 ^^^ 1) := by
          simpa using (Finset.mem_filter.mp hz).1
        exact h)).1⟩ : Fin 40))
  · intro z ha
    have hz : z ∈ oneHighFamilyBlockVertices (x.val / 5 ^^^ 1) := by
      simpa using (Finset.mem_filter.mp ha).1
    have hzBlock := oneHighFamilyBlockVertices_mem
      (oneHighFamily_xor_one_lt_eight (by omega : x.val / 5 < 8)) hz
    have hz40 := hzBlock.1
    have hzDiv := hzBlock.2
    have hvalue := (Finset.mem_filter.mp ha).2
    rw [oneHighFamilyF2CommonFinset]
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Fin.ext
      rw [oneHighStandardMate_val_eq_xor]
      simpa [Fin.divNat] using hzDiv
    · simpa [oneHighFamilyAtomValue, x.isLt, hz40,
        oneHighFamily_common_min_max_card R x ⟨z, hz40⟩] using hvalue
  · intro z ha z' ha' heq
    exact congrArg Fin.val heq
  · intro z hz
    rw [oneHighFamilyF2CommonFinset] at hz
    have hzParts := Finset.mem_filter.mp hz
    have hzDiv := (Finset.mem_filter.mp hzParts.1).2
    refine ⟨z.val, ?_, Fin.ext rfl⟩
    · apply Finset.mem_filter.mpr
      constructor
      · show z.val ∈ (oneHighFamilyBlockVertices (x.val / 5 ^^^ 1)).toFinset
        apply List.mem_toFinset.mpr
        apply (oneHighFamilyBlockVertices_mem_iff
          (oneHighFamily_xor_one_lt_eight (by omega : x.val / 5 < 8))).mpr
        constructor
        · exact z.isLt
        · have hv := congrArg Fin.val hzDiv
          rw [oneHighStandardMate_val_eq_xor] at hv
          exact hv
      · simp [oneHighFamilyAtomValue, x.isLt, z.isLt,
          oneHighFamily_common_min_max_card R x z, hzParts.2]

noncomputable def oneHighFamilyCommonWitness
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Fin 40)
    (h : (R.neighborFinset x ∩ R.neighborFinset z).card = 1) : Fin 40 :=
  Classical.choose (Finset.card_pos.mp (by omega :
    0 < (R.neighborFinset x ∩ R.neighborFinset z).card))

theorem oneHighFamilyCommonWitness_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Fin 40)
    (h : (R.neighborFinset x ∩ R.neighborFinset z).card = 1) :
    oneHighFamilyCommonWitness R x z h ∈
      R.neighborFinset x ∩ R.neighborFinset z := by
  exact Classical.choose_spec (Finset.card_pos.mp (by omega :
    0 < (R.neighborFinset x ∩ R.neighborFinset z).card))

theorem oneHighFamilyF2CommonFinset_mem_card
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x z : Fin 40) (hz : z ∈ oneHighFamilyF2CommonFinset R x) :
    (R.neighborFinset x ∩ R.neighborFinset z).card = 1 := by
  rw [oneHighFamilyF2CommonFinset] at hz
  exact (Finset.mem_filter.mp hz).2

theorem oneHighFamilyF2CommonFinset_card_eq_continuingFinset_card
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R) (x : Fin 40) :
    (oneHighFamilyF2CommonFinset R x).card =
      (oneHighFamilyF2ContinuingFinset R x).card := by
  classical
  apply Finset.card_bij (fun z hz => oneHighFamilyCommonWitness R x z
    (oneHighFamilyF2CommonFinset_mem_card R x z hz))
  · intro z hz
    have hzDef := hz
    rw [oneHighFamilyF2CommonFinset] at hzDef
    have hzParts := Finset.mem_filter.mp hzDef
    have hzBlock := (Finset.mem_filter.mp hzParts.1).2
    let hcard := oneHighFamilyF2CommonFinset_mem_card R x z hz
    let w := oneHighFamilyCommonWitness R x z hcard
    have hwMem := oneHighFamilyCommonWitness_mem R x z hcard
    have hwAdjX : R.Adj x w :=
      (R.mem_neighborFinset x w).mp (Finset.mem_inter.mp hwMem).1
    have hwAdjZ : R.Adj z w :=
      (R.mem_neighborFinset z w).mp (Finset.mem_inter.mp hwMem).2
    have hwBlockSelf : Fin.divNat (m := 8) (n := 5) w ≠
        Fin.divNat (m := 8) (n := 5) x := by
      intro heq
      have hm := hc.relation.2.1 w z
      apply hm
      · rw [hzBlock, heq]
      · exact hwAdjZ.symm
    have hwBlockMate : Fin.divNat (m := 8) (n := 5) w ≠
        oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x) := by
      intro heq
      exact hc.relation.2.1 x w heq hwAdjX
    rw [oneHighFamilyF2ContinuingFinset]
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwAdjX,
        hwBlockSelf, hwBlockMate⟩
    · intro hmiss
      have hzVertex : oneHighFamilyVertex
          (oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x))
          (Fin.modNat (m := 8) (n := 5) z) = z := by
        unfold oneHighFamilyVertex
        rw [← hzBlock]
        exact (finProdFinEquiv : Fin 8 × Fin 5 ≃ Fin 40).apply_symm_apply z
      exact hmiss (Fin.modNat (m := 8) (n := 5) z) (by
        rw [hzVertex]
        exact hwAdjZ.symm)
  · intro z hz z' hz' heq
    have hzDef := hz
    have hz'Def := hz'
    rw [oneHighFamilyF2CommonFinset] at hzDef hz'Def
    have hzBlock := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hzDef).1).2
    have hz'Block := (Finset.mem_filter.mp
      (Finset.mem_filter.mp hz'Def).1).2
    by_contra hzz'
    let hcard := oneHighFamilyF2CommonFinset_mem_card R x z hz
    let hcard' := oneHighFamilyF2CommonFinset_mem_card R x z' hz'
    let w := oneHighFamilyCommonWitness R x z hcard
    have hwz := (Finset.mem_inter.mp
      (oneHighFamilyCommonWitness_mem R x z hcard)).2
    have hwz' := (Finset.mem_inter.mp
      (oneHighFamilyCommonWitness_mem R x z' hcard')).2
    have hwzAdj : R.Adj w z :=
      (R.mem_neighborFinset z w).mp hwz |>.symm
    have hwz'Adj : R.Adj w z' := by
      have heqW : oneHighFamilyCommonWitness R x z' hcard' = w := by
        exact heq.symm
      have hadj : R.Adj (oneHighFamilyCommonWitness R x z' hcard') z' :=
        ((R.mem_neighborFinset z' _).mp hwz').symm
      simpa [heqW] using hadj
    exact hc.relation.2.2.2.2.1 w z z' hzz'
      (hzBlock.trans hz'Block.symm) ⟨hwzAdj, hwz'Adj⟩
  · intro w hw
    rw [oneHighFamilyF2ContinuingFinset] at hw
    have hwParts := Finset.mem_filter.mp hw
    have hwFar := Finset.mem_filter.mp hwParts.1
    have hex := Classical.not_forall.mp hwParts.2
    obtain ⟨r, hr⟩ := hex
    have hwr : R.Adj w (oneHighFamilyVertex
        (oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x)) r) :=
      Classical.not_not.mp hr
    let b := oneHighStandardMate
      (Fin.divNat (m := 8) (n := 5) x)
    let z := oneHighFamilyVertex b r
    have hxz : x ≠ z := by
      intro h
      have hd := congrArg (Fin.divNat (m := 8) (n := 5)) h
      simp only [z, b, oneHighFamilyVertex_divNat] at hd
      exact (oneHighStandardMate_ne
        (Fin.divNat (m := 8) (n := 5) x)) hd.symm
    have hwCommon : w ∈ R.neighborFinset x ∩ R.neighborFinset z := by
      exact Finset.mem_inter.mpr ⟨
        (R.mem_neighborFinset x w).mpr hwFar.2.1,
        (R.mem_neighborFinset z w).mpr hwr.symm⟩
    have hcardLe : (R.neighborFinset x ∩ R.neighborFinset z).card ≤ 1 :=
      hc.relation.2.2.1 x z hxz
    have hcard : (R.neighborFinset x ∩ R.neighborFinset z).card = 1 := by
      have hpos := Finset.card_pos.mpr ⟨w, hwCommon⟩
      omega
    have hzCommon : z ∈ oneHighFamilyF2CommonFinset R x := by
      rw [oneHighFamilyF2CommonFinset]
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simp [z, b]⟩, hcard⟩
    refine ⟨z, hzCommon, ?_⟩
    apply Finset.card_le_one.mp hcardLe
    · exact oneHighFamilyCommonWitness_mem R x z hcard
    · exact hwCommon

theorem oneHighFamilyF2Continuing_union_saver
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R) (x : Fin 40) :
    oneHighFamilyF2ContinuingFinset R x ∪
        oneHighFamilyF2SaverFinset a R x =
      oneHighEncodedFarNeighbors R x := by
  classical
  ext w
  simp only [Finset.mem_union]
  rw [oneHighFamilyF2ContinuingFinset, oneHighFamilyF2SaverFinset]
  simp only [Finset.mem_filter]
  constructor
  · rintro (⟨hw, _⟩ | ⟨hw, _⟩) <;> exact hw
  · intro hw
    by_cases hm : oneHighFamilyMissesBlock R w
        (oneHighStandardMate (Fin.divNat (m := 8) (n := 5) x))
    · right
      refine ⟨hw, ?_, hm⟩
      cases hmatched : oneHighFamilyVertexMatched a w.val with
      | true => rfl
      | false =>
          have hwFar := Finset.mem_filter.mp hw
          let c := Fin.divNat (m := 8) (n := 5) w
          let j := oneHighStandardMate
            (Fin.divNat (m := 8) (n := 5) x)
          have hjc : j ≠ c := by
            intro h
            exact hwFar.2.2.2 h.symm
          have hjm : j ≠ oneHighStandardMate c := by
            intro h
            have heq : Fin.divNat (m := 8) (n := 5) x = c := by
              apply oneHighStandardMate.injective
              exact h
            exact hwFar.2.2.1 heq.symm
          have hwVertex : oneHighFamilyVertex c
              (Fin.modNat (m := 8) (n := 5) w) = w := by
            unfold oneHighFamilyVertex c
            exact (finProdFinEquiv : Fin 8 × Fin 5 ≃ Fin 40).apply_symm_apply w
          exact False.elim (oneHighFamilyUnmatched_not_misses_farBlock
            a R hc c j (Fin.modNat (m := 8) (n := 5) w)
            (by simpa [hwVertex] using hmatched) hjc hjm (by
              simpa [hwVertex, j] using hm))
    · left
      exact ⟨hw, hm⟩

theorem oneHighFamilyF2Continuing_disjoint_saver
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (x : Fin 40) :
    Disjoint (oneHighFamilyF2ContinuingFinset R x)
      (oneHighFamilyF2SaverFinset a R x) := by
  classical
  rw [Finset.disjoint_left]
  intro w hwc hws
  rw [oneHighFamilyF2ContinuingFinset] at hwc
  rw [oneHighFamilyF2SaverFinset] at hws
  exact (Finset.mem_filter.mp hwc).2 (Finset.mem_filter.mp hws).2.2

theorem oneHighFamilyV2F2Ledger_of_constraints
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R) :
    OneHighFamilyV2F2Ledger R a := by
  constructor
  intro x hx
  let xf : Fin 40 := ⟨x, hx⟩
  rw [List.map_append, List.count_append]
  rw [oneHighFamilyV2PairedCommonAtoms_count_eq_commonFinset_card R xf]
  rw [oneHighFamilyV2SaverAtoms_count_eq_saverFinset_card a R xf]
  rw [oneHighFamilyF2CommonFinset_card_eq_continuingFinset_card a R hc xf]
  calc
    (oneHighFamilyF2ContinuingFinset R xf).card +
        (oneHighFamilyF2SaverFinset a R xf).card =
        (oneHighEncodedFarNeighbors R xf).card := by
      rw [← Finset.card_union_of_disjoint
        (oneHighFamilyF2Continuing_disjoint_saver a R xf)]
      rw [oneHighFamilyF2Continuing_union_saver a R hc xf]
    _ = oneHighFamilyFarDegreeBound a x := by
      rw [hc.relation.2.2.2.2.2.1 xf]
      exact (oneHighFamilyFarDegreeBound_eq a x hx).symm

theorem oneHighFamilyFoldl_append_pairs
    (x : Nat) (zs : List Nat) (init : List (Nat × Nat)) :
    zs.foldl (fun pairs z => pairs ++ [(x, z)]) init =
      init ++ zs.map (fun z => (x, z)) := by
  induction zs generalizing init with
  | nil => simp
  | cons z zs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih]
      simp [List.append_assoc]

theorem oneHighFamilyFoldl_append_pair_blocks
    (xs zs : List Nat) (init : List (Nat × Nat)) :
    xs.foldl (fun pairs x =>
      zs.foldl (fun pairs z => pairs ++ [(x, z)]) pairs) init =
      init ++ xs.flatMap (fun x => zs.map fun z => (x, z)) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [oneHighFamilyFoldl_append_pairs, ih]
      simp [List.append_assoc]

theorem oneHighFamilyCommonPairs_eq_flatMap (bi bj : Nat) :
    oneHighFamilyCommonPairs bi bj =
      (oneHighFamilyBlockVertices bi).flatMap fun x =>
        (oneHighFamilyBlockVertices bj).map fun z => (x, z) := by
  unfold oneHighFamilyCommonPairs
  simpa using oneHighFamilyFoldl_append_pair_blocks
    (oneHighFamilyBlockVertices bi) (oneHighFamilyBlockVertices bj) []

theorem oneHighFamilyV2F3aAtoms_eq_commonPairs (pair : Nat) :
    oneHighFamilyV2F3aAtoms pair =
      (oneHighFamilyCommonPairs (2 * pair) (2 * pair + 1)).map fun p =>
        .common (min p.1 p.2) (max p.1 p.2) := by
  have hm := congrArg (List.map fun p : Nat × Nat =>
    OneHighFamilyAtom.common (min p.1 p.2) (max p.1 p.2))
    (oneHighFamilyCommonPairs_eq_flatMap (2 * pair) (2 * pair + 1))
  simp only [List.map_flatMap, List.map_map] at hm
  exact hm.symm

theorem oneHighFamilyV2F3aValues_eq_commonPairs
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj] (pair : Nat) :
    (oneHighFamilyV2F3aAtoms pair).map (oneHighFamilyAtomValue R) =
      (oneHighFamilyCommonPairs (2 * pair) (2 * pair + 1)).map fun p =>
        oneHighFamilyAtomValue R
          (.common (min p.1 p.2) (max p.1 p.2)) := by
  rw [oneHighFamilyV2F3aAtoms_eq_commonPairs]
  induction oneHighFamilyCommonPairs (2 * pair) (2 * pair + 1) with
  | nil => rfl
  | cons p ps ih =>
      simp only [List.map_cons]
      rw [ih]

theorem oneHighFamilyV2F3aLedger_of_constraints
    (a : Nat) (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    (hc : OneHighPureFamilyCnfConstraints a R) :
    OneHighFamilyV2F3aLedger R a := by
  constructor
  intro pair hpair
  let pairs := oneHighFamilyCommonPairs (2 * pair) (2 * pair + 1)
  calc
    ((oneHighFamilyV2F3aAtoms pair).map
        (oneHighFamilyAtomValue R)).count true =
        (pairs.map (fun p => oneHighFamilyAtomValue R
          (.common (min p.1 p.2) (max p.1 p.2)))).count true := by
      rw [oneHighFamilyV2F3aValues_eq_commonPairs]
    _ = (pairs.toFinset.filter fun p => oneHighFamilyAtomValue R
          (.common (min p.1 p.2) (max p.1 p.2)) = true).card :=
      List.count_map_true_eq_filter_toFinset_card pairs
        (oneHighFamilyCommonPairs_nodup _ _) _
    _ = (oneHighFamilyCAtoms R
          (⟨2 * pair, by omega⟩ : Fin 8)).card :=
      oneHighFamilyCommonPairs_filter_card R pair hpair
    _ = 30 - 2 * oneHighFamilyInternalEdges a
          (⟨2 * pair, by omega⟩ : Fin 8) -
          2 * oneHighFamilyInternalEdges a
            (oneHighStandardMate (⟨2 * pair, by omega⟩ : Fin 8)) :=
      oneHighFamily_cAtoms_card_eq_generatorBound hc.relation _
    _ = 30 - 2 * oneHighFamilyInternalEdgesNat a (2 * pair) -
          2 * oneHighFamilyInternalEdgesNat a (2 * pair + 1) := by
      rw [oneHighStandardMate_even_pair pair hpair]
      rfl

end Erdos85

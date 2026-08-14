import Proofs.Erdos85OneHighV2Satisfaction

/-!
# Graph-side ledgers for the exact fleet-v2 replay

This file discharges the combinatorial payloads kept deliberately separate
from the byte-exact generator and its valuation/state mechanics.
-/

namespace Erdos85

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

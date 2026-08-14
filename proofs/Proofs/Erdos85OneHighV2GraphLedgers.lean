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

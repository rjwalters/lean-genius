import Proofs.Erdos85OneHighV2Satisfaction

/-!
# Graph-side ledgers for the exact fleet-v2 replay

This file discharges the combinatorial payloads kept deliberately separate
from the byte-exact generator and its valuation/state mechanics.
-/

namespace Erdos85

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

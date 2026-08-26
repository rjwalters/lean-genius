import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyOrbitWitness

/-! # Executable action of the canonical empty-graph permutation rows

The orbit cover represents a relabeling by rebuilding a 21-bit mask from a
row in `(List.range 7).permutations`.  This file checks, over the exact finite
representative and row tables used by the cover, that the rebuilt mask has the
expected pulled-along adjacency relation.  The exported theorem uses ordinary
list-membership hypotheses, so later semantic consumers do not depend on table
indices.
-/

namespace Erdos85

private theorem getD_ofFn {α : Type*} {n : Nat}
    (f : Fin n → α) (i : Fin n) (fallback : α) :
    (List.ofFn f).getD i.val fallback = f i := by
  let j : Fin (List.ofFn f).length :=
    ⟨i.val, by simpa only [List.length_ofFn] using i.isLt⟩
  calc
    (List.ofFn f).getD i.val fallback = (List.ofFn f).get j :=
      List.getD_eq_get (l := List.ofFn f) (d := fallback) j
    _ = f (Fin.cast (by simp only [List.length_ofFn]) j) :=
      List.get_ofFn f j
    _ = f i := by
      congr 1

/-- The executable 7-by-7 adjacency matrix of a 21-bit mask. -/
def sevenHighT0CanonicalEmptyAdjacencyRows (mask : Nat) :
    List (List Bool) :=
  List.ofFn fun left : Fin 7 =>
    List.ofFn fun right : Fin 7 =>
      sevenHighT0CanonicalEmptyAdj mask left.val right.val

/-- The adjacency matrix of the rebuilt mask, with its rows and columns
addressed by the source labels of the permutation.  The rebuilt mask is bound
outside the matrix traversal so the finite audit computes it only once. -/
def sevenHighT0CanonicalEmptyPermutedAdjacencyRows
    (permutation : List Nat) (mask : Nat) : List (List Bool) :=
  let permutedMask :=
    sevenHighT0CanonicalEmptyPermutedMask permutation mask
  List.ofFn fun left : Fin 7 =>
    List.ofFn fun right : Fin 7 =>
      sevenHighT0CanonicalEmptyAdj permutedMask
        (permutation.getD left.val 0)
        (permutation.getD right.val 0)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Finite audit of the raw mask action used in the orbit cover.  Keeping the
native check at the table-index boundary makes its scope explicit: precisely
the 43 pinned representatives and the 5,040 checked permutation rows. -/
theorem sevenHighT0CanonicalEmptyPermutationAction_table :
    (∀ representativeIndex :
        Fin sevenHighT0CanonicalEmptyRepresentatives.length,
      let representative :=
        sevenHighT0CanonicalEmptyRepresentatives.get representativeIndex
      representative.mask < 2 ^ 21) ∧
    (∀ representativeIndex :
        Fin sevenHighT0CanonicalEmptyRepresentatives.length,
      ∀ permutationIndex : Fin sevenHighT0CanonicalPermutationRows.length,
        let representative :=
          sevenHighT0CanonicalEmptyRepresentatives.get representativeIndex
        let permutation :=
          sevenHighT0CanonicalPermutationRows.get permutationIndex
        sevenHighT0CanonicalEmptyPermutedAdjacencyRows
            permutation representative.mask =
          sevenHighT0CanonicalEmptyAdjacencyRows representative.mask) := by
  native_decide

/-- Every pinned representative is a bounded 21-bit mask. -/
theorem sevenHighT0CanonicalEmptyRepresentative_mask_lt
    (representative : SevenHighT0CanonicalEmptyRepresentative)
    (hrepresentative :
      representative ∈ sevenHighT0CanonicalEmptyRepresentatives) :
    representative.mask < 2 ^ 21 := by
  obtain ⟨representativeIndex, hget⟩ :=
    List.get_of_mem hrepresentative
  subst representative
  exact sevenHighT0CanonicalEmptyPermutationAction_table.1
    representativeIndex

/-- Relabeling a pinned representative mask by a checked permutation row
transports executable adjacency along the corresponding `Fin 7` permutation. -/
theorem sevenHighT0CanonicalEmptyPermutedMask_adj
    (representative : SevenHighT0CanonicalEmptyRepresentative)
    (hrepresentative :
      representative ∈ sevenHighT0CanonicalEmptyRepresentatives)
    (permutation : List Nat)
    (hpermutation : permutation ∈ sevenHighT0CanonicalPermutationRows)
    (left right : Fin 7) :
    sevenHighT0CanonicalEmptyAdj
        (sevenHighT0CanonicalEmptyPermutedMask
          permutation representative.mask)
        (sevenHighT0CanonicalPermutationRowEquiv
          permutation hpermutation left).val
        (sevenHighT0CanonicalPermutationRowEquiv
          permutation hpermutation right).val =
      sevenHighT0CanonicalEmptyAdj
        representative.mask left.val right.val := by
  obtain ⟨representativeIndex, hrepresentativeGet⟩ :=
    List.get_of_mem hrepresentative
  obtain ⟨permutationIndex, hpermutationGet⟩ :=
    List.get_of_mem hpermutation
  rw [sevenHighT0CanonicalPermutationRowEquiv_apply,
    sevenHighT0CanonicalPermutationRowEquiv_apply]
  subst representative
  subst permutation
  have hrows := sevenHighT0CanonicalEmptyPermutationAction_table.2
    representativeIndex permutationIndex
  have hcell := congrArg
    (fun rows : List (List Bool) =>
      (rows.getD left.val []).getD right.val false) hrows
  simpa only [sevenHighT0CanonicalEmptyPermutedAdjacencyRows,
    sevenHighT0CanonicalEmptyAdjacencyRows, getD_ofFn] using hcell

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyRepresentative_mask_lt
#print axioms Erdos85.sevenHighT0CanonicalEmptyPermutedMask_adj

import Proofs.Erdos85OneHighV2CanonicalKey
import Proofs.Erdos85OneHighV2Inventory
import Proofs.Erdos85OneHighV2Enumerator

/-! # Native orbit-set comparison for the h=1 inventory -/

namespace Erdos85

def oneHighFiniteNatify (w : OneHighFiniteMissTable) :
    OneHighRelevantPair → Nat := fun pair => (w pair).val

def oneHighInventoryKeys (profile : Fin 5) : List Nat :=
  (oneHighInventoryFiniteTables profile).map fun w =>
    oneHighNatKey (oneHighFiniteNatify w)

def oneHighEnumCanonicalKeys (profile : Nat) : List Nat :=
  let perms : Finset (OneHighProfilePerm profile) := Finset.univ
  (oneHighEnumFiniteTables profile).map fun w =>
    perms.inf' ⟨oneHighProfilePermId profile, Finset.mem_univ _⟩
      (fun σ => oneHighNatKey (oneHighNatPermute σ.1 w))

theorem oneHighEnumCanonicalKeys_eq (profile : Nat) :
    oneHighEnumCanonicalKeys profile =
      (oneHighEnumFiniteTables profile).map
        (oneHighCanonicalKey profile) := by
  rfl

def oneHighAdjacentDedup (xs : List Nat) : List Nat :=
  xs.foldr (fun x acc => if acc.head? = some x then acc else x :: acc) []

theorem oneHighAdjacentDedup_mem_iff (key : Nat) (xs : List Nat) :
    key ∈ oneHighAdjacentDedup xs ↔ key ∈ xs := by
  induction xs generalizing key with
  | nil => simp [oneHighAdjacentDedup]
  | cons x rest ih =>
      simp only [oneHighAdjacentDedup, List.foldr_cons]
      split <;> rename_i hhead
      · change (oneHighAdjacentDedup rest).head? = some x at hhead
        have hx : x ∈ oneHighAdjacentDedup rest := List.mem_of_head? hhead
        have hxrest : x ∈ rest := (ih x).mp hx
        have hd : List.foldr
            (fun x acc => if acc.head? = some x then acc else x :: acc)
            [] rest = oneHighAdjacentDedup rest := rfl
        rw [hd]
        simp only [List.mem_cons]
        rw [ih key]
        constructor
        · exact Or.inr
        · rintro (rfl | hk)
          · exact hxrest
          · exact hk
      · have hd : List.foldr
            (fun x acc => if acc.head? = some x then acc else x :: acc)
            [] rest = oneHighAdjacentDedup rest := rfl
        rw [hd]
        simp only [List.mem_cons]
        rw [ih key]

def oneHighPrunedEnumRawKeySet (profile : Nat) : List Nat :=
  oneHighAdjacentDedup <|
    ((enumerateOneHighFiniteTables profile).map fun w =>
      oneHighNatKey (oneHighFiniteNatify w)).mergeSort

def oneHighInventoryOrbitRawKeySet (profile : Fin 5) : List Nat :=
  let perms : Finset (OneHighProfilePerm profile.val) := Finset.univ
  oneHighAdjacentDedup <|
    ((oneHighInventoryFiniteTables profile).flatMap fun w =>
      ((perms.image fun σ =>
        oneHighNatKey
          (oneHighNatPermute σ.1 (oneHighFiniteNatify w))).sort
            (· ≤ ·))).mergeSort

theorem oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_four :
    oneHighPrunedEnumRawKeySet 4 =
      oneHighInventoryOrbitRawKeySet 4 := by native_decide

theorem oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_three :
    oneHighPrunedEnumRawKeySet 3 =
      oneHighInventoryOrbitRawKeySet 3 := by native_decide

theorem oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_two :
    oneHighPrunedEnumRawKeySet 2 =
      oneHighInventoryOrbitRawKeySet 2 := by native_decide

theorem oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_one :
    oneHighPrunedEnumRawKeySet 1 =
      oneHighInventoryOrbitRawKeySet 1 := by native_decide

theorem oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_zero :
    oneHighPrunedEnumRawKeySet 0 =
      oneHighInventoryOrbitRawKeySet 0 := by native_decide

end Erdos85

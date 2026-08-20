import Proofs.Erdos85MuNegThreeOneTwoOwnerNonzero

/-!
# Relation valuation for the `mu=-3`, `(k,r)=(1,2)` owner bridge

This first graph-to-certificate layer turns a cross-defect relation `D` and
an exterior-owner adjacency relation `X` into the exact DIMACS valuation of
the checked owner CNFs.  The decode lemmas keep all later clause-family
proofs independent of DIMACS numbering.

Node: outline F.3, canonical negative switch endpoint `(-3,1,2)`.
-/

namespace Erdos85

/-- A cross owner cell is active precisely when it is not a defect cell. -/
def muNegThreeOwnerActive (D : Nat → Nat → Bool) (a : Nat) : Bool :=
  !D (muNegThreeCellRow a) (muNegThreeCellCol a)

/-- Variables `1..64` read the cross-defect grid; variables from `65` read
the normalized admissible owner-pair table. -/
def muNegThreeValOfRelations
    (D X : Nat → Nat → Bool) : DimacsValuation :=
  fun id ↦
    if 1 ≤ id ∧ id ≤ 64 then
      D ((id - 1) / 8) ((id - 1) % 8)
    else
      match muNegThreeHitPairs[id - 65]? with
      | some p => X p.1 p.2
      | none => false

/-- Decode a cross-defect variable. -/
theorem muNegThreeValOfRelations_dvar
    (D X : Nat → Nat → Bool) {i j : Nat} (hi : i < 8) (hj : j < 8) :
    muNegThreeValOfRelations D X (muNegThreeDVar (i * 8 + j)) = D i j := by
  have hrange : 1 ≤ muNegThreeDVar (i * 8 + j) ∧
      muNegThreeDVar (i * 8 + j) ≤ 64 := by
    unfold muNegThreeDVar
    omega
  have hdiv : (muNegThreeDVar (i * 8 + j) - 1) / 8 = i := by
    unfold muNegThreeDVar
    omega
  have hmod : (muNegThreeDVar (i * 8 + j) - 1) % 8 = j := by
    unfold muNegThreeDVar
    omega
  simp [muNegThreeValOfRelations, hrange, hdiv, hmod]

private theorem idxOf?_some_getElem? {α : Type*} [BEq α] [LawfulBEq α]
    {l : List α} {x : α} {k : Nat} (h : l.idxOf? x = some k) :
    l[k]? = some x := by
  induction l generalizing k with
  | nil => simp [List.idxOf?] at h
  | cons a l ih =>
    rw [List.idxOf?_cons] at h
    by_cases hax : a == x
    · simp [hax] at h
      subst h
      simpa using (eq_of_beq hax)
    · simp [hax, Option.map_eq_some_iff] at h
      obtain ⟨k', hk', rfl⟩ := h
      simpa using ih hk'

/-- Decode a generated hit variable at its normalized owner pair. -/
theorem muNegThreeValOfRelations_xvar
    (D X : Nat → Nat → Bool) {a b id : Nat}
    (h : muNegThreeXVar? a b = some id) :
    muNegThreeValOfRelations D X id = X (min a b) (max a b) := by
  unfold muNegThreeXVar? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k, hk, rfl⟩ := h
  have hget : muNegThreeHitPairs[k]? =
      some (if a < b then (a, b) else (b, a)) :=
    idxOf?_some_getElem? hk
  have hidx : k + 65 - 65 = k := by omega
  rcases Nat.lt_or_ge a b with hab | hab
  · have hmin : min a b = a := Nat.min_eq_left (Nat.le_of_lt hab)
    have hmax : max a b = b := Nat.max_eq_right (Nat.le_of_lt hab)
    simp [muNegThreeValOfRelations, hidx, hget, hab, hmin, hmax]
  · have hnab : ¬ a < b := Nat.not_lt.mpr hab
    have hmin : min a b = b := Nat.min_eq_right hab
    have hmax : max a b = a := Nat.max_eq_left hab
    simp [muNegThreeValOfRelations, hidx, hget, hnab, hmin, hmax]

/-- Every admissible normalized owner pair has a hit variable. -/
theorem muNegThreeXVar?_isSome_of_mem {a b : Nat}
    (hmem : (min a b, max a b) ∈ muNegThreeHitPairs) :
    (muNegThreeXVar? a b).isSome = true := by
  unfold muNegThreeXVar?
  rcases Nat.lt_or_ge a b with hab | hab
  · have hp : (if a < b then (a, b) else (b, a)) =
        (min a b, max a b) := by
      simp [hab, Nat.min_eq_left (Nat.le_of_lt hab),
        Nat.max_eq_right (Nat.le_of_lt hab)]
    rw [hp]
    simpa [Option.isSome_map] using List.isSome_idxOf?.mpr hmem
  · have hnab : ¬ a < b := Nat.not_lt.mpr hab
    have hp : (if a < b then (a, b) else (b, a)) =
        (min a b, max a b) := by
      simp [hnab, Nat.min_eq_right hab, Nat.max_eq_left hab]
    rw [hp]
    simpa [Option.isSome_map] using List.isSome_idxOf?.mpr hmem

end Erdos85

#print axioms Erdos85.muNegThreeValOfRelations_dvar
#print axioms Erdos85.muNegThreeValOfRelations_xvar
#print axioms Erdos85.muNegThreeXVar?_isSome_of_mem

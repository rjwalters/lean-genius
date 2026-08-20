import Proofs.Erdos85MuNegOneOneFourOwnerNonzero
import Proofs.Erdos85MuNegOneOneFourOwnerTypedModel

/-!
# Relation-induced valuations for the μ=-1 `(1,4)` owner-grid CNFs

Node: outline F.3 (μ=-1 lane; graph→valuation bridge, increment 3a of
the plan in squad msgs 13943/13945/13947).

The graph side of the bridge will supply two Boolean relations: a
cross-defect relation `D` on shore coordinates and an owner-vertex
adjacency relation `X` on typed owner indices.  This layer turns the
pair into a `DimacsValuation` matching the generator's numbering
(`muNegOneDVar` for `1..64`, hit-pair table offsets from `65`) and
proves the two decode laws the clause-family embeddings rest on.
Following the low-`8+8` bridge, relations are `Nat`-coded so the
generator tables apply without coercion.
-/

namespace Erdos85

/-- Activity of an owner index under a cross-defect relation: the
sixteen within-shore owners are always active, a cross cell is active
exactly when it is not a defect cell. -/
def muNegOneOwnerActive (D : Nat → Nat → Bool) (e : Nat) : Bool :=
  if e < 16 then true else !D ((e - 16) / 8) ((e - 16) % 8)

/-- The valuation induced by a cross-defect relation and an owner
adjacency relation.  Variables `1..64` are the cross-defect grid in
row-major order; variables from `65` follow the admissible hit-pair
table of the sector mode. -/
def muNegOneValOfRelations (uTri vTri : Bool)
    (D : Nat → Nat → Bool) (X : Nat → Nat → Bool) : DimacsValuation :=
  fun id ↦
    if 1 ≤ id ∧ id ≤ 64 then D ((id - 1) / 8) ((id - 1) % 8)
    else
      match (muNegOneHitPairs uTri vTri)[id - 65]? with
      | some p => X p.1 p.2
      | none => false

/-- Decode law for the cross-defect block. -/
theorem muNegOneValOfRelations_dvar (uTri vTri : Bool)
    (D : Nat → Nat → Bool) (X : Nat → Nat → Bool)
    {i j : Nat} (hi : i < 8) (hj : j < 8) :
    muNegOneValOfRelations uTri vTri D X (muNegOneDVar i j) = D i j := by
  have hrange : 1 ≤ muNegOneDVar i j ∧ muNegOneDVar i j ≤ 64 := by
    unfold muNegOneDVar
    omega
  have hdiv : (muNegOneDVar i j - 1) / 8 = i := by
    unfold muNegOneDVar
    omega
  have hmod : (muNegOneDVar i j - 1) % 8 = j := by
    unfold muNegOneDVar
    omega
  simp [muNegOneValOfRelations, hrange, hdiv, hmod]

/-- A successful index lookup names the element at that position. -/
theorem list_idxOf?_some_getElem? {α : Type*} [BEq α] [LawfulBEq α]
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

/-- Decode law for the hit block: a generated hit variable reads the
owner adjacency relation at its normalized index pair. -/
theorem muNegOneValOfRelations_xvar (uTri vTri : Bool)
    (D : Nat → Nat → Bool) (X : Nat → Nat → Bool)
    {a b id : Nat}
    (h : muNegOneXVar? (muNegOneHitPairs uTri vTri) a b = some id) :
    muNegOneValOfRelations uTri vTri D X id =
      X (min a b) (max a b) := by
  unfold muNegOneXVar? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k, hk, rfl⟩ := h
  have hget : (muNegOneHitPairs uTri vTri)[k]? =
      some (if a < b then (a, b) else (b, a)) := by
    exact list_idxOf?_some_getElem? hk
  have hidx : k + 65 - 65 = k := by omega
  rcases Nat.lt_or_ge a b with hab | hab
  · have hmin : min a b = a := Nat.min_eq_left (Nat.le_of_lt hab)
    have hmax : max a b = b := Nat.max_eq_right (Nat.le_of_lt hab)
    simp [muNegOneValOfRelations, hidx, hget, hab, hmin, hmax]
  · have hmin : min a b = b := Nat.min_eq_right hab
    have hmax : max a b = a := Nat.max_eq_left hab
    have hnab : ¬ a < b := Nat.not_lt.mpr hab
    simp [muNegOneValOfRelations, hidx, hget, hnab, hmin, hmax]

/-- Every admissible owner pair of the generated table carries a hit
variable (three canonical modes). -/
theorem muNegOneXVar?_isSome_of_mem (uTri vTri : Bool)
    {a b : Nat}
    (hmem : (min a b, max a b) ∈ muNegOneHitPairs uTri vTri) :
    (muNegOneXVar? (muNegOneHitPairs uTri vTri) a b).isSome = true := by
  unfold muNegOneXVar?
  rcases Nat.lt_or_ge a b with hab | hab
  · have : (if a < b then (a, b) else (b, a)) = (min a b, max a b) := by
      simp [hab, Nat.min_eq_left (Nat.le_of_lt hab),
        Nat.max_eq_right (Nat.le_of_lt hab)]
    rw [this]
    simpa [Option.isSome_map] using List.isSome_idxOf?.mpr hmem
  · have hnab : ¬ a < b := Nat.not_lt.mpr hab
    have : (if a < b then (a, b) else (b, a)) = (min a b, max a b) := by
      simp [hnab, Nat.min_eq_right hab, Nat.max_eq_left hab]
    rw [this]
    simpa [Option.isSome_map] using List.isSome_idxOf?.mpr hmem

end Erdos85

#print axioms Erdos85.muNegOneValOfRelations_dvar
#print axioms Erdos85.muNegOneValOfRelations_xvar
#print axioms Erdos85.muNegOneXVar?_isSome_of_mem

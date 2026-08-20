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

/-- Graph-shaped finite content of the seven owner-CNF families.  It uses
only Nat-coded grid/owner relations and generator-independent cardinality or
uniqueness statements; DIMACS numbering is confined to the valuation above.
-/
structure MuNegThreeOneTwoFiniteSemantics (fwd : Bool) (c : Nat)
    (D X : Nat → Nat → Bool) : Prop where
  fixed : ∀ i j, i < 8 → j < 8 → i % 2 == j % 2 →
    D i j = (j == muNegThreePhi fwd c i)
  opposite_rows : ∀ i, i < 8 →
    (((List.range 8).filter fun j => !(i % 2 == j % 2)).countP
      fun j => D i j) = 1
  opposite_columns : ∀ j, j < 8 →
    (((List.range 8).filter fun i => !(i % 2 == j % 2)).countP
      fun i => D i j) = 1
  intertwine : ∀ i j, i < 8 → j < 8 →
    (cond (D ((i + 7) % 8) j) 1 0) +
      (cond (D ((i + 1) % 8) j) 1 0) =
    (cond (D i ((j + 1) % 8)) 1 0) +
      (cond (D i ((j + 7) % 8)) 1 0)
  hit_active : ∀ a b, (a, b) ∈ muNegThreeHitPairs → X a b = true →
    muNegThreeOwnerActive D a = true ∧
      muNegThreeOwnerActive D b = true
  service_exists : ∀ a, a < 64 → muNegThreeOwnerActive D a = true →
    ∀ (onRow : Bool) t,
      (if onRow then
        muNegThreeOffsetOne (muNegThreeCellRow a) t
      else muNegThreeOffsetOne (muNegThreeCellCol a) t) = false →
      ∃ b, b < 64 ∧ b ≠ a ∧
        (if onRow then muNegThreeCellRow b = t
          else muNegThreeCellCol b = t) ∧
        (min a b, max a b) ∈ muNegThreeHitPairs ∧
        X (min a b) (max a b) = true
  service_unique : ∀ a, a < 64 → muNegThreeOwnerActive D a = true →
    ∀ (onRow : Bool) t,
      (if onRow then
        muNegThreeOffsetOne (muNegThreeCellRow a) t
      else muNegThreeOffsetOne (muNegThreeCellCol a) t) = false →
      ∀ b d, b < 64 → b ≠ a →
        (if onRow then muNegThreeCellRow b = t
          else muNegThreeCellCol b = t) →
        (min a b, max a b) ∈ muNegThreeHitPairs →
        X (min a b) (max a b) = true →
        d < 64 → d ≠ a →
        (if onRow then muNegThreeCellRow d = t
          else muNegThreeCellCol d = t) →
        (min a d, max a d) ∈ muNegThreeHitPairs →
        X (min a d) (max a d) = true → b = d
  c4_intersecting : ∀ a b g, a < b → b < 64 → g < 64 →
    g ≠ a → g ≠ b →
    (muNegThreeCellRow a = muNegThreeCellRow b ∨
      muNegThreeCellCol a = muNegThreeCellCol b) →
    (min a g, max a g) ∈ muNegThreeHitPairs →
    (min b g, max b g) ∈ muNegThreeHitPairs →
    X (min a g) (max a g) = true →
    X (min b g) (max b g) = true → False
  c4_no_two : ∀ a b g h, a < b → b < 64 → g < 64 → h < 64 →
    g ≠ h → g ≠ a → g ≠ b → h ≠ a → h ≠ b →
    muNegThreeCellRow a ≠ muNegThreeCellRow b →
    muNegThreeCellCol a ≠ muNegThreeCellCol b →
    (min a g, max a g) ∈ muNegThreeHitPairs →
    (min b g, max b g) ∈ muNegThreeHitPairs →
    (min a h, max a h) ∈ muNegThreeHitPairs →
    (min b h, max b h) ∈ muNegThreeHitPairs →
    X (min a g) (max a g) = true →
    X (min b g) (max b g) = true →
    X (min a h) (max a h) = true →
    X (min b h) (max b h) = true → False

/-- The fixed same-sign matching family is already embedded by the relation
valuation and the first finite-semantics field. -/
theorem muNegThreeFiniteSemantics_fixed
    {fwd : Bool} {c : Nat} {D X : Nat → Nat → Bool}
    (h : MuNegThreeOneTwoFiniteSemantics fwd c D X) :
    ∀ clause ∈ muNegThreeFixClauses fwd c,
      dimacsClauseSatisfied (muNegThreeValOfRelations D X) clause := by
  apply muNegThreeFixClauses_satisfied
  intro i j hi hj hparity
  rw [muNegThreeValOfRelations_dvar D X hi hj]
  exact h.fixed i j hi hj hparity

end Erdos85

#print axioms Erdos85.muNegThreeValOfRelations_dvar
#print axioms Erdos85.muNegThreeValOfRelations_xvar
#print axioms Erdos85.muNegThreeXVar?_isSome_of_mem
#print axioms Erdos85.muNegThreeFiniteSemantics_fixed

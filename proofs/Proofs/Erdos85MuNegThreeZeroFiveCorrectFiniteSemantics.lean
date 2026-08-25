import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerCnf

/-!
# Finite semantics for the corrected h305 owner CNF

This is the graph-to-valuation side of the honest 88-owner encoding.  It is
kept separate from the older h305 finite-semantics file, whose valuation and
owner activity are hard-coded to the 80-owner h114 table.
-/

namespace Erdos85

open Std Sat

private theorem h305Correct_list_idxOf?_some_getElem?
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    {l : List alpha} {x : alpha} {k : Nat} (h : l.idxOf? x = some k) :
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

private theorem h305Correct_pair_norm (a b : Nat) :
    (if a < b then (a, b) else (b, a)) = (min a b, max a b) := by
  rcases Nat.lt_or_ge a b with h | h
  · simp [h, Nat.min_eq_left (Nat.le_of_lt h),
      Nat.max_eq_right (Nat.le_of_lt h)]
  · simp [Nat.not_lt.mpr h, Nat.min_eq_right h, Nat.max_eq_left h]

/-- Activity in the corrected owner table.  Fixed shore owners have no
guard; a cross owner is active exactly when its defect guard is false. -/
def muNegThreeZeroFiveCorrectOwnerActive (uTri vTri : Bool)
    (D : Nat → Nat → Bool) (a : Nat) : Bool :=
  let os := muNegThreeZeroFiveCorrectOwners uTri vTri
  let p := os[a]!
  match muNegThreeZeroFiveCorrectGuard? os a with
  | none => true
  | some _ => !D p.1 (p.2 - 8)

/-- Valuation matching the corrected hit-pair table. -/
def muNegThreeZeroFiveCorrectValOfRelations (uTri vTri : Bool)
    (D X : Nat → Nat → Bool) : DimacsValuation :=
  fun id =>
    if 1 ≤ id ∧ id ≤ 64 then D ((id - 1) / 8) ((id - 1) % 8)
    else
      match (muNegThreeZeroFiveCorrectHitPairs uTri vTri)[id - 65]? with
      | some p => X p.1 p.2
      | none => false

theorem muNegThreeZeroFiveCorrectValOfRelations_dvar
    (uTri vTri : Bool) (D X : Nat → Nat → Bool)
    {i j : Nat} (hi : i < 8) (hj : j < 8) :
    muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X
      (muNegOneDVar i j) = D i j := by
  have hrange : 1 ≤ muNegOneDVar i j ∧ muNegOneDVar i j ≤ 64 := by
    unfold muNegOneDVar
    omega
  have hdiv : (muNegOneDVar i j - 1) / 8 = i := by
    unfold muNegOneDVar
    omega
  have hmod : (muNegOneDVar i j - 1) % 8 = j := by
    unfold muNegOneDVar
    omega
  simp [muNegThreeZeroFiveCorrectValOfRelations, hrange, hdiv, hmod]

theorem muNegThreeZeroFiveCorrectValOfRelations_xvar
    (uTri vTri : Bool) (D X : Nat → Nat → Bool)
    {a b id : Nat}
    (h : muNegThreeZeroFiveCorrectXVar?
      (muNegThreeZeroFiveCorrectHitPairs uTri vTri) a b = some id) :
    muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X id =
      X (min a b) (max a b) := by
  unfold muNegThreeZeroFiveCorrectXVar? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k, hk, rfl⟩ := h
  have hget : (muNegThreeZeroFiveCorrectHitPairs uTri vTri)[k]? =
      some (if a < b then (a, b) else (b, a)) :=
    h305Correct_list_idxOf?_some_getElem? hk
  have hidx : k + 65 - 65 = k := by omega
  rcases Nat.lt_or_ge a b with hab | hab
  · have hmin : min a b = a := Nat.min_eq_left (Nat.le_of_lt hab)
    have hmax : max a b = b := Nat.max_eq_right (Nat.le_of_lt hab)
    simp [muNegThreeZeroFiveCorrectValOfRelations, hidx, hget, hab,
      hmin, hmax]
  · have hmin : min a b = b := Nat.min_eq_right hab
    have hmax : max a b = a := Nat.max_eq_left hab
    have hnab : ¬a < b := Nat.not_lt.mpr hab
    simp [muNegThreeZeroFiveCorrectValOfRelations, hidx, hget, hnab,
      hmin, hmax]

theorem muNegThreeZeroFiveCorrectXVar?_isSome_of_mem
    (uTri vTri : Bool) {a b : Nat}
    (hmem : (min a b, max a b) ∈
      muNegThreeZeroFiveCorrectHitPairs uTri vTri) :
    (muNegThreeZeroFiveCorrectXVar?
      (muNegThreeZeroFiveCorrectHitPairs uTri vTri) a b).isSome = true := by
  unfold muNegThreeZeroFiveCorrectXVar?
  rcases Nat.lt_or_ge a b with hab | hab
  · have hp : (if a < b then (a, b) else (b, a)) =
        (min a b, max a b) := by
      simp [hab, Nat.min_eq_left (Nat.le_of_lt hab),
        Nat.max_eq_right (Nat.le_of_lt hab)]
    rw [hp]
    simpa [Option.isSome_map] using List.isSome_idxOf?.mpr hmem
  · have hnab : ¬a < b := Nat.not_lt.mpr hab
    have hp : (if a < b then (a, b) else (b, a)) =
        (min a b, max a b) := by
      simp [hnab, Nat.min_eq_right hab, Nat.max_eq_left hab]
    rw [hp]
    simpa [Option.isSome_map] using List.isSome_idxOf?.mpr hmem

theorem muNegThreeZeroFiveCorrectXVar?_bounds
    {pairs : List (Nat × Nat)} {a b x : Nat}
    (h : muNegThreeZeroFiveCorrectXVar? pairs a b = some x) :
    65 ≤ x := by
  unfold muNegThreeZeroFiveCorrectXVar? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k, _, rfl⟩ := h
  omega

theorem muNegThreeZeroFiveCorrectXVar?_key_mem
    {pairs : List (Nat × Nat)} {a b x : Nat}
    (h : muNegThreeZeroFiveCorrectXVar? pairs a b = some x) :
    (min a b, max a b) ∈ pairs := by
  unfold muNegThreeZeroFiveCorrectXVar? at h
  rw [h305Correct_pair_norm, Option.map_eq_some_iff] at h
  obtain ⟨k, hk, _⟩ := h
  exact List.mem_of_getElem? (h305Correct_list_idxOf?_some_getElem? hk)

theorem muNegThreeZeroFiveCorrectXVar?_inj
    {pairs : List (Nat × Nat)} {a b b' x : Nat}
    (h : muNegThreeZeroFiveCorrectXVar? pairs a b = some x)
    (h' : muNegThreeZeroFiveCorrectXVar? pairs a b' = some x) :
    (min a b, max a b) = (min a b', max a b') := by
  unfold muNegThreeZeroFiveCorrectXVar? at h h'
  rw [h305Correct_pair_norm, Option.map_eq_some_iff] at h h'
  obtain ⟨k, hk, hkx⟩ := h
  obtain ⟨k', hk', hk'x⟩ := h'
  have hkk : k = k' := by omega
  subst hkk
  have e1 := h305Correct_list_idxOf?_some_getElem? hk
  have e2 := h305Correct_list_idxOf?_some_getElem? hk'
  rw [e1] at e2
  exact Option.some.inj e2

/-- Non-cross semantic obligations for the corrected 88-owner table. -/
structure MuNegThreeZeroFiveCorrectNonCrossSemantics
    (uTri vTri sigma : Bool) (D X : Nat → Nat → Bool) : Prop where
  intertwine : ∀ i j, i < 8 → j < 8 →
    (cond (D ((i + 7) % 8) j) 1 0) +
        (cond (D ((i + 1) % 8) j) 1 0) =
      (cond (D i ((j + 1) % 8)) 1 0) +
        (cond (D i ((j + 7) % 8)) 1 0)
  hit_active : ∀ a b,
    (a, b) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
    X a b = true →
    muNegThreeZeroFiveCorrectOwnerActive uTri vTri D a = true ∧
      muNegThreeZeroFiveCorrectOwnerActive uTri vTri D b = true
  service_exists : ∀ a, a < 88 →
    muNegThreeZeroFiveCorrectOwnerActive uTri vTri D a = true →
    ∀ w ∈ muNegOneTwelve
      ((muNegThreeZeroFiveCorrectOwners uTri vTri)[a]!),
      ∃ b, b < 88 ∧ b ≠ a ∧
        muNegOnePairMem
          ((muNegThreeZeroFiveCorrectOwners uTri vTri)[b]!) w = true ∧
        (min a b, max a b) ∈
          muNegThreeZeroFiveCorrectHitPairs uTri vTri ∧
        X (min a b) (max a b) = true
  service_unique : ∀ a, a < 88 →
    muNegThreeZeroFiveCorrectOwnerActive uTri vTri D a = true →
    ∀ w ∈ muNegOneTwelve
      ((muNegThreeZeroFiveCorrectOwners uTri vTri)[a]!),
      ∀ b c, b < 88 → b ≠ a →
        muNegOnePairMem
          ((muNegThreeZeroFiveCorrectOwners uTri vTri)[b]!) w = true →
        (min a b, max a b) ∈
          muNegThreeZeroFiveCorrectHitPairs uTri vTri →
        X (min a b) (max a b) = true → c < 88 → c ≠ a →
        muNegOnePairMem
          ((muNegThreeZeroFiveCorrectOwners uTri vTri)[c]!) w = true →
        (min a c, max a c) ∈
          muNegThreeZeroFiveCorrectHitPairs uTri vTri →
        X (min a c) (max a c) = true → b = c
  c4_intersecting : ∀ a b g, a < b → b < 88 → g < 88 →
    g ≠ a → g ≠ b →
    muNegOneShare ((muNegThreeZeroFiveCorrectOwners uTri vTri)[a]!)
      ((muNegThreeZeroFiveCorrectOwners uTri vTri)[b]!) = true →
    (min a g, max a g) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
    (min b g, max b g) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
    X (min a g) (max a g) = true →
    X (min b g) (max b g) = true → False
  c4_no_two : ∀ a b g h, a < b → b < 88 → g < 88 → h < 88 →
    g ≠ h → g ≠ a → g ≠ b → h ≠ a → h ≠ b →
    muNegOneShare ((muNegThreeZeroFiveCorrectOwners uTri vTri)[a]!)
      ((muNegThreeZeroFiveCorrectOwners uTri vTri)[b]!) = false →
    (min a g, max a g) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
    (min b g, max b g) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
    (min a h, max a h) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
    (min b h, max b h) ∈ muNegThreeZeroFiveCorrectHitPairs uTri vTri →
    X (min a g) (max a g) = true →
    X (min b g) (max b g) = true →
    X (min a h) (max a h) = true →
    X (min b h) (max b h) = true → False

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectValOfRelations_dvar
#print axioms Erdos85.muNegThreeZeroFiveCorrectValOfRelations_xvar

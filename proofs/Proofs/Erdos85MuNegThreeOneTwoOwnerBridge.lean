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

open Std Sat

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

private theorem eq_of_countP_eq_one_of_true
    {α : Type*} (l : List α) (p : α → Bool) {a b : α}
    (hone : l.countP p = 1) (ha : a ∈ l) (hb : b ∈ l)
    (hpa : p a = true) (hpb : p b = true) : a = b := by
  induction l generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
    by_cases hx : p x = true
    · have hzero : xs.countP p = 0 := by
        simpa [List.countP_cons, hx] using hone
      have hnone := List.countP_eq_zero.mp hzero
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · rfl
        · exact False.elim ((hnone b hb) hpb)
      · exact False.elim ((hnone a ha) hpa)
    · have hx' : p x = false := Bool.eq_false_of_not_eq_true hx
      have hone' : xs.countP p = 1 := by
        simpa [List.countP_cons, hx'] using hone
      simp only [List.mem_cons] at ha hb
      have hax : a ≠ x := by rintro rfl; exact hx hpa
      have hbx : b ≠ x := by rintro rfl; exact hx hpb
      exact ih hone' (ha.resolve_left hax) (hb.resolve_left hbx) hpa hpb

private theorem dimacs_neg_satisfied_of_false
    {val : DimacsValuation} {lit : Int} (hpos : 0 < lit)
    (hfalse : dimacsLitValue val lit = false) :
    dimacsLitValue val (-lit) = true := by
  simp only [dimacsLitValue, if_pos hpos] at hfalse
  rw [dimacsLitValue, if_neg (by omega), Int.natAbs_neg]
  simp [hfalse]

private theorem muNegThreeExactlyOne_of_count_one
    (val : DimacsValuation) (coords : List Nat) (p : Nat → Bool)
    (lit : Nat → Int) (hpos : ∀ j ∈ coords, 0 < lit j)
    (hdecode : ∀ j ∈ coords, dimacsLitValue val (lit j) = p j)
    (hone : coords.countP p = 1) :
    MuNegThreeExactlyOneSemantics val (coords.map lit) := by
  constructor
  · obtain ⟨j, hj, hpj⟩ := List.countP_pos_iff.mp (by omega : 0 < coords.countP p)
    refine ⟨lit j, List.mem_map.mpr ⟨j, hj, rfl⟩, ?_⟩
    rw [hdecode j hj, hpj]
  · intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    by_cases hva : dimacsLitValue val (lit a) = true
    · by_cases hvb : dimacsLitValue val (lit b) = true
      · have hpa : p a = true := by simpa [hdecode a ha] using hva
        have hpb : p b = true := by simpa [hdecode b hb] using hvb
        have hab := eq_of_countP_eq_one_of_true coords p hone ha hb hpa hpb
        subst b
        omega
      · have hvb' : dimacsLitValue val (lit b) = false :=
          Bool.eq_false_of_not_eq_true hvb
        refine ⟨-(lit b), by simp, ?_⟩
        exact dimacs_neg_satisfied_of_false (hpos b hb) hvb'
    · have hva' : dimacsLitValue val (lit a) = false :=
        Bool.eq_false_of_not_eq_true hva
      refine ⟨-(lit a), by simp, ?_⟩
      exact dimacs_neg_satisfied_of_false (hpos a ha) hva'

/-- Embed the opposite-sign exactly-one row family. -/
theorem muNegThreeFiniteSemantics_opposite_rows
    {fwd : Bool} {c : Nat} {D X : Nat → Nat → Bool}
    (h : MuNegThreeOneTwoFiniteSemantics fwd c D X) :
    ∀ clause ∈ muNegThreeOppRowClauses,
      dimacsClauseSatisfied (muNegThreeValOfRelations D X) clause := by
  apply muNegThreeOppRowClauses_satisfied
  intro i hi
  let coords := (List.range 8).filter fun j => !(i % 2 == j % 2)
  apply muNegThreeExactlyOne_of_count_one (muNegThreeValOfRelations D X)
    coords (fun j => D i j)
    (fun j => Int.ofNat (muNegThreeDVar (i * 8 + j)))
  · intro j hj
    change Int.ofNat 0 < Int.ofNat (muNegThreeDVar (i * 8 + j))
    exact (Int.ofNat_lt).2 (by simp [muNegThreeDVar])
  · intro j hj
    have hj8 : j < 8 := List.mem_range.mp (List.mem_filter.mp hj).1
    have hdpos : 0 < muNegThreeDVar (i * 8 + j) := by
      simp [muNegThreeDVar]
    simp [dimacsLitValue, hdpos,
      muNegThreeValOfRelations_dvar D X hi hj8]
  · exact h.opposite_rows i hi

/-- Embed the opposite-sign exactly-one column family. -/
theorem muNegThreeFiniteSemantics_opposite_columns
    {fwd : Bool} {c : Nat} {D X : Nat → Nat → Bool}
    (h : MuNegThreeOneTwoFiniteSemantics fwd c D X) :
    ∀ clause ∈ muNegThreeOppColClauses,
      dimacsClauseSatisfied (muNegThreeValOfRelations D X) clause := by
  apply muNegThreeOppColClauses_satisfied
  intro j hj
  let coords := (List.range 8).filter fun i => !(i % 2 == j % 2)
  apply muNegThreeExactlyOne_of_count_one (muNegThreeValOfRelations D X)
    coords (fun i => D i j)
    (fun i => Int.ofNat (muNegThreeDVar (i * 8 + j)))
  · intro i hi
    change Int.ofNat 0 < Int.ofNat (muNegThreeDVar (i * 8 + j))
    exact (Int.ofNat_lt).2 (by simp [muNegThreeDVar])
  · intro i hi
    have hi8 : i < 8 := List.mem_range.mp (List.mem_filter.mp hi).1
    have hdpos : 0 < muNegThreeDVar (i * 8 + j) := by
      simp [muNegThreeDVar]
    simp [dimacsLitValue, hdpos,
      muNegThreeValOfRelations_dvar D X hi8 hj]
  · exact h.opposite_columns j hj

end Erdos85

#print axioms Erdos85.muNegThreeValOfRelations_dvar
#print axioms Erdos85.muNegThreeValOfRelations_xvar
#print axioms Erdos85.muNegThreeXVar?_isSome_of_mem
#print axioms Erdos85.muNegThreeFiniteSemantics_fixed
#print axioms Erdos85.muNegThreeFiniteSemantics_opposite_rows
#print axioms Erdos85.muNegThreeFiniteSemantics_opposite_columns

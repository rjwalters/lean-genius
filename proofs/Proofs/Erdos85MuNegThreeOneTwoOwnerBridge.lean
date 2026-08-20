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

private theorem muNegThree_bool_sum_eq_cases {A B C E : Bool}
    (h : (cond A 1 0) + (cond B 1 0) =
      (cond C 1 0) + (cond E 1 0)) :
    (A = true → C = true ∨ E = true) ∧
    (B = true → C = true ∨ E = true) ∧
    (C = true → A = true ∨ B = true) ∧
    (E = true → A = true ∨ B = true) ∧
    (A = true → B = true → C = true) ∧
    (A = true → B = true → E = true) ∧
    (C = true → E = true → A = true) ∧
    (C = true → E = true → B = true) := by
  revert h
  cases A <;> cases B <;> cases C <;> cases E <;> decide

private theorem muNegThree_dimacsLitValue_ofNat
    {val : DimacsValuation} {n : Nat} (hn : 0 < n) :
    dimacsLitValue val (Int.ofNat n) = val n := by
  have h : (0 : Int) < Int.ofNat n := by
    show (0 : Int) < (n : Int)
    exact_mod_cast hn
  rw [dimacsLitValue, if_pos h]
  simp

private theorem muNegThree_dimacsLitValue_neg_ofNat
    {val : DimacsValuation} {n : Nat} (hn : 0 < n) :
    dimacsLitValue val (-Int.ofNat n) = !val n := by
  have h : (0 : Int) < Int.ofNat n := by
    show (0 : Int) < (n : Int)
    exact_mod_cast hn
  rw [dimacsLitValue, if_neg (by omega), Int.natAbs_neg]
  simp

/-- The eight local intertwining clauses follow from equality of the two
Boolean neighbor counts. -/
private theorem muNegThreeSumEq_satisfied
    {val : DimacsValuation} {a b c d : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcount : (cond (val a) 1 0) + (cond (val b) 1 0) =
      (cond (val c) 1 0) + (cond (val d) 1 0)) :
    ∀ clause ∈ muNegThreeSumEq (Int.ofNat a) (Int.ofNat b)
      (Int.ofNat c) (Int.ofNat d),
      dimacsClauseSatisfied val clause := by
  obtain ⟨hAcd, hBcd, hCab, hDab, hABc, hABd, hCDa, hCDb⟩ :=
    muNegThree_bool_sum_eq_cases hcount
  intro clause hclause
  simp only [muNegThreeSumEq, List.mem_cons, List.not_mem_nil, or_false]
    at hclause
  rcases hclause with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases hA : val a = true
    · rcases hAcd hA with h | h
      · exact ⟨Int.ofNat c, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hc, h]⟩
      · exact ⟨Int.ofNat d, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hd, h]⟩
    · exact ⟨-Int.ofNat a, by simp, by
        rw [muNegThree_dimacsLitValue_neg_ofNat ha]; simpa using hA⟩
  · by_cases hB : val b = true
    · rcases hBcd hB with h | h
      · exact ⟨Int.ofNat c, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hc, h]⟩
      · exact ⟨Int.ofNat d, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hd, h]⟩
    · exact ⟨-Int.ofNat b, by simp, by
        rw [muNegThree_dimacsLitValue_neg_ofNat hb]; simpa using hB⟩
  · by_cases hC : val c = true
    · rcases hCab hC with h | h
      · exact ⟨Int.ofNat a, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat ha, h]⟩
      · exact ⟨Int.ofNat b, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hb, h]⟩
    · exact ⟨-Int.ofNat c, by simp, by
        rw [muNegThree_dimacsLitValue_neg_ofNat hc]; simpa using hC⟩
  · by_cases hD : val d = true
    · rcases hDab hD with h | h
      · exact ⟨Int.ofNat a, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat ha, h]⟩
      · exact ⟨Int.ofNat b, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hb, h]⟩
    · exact ⟨-Int.ofNat d, by simp, by
        rw [muNegThree_dimacsLitValue_neg_ofNat hd]; simpa using hD⟩
  · by_cases hA : val a = true
    · by_cases hB : val b = true
      · exact ⟨Int.ofNat c, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hc, hABc hA hB]⟩
      · exact ⟨-Int.ofNat b, by simp, by
          rw [muNegThree_dimacsLitValue_neg_ofNat hb]; simpa using hB⟩
    · exact ⟨-Int.ofNat a, by simp, by
        rw [muNegThree_dimacsLitValue_neg_ofNat ha]; simpa using hA⟩
  · by_cases hA : val a = true
    · by_cases hB : val b = true
      · exact ⟨Int.ofNat d, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hd, hABd hA hB]⟩
      · exact ⟨-Int.ofNat b, by simp, by
          rw [muNegThree_dimacsLitValue_neg_ofNat hb]; simpa using hB⟩
    · exact ⟨-Int.ofNat a, by simp, by
        rw [muNegThree_dimacsLitValue_neg_ofNat ha]; simpa using hA⟩
  · by_cases hC : val c = true
    · by_cases hD : val d = true
      · exact ⟨Int.ofNat a, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat ha, hCDa hC hD]⟩
      · exact ⟨-Int.ofNat d, by simp, by
          rw [muNegThree_dimacsLitValue_neg_ofNat hd]; simpa using hD⟩
    · exact ⟨-Int.ofNat c, by simp, by
        rw [muNegThree_dimacsLitValue_neg_ofNat hc]; simpa using hC⟩
  · by_cases hC : val c = true
    · by_cases hD : val d = true
      · exact ⟨Int.ofNat b, by simp, by
          rw [muNegThree_dimacsLitValue_ofNat hb, hCDb hC hD]⟩
      · exact ⟨-Int.ofNat d, by simp, by
          rw [muNegThree_dimacsLitValue_neg_ofNat hd]; simpa using hD⟩
    · exact ⟨-Int.ofNat c, by simp, by
        rw [muNegThree_dimacsLitValue_neg_ofNat hc]; simpa using hC⟩

/-- Embed every entrywise C8 intertwining clause. -/
theorem muNegThreeFiniteSemantics_intertwining
    {fwd : Bool} {c : Nat} {D X : Nat → Nat → Bool}
    (h : MuNegThreeOneTwoFiniteSemantics fwd c D X) :
    ∀ clause ∈ muNegThreeIntertwineClauses,
      dimacsClauseSatisfied (muNegThreeValOfRelations D X) clause := by
  apply muNegThreeIntertwineClauses_satisfied
  intro i j hi hj
  let a := muNegThreeDVar (((i + 7) % 8) * 8 + j)
  let b := muNegThreeDVar (((i + 1) % 8) * 8 + j)
  let cc := muNegThreeDVar (i * 8 + (j + 1) % 8)
  let d := muNegThreeDVar (i * 8 + (j + 7) % 8)
  apply muNegThreeSumEq_satisfied
  · simp [a, muNegThreeDVar]
  · simp [b, muNegThreeDVar]
  · simp [cc, muNegThreeDVar]
  · simp [d, muNegThreeDVar]
  · have hi7 : (i + 7) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hi1 : (i + 1) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hj1 : (j + 1) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have hj7 : (j + 7) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    simpa [a, b, cc, d,
      muNegThreeValOfRelations_dvar D X hi7 hj,
      muNegThreeValOfRelations_dvar D X hi1 hj,
      muNegThreeValOfRelations_dvar D X hi hj1,
      muNegThreeValOfRelations_dvar D X hi hj7] using
        h.intertwine i j hi hj

theorem muNegThreeHitPairs_lt {p : Nat × Nat}
    (hp : p ∈ muNegThreeHitPairs) : p.1 < p.2 ∧ p.2 < 64 := by
  simp only [muNegThreeHitPairs, List.mem_flatMap, List.mem_range,
    List.mem_map, List.mem_filter] at hp
  obtain ⟨a, ha, b, ⟨hb, hab⟩, rfl⟩ := hp
  exact ⟨((Bool.and_eq_true _ _).mp hab).1 |> of_decide_eq_true, hb⟩

theorem muNegThreeXVar?_bounds {a b x : Nat}
    (h : muNegThreeXVar? a b = some x) : 65 ≤ x := by
  unfold muNegThreeXVar? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k, _, rfl⟩ := h
  omega

theorem muNegThreeXVar?_key_mem {a b x : Nat}
    (h : muNegThreeXVar? a b = some x) :
    (min a b, max a b) ∈ muNegThreeHitPairs := by
  unfold muNegThreeXVar? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k, hk, _⟩ := h
  have hget := idxOf?_some_getElem? hk
  have hmem := List.mem_of_getElem? hget
  rcases Nat.lt_or_ge a b with hab | hab
  · simpa [hab, Nat.min_eq_left (Nat.le_of_lt hab),
      Nat.max_eq_right (Nat.le_of_lt hab)] using hmem
  · have hnab : ¬ a < b := Nat.not_lt.mpr hab
    simpa [hnab, Nat.min_eq_right hab, Nat.max_eq_left hab] using hmem

/-- Embed the hit-activity family: a true owner hit forces both cross cells
to be active, hence their negative defect guards satisfy the two clauses. -/
theorem muNegThreeFiniteSemantics_hit_activity
    {fwd : Bool} {c : Nat} {D X : Nat → Nat → Bool}
    (hsem : MuNegThreeOneTwoFiniteSemantics fwd c D X) :
    ∀ clause ∈ muNegThreeHitActivityClauses,
      dimacsClauseSatisfied (muNegThreeValOfRelations D X) clause := by
  intro clause hclause
  simp only [muNegThreeHitActivityClauses, List.mem_flatMap] at hclause
  obtain ⟨p, hp, hin⟩ := hclause
  have hplt := muNegThreeHitPairs_lt hp
  cases hx : muNegThreeXVar? p.1 p.2 with
  | none => rw [hx] at hin; simp at hin
  | some x =>
    rw [hx] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    have hxpos : 0 < x := by
      have := muNegThreeXVar?_bounds hx
      omega
    have hvalx : muNegThreeValOfRelations D X x = X p.1 p.2 := by
      have hv := muNegThreeValOfRelations_xvar D X hx
      simpa [Nat.min_eq_left (Nat.le_of_lt hplt.1),
        Nat.max_eq_right (Nat.le_of_lt hplt.1)] using hv
    by_cases hX : X p.1 p.2 = true
    · have hact := hsem.hit_active p.1 p.2 hp hX
      have guard (a : Nat) (ha : a < 64)
          (hactive : muNegThreeOwnerActive D a = true) :
          dimacsLitValue (muNegThreeValOfRelations D X)
            (-Int.ofNat (muNegThreeDVar a)) = true := by
        have hrow : muNegThreeCellRow a < 8 := by
          unfold muNegThreeCellRow
          omega
        have hcol : muNegThreeCellCol a < 8 := by
          unfold muNegThreeCellCol
          exact Nat.mod_lt _ (by norm_num)
        have hD : D (muNegThreeCellRow a) (muNegThreeCellCol a) = false := by
          simpa [muNegThreeOwnerActive] using hactive
        have haidx : muNegThreeCellRow a * 8 + muNegThreeCellCol a = a := by
          simpa [muNegThreeCellRow, muNegThreeCellCol, Nat.mul_comm] using
            Nat.div_add_mod a 8
        rw [muNegThree_dimacsLitValue_neg_ofNat (by simp [muNegThreeDVar]),
          ← haidx,
          muNegThreeValOfRelations_dvar D X hrow hcol, hD]
        rfl
      rcases hin with rfl | rfl
      · exact ⟨-Int.ofNat (muNegThreeDVar p.1), by simp,
          guard p.1 (by omega) hact.1⟩
      · exact ⟨-Int.ofNat (muNegThreeDVar p.2), by simp,
          guard p.2 hplt.2 hact.2⟩
    · have hXf : X p.1 p.2 = false := Bool.eq_false_of_not_eq_true hX
      have hneg : dimacsLitValue (muNegThreeValOfRelations D X)
          (-Int.ofNat x) = true := by
        rw [muNegThree_dimacsLitValue_neg_ofNat hxpos, hvalx, hXf]
        rfl
      rcases hin with rfl | rfl <;>
        exact ⟨-Int.ofNat x, by simp, hneg⟩

private theorem muNegThreeXLit?_eq_some {a b : Nat} {lit : Int}
    (h : muNegThreeXLit? a b = some lit) :
    ∃ x : Nat, muNegThreeXVar? a b = some x ∧ lit = Int.ofNat x := by
  unfold muNegThreeXLit? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

/-- A guarded exact-one block is satisfied when its positive guard is true,
or when exactly one of its positive service literals is true. -/
private theorem muNegThreeGuarded_satisfied {val : DimacsValuation}
    {g : Int} {lits : List Int} {clause : DimacsClause}
    (hcl : clause ∈ muNegThreeGuarded g lits)
    (hpos : ∀ lit ∈ lits, 0 < lit)
    (hdisj : dimacsLitValue val g = true ∨
      ((∃ lit ∈ lits, dimacsLitValue val lit = true) ∧
        (∀ l₁ ∈ lits, ∀ l₂ ∈ lits,
          dimacsLitValue val l₁ = true →
          dimacsLitValue val l₂ = true → l₁ = l₂))) :
    dimacsClauseSatisfied val clause := by
  rw [muNegThreeGuarded] at hcl
  rcases List.mem_append.mp hcl with hone | hpair
  · simp only [List.mem_singleton] at hone
    subst hone
    rcases hdisj with hg | ⟨⟨lit, hmem, hval⟩, _⟩
    · exact ⟨g, by simp, hg⟩
    · exact ⟨lit, by simp [hmem], hval⟩
  · simp only [List.mem_flatMap, List.mem_map, List.mem_filter] at hpair
    obtain ⟨x, hx, y, ⟨hy, hxy⟩, rfl⟩ := hpair
    rcases hdisj with hg | ⟨_, huniq⟩
    · exact ⟨g, by simp, hg⟩
    · by_cases hvx : dimacsLitValue val x = true
      · by_cases hvy : dimacsLitValue val y = true
        · have hxy' : x = y := huniq x hx y hy hvx hvy
          subst hxy'
          simp at hxy
        · have hvyf := Bool.eq_false_of_not_eq_true hvy
          exact ⟨-y, by simp, dimacs_neg_satisfied_of_false (hpos y hy) hvyf⟩
      · have hvxf := Bool.eq_false_of_not_eq_true hvx
        exact ⟨-x, by simp, dimacs_neg_satisfied_of_false (hpos x hx) hvxf⟩

/-- Embed the guarded service family from existence and uniqueness of an
active owner's service hit in every non-neighboring row and column. -/
theorem muNegThreeFiniteSemantics_service
    {fwd : Bool} {c : Nat} {D X : Nat → Nat → Bool}
    (hsem : MuNegThreeOneTwoFiniteSemantics fwd c D X) :
    ∀ clause ∈ muNegThreeServiceClauses,
      dimacsClauseSatisfied (muNegThreeValOfRelations D X) clause := by
  have block (a : Nat) (ha : a < 64) (onRow : Bool) (t : Nat)
      (ht : t < 8)
      (hoff : (if onRow then
          muNegThreeOffsetOne (muNegThreeCellRow a) t
        else muNegThreeOffsetOne (muNegThreeCellCol a) t) = false) :
      ∀ clause ∈ muNegThreeGuarded
          (Int.ofNat (muNegThreeDVar a))
          (muNegThreeServiceLits a onRow t),
        dimacsClauseSatisfied (muNegThreeValOfRelations D X) clause := by
    intro clause hcl
    apply muNegThreeGuarded_satisfied hcl
    · intro lit hlit
      rw [muNegThreeServiceLits, List.mem_filterMap] at hlit
      obtain ⟨b, _, hfb⟩ := hlit
      by_cases hcond : (b != a &&
          (if onRow then muNegThreeCellRow b == t
            else muNegThreeCellCol b == t)) = true
      · rw [if_pos hcond] at hfb
        obtain ⟨x, hx, rfl⟩ := muNegThreeXLit?_eq_some hfb
        have hb := muNegThreeXVar?_bounds hx
        show (0 : Int) < (x : Int)
        exact_mod_cast (by omega : 0 < x)
      · rw [if_neg hcond] at hfb
        simp at hfb
    · by_cases hact : muNegThreeOwnerActive D a = true
      · right
        constructor
        · obtain ⟨b, hb64, hbne, hcoord, hkey, hX⟩ :=
            hsem.service_exists a ha hact onRow t hoff
          have hsome := muNegThreeXVar?_isSome_of_mem hkey
          cases hx : muNegThreeXVar? a b with
          | none => rw [hx] at hsome; simp at hsome
          | some x =>
            refine ⟨Int.ofNat x, ?_, ?_⟩
            · rw [muNegThreeServiceLits, List.mem_filterMap]
              refine ⟨b, by simpa using hb64, ?_⟩
              rw [if_pos ((Bool.and_eq_true _ _).mpr
                ⟨bne_iff_ne.mpr hbne, by simpa using hcoord⟩)]
              unfold muNegThreeXLit?
              rw [hx]
              rfl
            · rw [muNegThree_dimacsLitValue_ofNat
                (by have := muNegThreeXVar?_bounds hx; omega),
                muNegThreeValOfRelations_xvar D X hx]
              exact hX
        · intro l₁ hl₁ l₂ hl₂ hv₁ hv₂
          rw [muNegThreeServiceLits, List.mem_filterMap] at hl₁ hl₂
          obtain ⟨b₁, hb₁r, hf₁⟩ := hl₁
          obtain ⟨b₂, hb₂r, hf₂⟩ := hl₂
          rw [List.mem_range] at hb₁r hb₂r
          by_cases hc₁ : (b₁ != a &&
              (if onRow then muNegThreeCellRow b₁ == t
                else muNegThreeCellCol b₁ == t)) = true
          · rw [if_pos hc₁] at hf₁
            by_cases hc₂ : (b₂ != a &&
                (if onRow then muNegThreeCellRow b₂ == t
                  else muNegThreeCellCol b₂ == t)) = true
            · rw [if_pos hc₂] at hf₂
              simp only [Bool.and_eq_true, bne_iff_ne] at hc₁ hc₂
              obtain ⟨x₁, hx₁, rfl⟩ := muNegThreeXLit?_eq_some hf₁
              obtain ⟨x₂, hx₂, rfl⟩ := muNegThreeXLit?_eq_some hf₂
              have hX₁ : X (min a b₁) (max a b₁) = true := by
                rw [muNegThree_dimacsLitValue_ofNat
                    (by have := muNegThreeXVar?_bounds hx₁; omega),
                  muNegThreeValOfRelations_xvar D X hx₁] at hv₁
                exact hv₁
              have hX₂ : X (min a b₂) (max a b₂) = true := by
                rw [muNegThree_dimacsLitValue_ofNat
                    (by have := muNegThreeXVar?_bounds hx₂; omega),
                  muNegThreeValOfRelations_xvar D X hx₂] at hv₂
                exact hv₂
              have hb₁₂ : b₁ = b₂ := hsem.service_unique a ha hact onRow t hoff
                b₁ b₂ hb₁r hc₁.1 (by simpa using hc₁.2)
                (muNegThreeXVar?_key_mem hx₁) hX₁
                hb₂r hc₂.1 (by simpa using hc₂.2)
                (muNegThreeXVar?_key_mem hx₂) hX₂
              subst hb₁₂
              rw [hx₁] at hx₂
              exact congrArg Int.ofNat (Option.some.inj hx₂)
            · rw [if_neg hc₂] at hf₂
              simp at hf₂
          · rw [if_neg hc₁] at hf₁
            simp at hf₁
      · left
        have hD : D (muNegThreeCellRow a) (muNegThreeCellCol a) = true := by
          have : muNegThreeOwnerActive D a = false := Bool.eq_false_of_not_eq_true hact
          simpa [muNegThreeOwnerActive] using this
        have hrow : muNegThreeCellRow a < 8 := by
          unfold muNegThreeCellRow
          omega
        have hcol : muNegThreeCellCol a < 8 := by
          exact Nat.mod_lt _ (by norm_num)
        have haidx : muNegThreeCellRow a * 8 + muNegThreeCellCol a = a := by
          simpa [muNegThreeCellRow, muNegThreeCellCol, Nat.mul_comm] using
            Nat.div_add_mod a 8
        rw [muNegThree_dimacsLitValue_ofNat (by simp [muNegThreeDVar]),
          ← haidx, muNegThreeValOfRelations_dvar D X hrow hcol, hD]
  intro clause hclause
  simp only [muNegThreeServiceClauses, List.mem_flatMap, List.mem_range,
    List.mem_append] at hclause
  obtain ⟨a, ha, hrow | hcol⟩ := hclause
  · obtain ⟨t, ht, hmem⟩ := hrow
    split at hmem
    · simp at hmem
    · exact block a ha true t ht (by simpa using ‹¬ muNegThreeOffsetOne
          (muNegThreeCellRow a) t = true›) clause hmem
  · obtain ⟨t, ht, hmem⟩ := hcol
    split at hmem
    · simp at hmem
    · exact block a ha false t ht (by simpa using ‹¬ muNegThreeOffsetOne
          (muNegThreeCellCol a) t = true›) clause hmem

end Erdos85

#print axioms Erdos85.muNegThreeValOfRelations_dvar
#print axioms Erdos85.muNegThreeValOfRelations_xvar
#print axioms Erdos85.muNegThreeXVar?_isSome_of_mem
#print axioms Erdos85.muNegThreeFiniteSemantics_fixed
#print axioms Erdos85.muNegThreeFiniteSemantics_opposite_rows
#print axioms Erdos85.muNegThreeFiniteSemantics_opposite_columns
#print axioms Erdos85.muNegThreeFiniteSemantics_intertwining
#print axioms Erdos85.muNegThreeFiniteSemantics_hit_activity
#print axioms Erdos85.muNegThreeFiniteSemantics_service

import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerCnf
import Proofs.Erdos85MuNegThreeZeroFiveCorrectAdmissibility
import Proofs.Erdos85MuNegThreeZeroFiveOwnerCnfSemantics
import Proofs.Erdos85MuNegOneOneFourFiniteSemantics

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

private theorem h305Correct_dimacsLitValue_neg_ofNat
    {val : DimacsValuation} {n : Nat} (hn : 0 < n) :
    dimacsLitValue val (-Int.ofNat n) = !val n := by
  have hp : (0 : Int) < Int.ofNat n := Int.natCast_pos.mpr hn
  rw [dimacsLitValue, if_neg (by omega), Int.natAbs_neg]
  simp

private theorem h305Correct_dimacsLitValue_ofNat
    {val : DimacsValuation} {n : Nat} (hn : 0 < n) :
    dimacsLitValue val (Int.ofNat n) = val n := by
  have hp : (0 : Int) < Int.ofNat n := Int.natCast_pos.mpr hn
  rw [dimacsLitValue, if_pos hp]
  simp

private theorem h305Correct_dimacsLitValue_neg_of_pos
    {val : DimacsValuation} {l : Int} (hl : 0 < l)
    (hv : ¬dimacsLitValue val l = true) :
    dimacsLitValue val (-l) = true := by
  simp only [dimacsLitValue, if_pos hl, Bool.not_eq_true] at hv
  rw [dimacsLitValue, if_neg (by omega), Int.natAbs_neg]
  simp [hv]

private theorem h305Correct_xlit_eq_some
    {pairs : List (Nat × Nat)} {a b : Nat} {lit : Int}
    (h : muNegThreeZeroFiveCorrectXLit? pairs a b = some lit) :
    ∃ x : Nat,
      muNegThreeZeroFiveCorrectXVar? pairs a b = some x ∧
      lit = Int.ofNat x := by
  unfold muNegThreeZeroFiveCorrectXLit? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

private theorem h305Correct_owner_get_eq (uTri vTri : Bool)
    {a : Nat} (ha : a < 88) :
    (muNegThreeZeroFiveCorrectOwners uTri vTri)[a]! =
      muNegThreeZeroFiveCorrectOwnerAt uTri vTri ⟨a, ha⟩ := by
  have hal : a < (muNegThreeZeroFiveCorrectOwners uTri vTri).length := by
    rw [muNegThreeZeroFiveCorrectOwners_length]
    exact ha
  unfold muNegThreeZeroFiveCorrectOwnerAt
  simpa only using
    (getElem!_pos (muNegThreeZeroFiveCorrectOwners uTri vTri) a hal)

/-- The corrected hit-activity clauses are satisfied by the induced
valuation whenever semantic hits use active owners. -/
theorem muNegThreeZeroFiveCorrectHitActivityClauses_satisfied
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hsem : MuNegThreeZeroFiveCorrectNonCrossSemantics
      uTri vTri sigma D X) :
    let os := muNegThreeZeroFiveCorrectOwners uTri vTri
    let pairs := muNegThreeZeroFiveCorrectHitPairs uTri vTri
    ∀ clause ∈ muNegThreeZeroFiveCorrectHitActivityClauses os pairs,
      dimacsClauseSatisfied
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) clause := by
  dsimp only
  intro clause hclause
  simp only [muNegThreeZeroFiveCorrectHitActivityClauses,
    List.mem_flatMap] at hclause
  obtain ⟨pr, hpr, hin⟩ := hclause
  have hprb := (mem_muNegThreeZeroFiveCorrectHitPairs_iff
    uTri vTri pr.1 pr.2).mp hpr
  cases hx : muNegThreeZeroFiveCorrectXVar?
      (muNegThreeZeroFiveCorrectHitPairs uTri vTri) pr.1 pr.2 with
  | none => rw [hx] at hin; simp at hin
  | some x =>
    rw [hx] at hin
    have hxpos : 0 < x := by
      have := muNegThreeZeroFiveCorrectXVar?_bounds hx
      omega
    have hvalx : muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X x =
        X pr.1 pr.2 := by
      have h := muNegThreeZeroFiveCorrectValOfRelations_xvar
        uTri vTri D X hx
      rwa [Nat.min_eq_left (Nat.le_of_lt hprb.2.2.1),
        Nat.max_eq_right (Nat.le_of_lt hprb.2.2.1)] at h
    by_cases hX : X pr.1 pr.2 = true
    · have hactive := hsem.hit_active pr.1 pr.2 hpr hX
      have hguard : ∀ o : Nat, o < 88 →
          muNegThreeZeroFiveCorrectOwnerActive uTri vTri D o = true →
          ∀ g : Nat,
            muNegThreeZeroFiveCorrectGuard?
              (muNegThreeZeroFiveCorrectOwners uTri vTri) o = some g →
            clause = [-Int.ofNat x, -Int.ofNat g] →
            dimacsClauseSatisfied
              (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X)
              clause := by
        intro o ho hact g hg hcl
        let p := (muNegThreeZeroFiveCorrectOwners uTri vTri)[o]!
        have hpBound := muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen
          uTri vTri ⟨o, ho⟩
        have hp2lt : p.2 < 16 := by
          change ((muNegThreeZeroFiveCorrectOwners uTri vTri)[o]!).2 < 16
          rw [h305Correct_owner_get_eq uTri vTri ho]
          exact hpBound.2
        have hgdata : p.1 < 8 ∧ 8 ≤ p.2 ∧
            g = muNegOneDVar p.1 (p.2 - 8) := by
          unfold muNegThreeZeroFiveCorrectGuard? at hg
          dsimp only at hg
          split at hg
          · next hcond =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            exact ⟨hcond.1, hcond.2,
              (Option.some.inj hg).symm⟩
          · exact absurd hg (by simp)
        have hDfalse : D p.1 (p.2 - 8) = false := by
          unfold muNegThreeZeroFiveCorrectOwnerActive at hact
          dsimp only at hact
          rw [hg] at hact
          change (!D p.1 (p.2 - 8)) = true at hact
          simpa using hact
        refine ⟨-Int.ofNat g, by rw [hcl]; simp, ?_⟩
        rw [h305Correct_dimacsLitValue_neg_ofNat (by
          rw [hgdata.2.2]; unfold muNegOneDVar; omega),
          hgdata.2.2,
          muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X
            hgdata.1 (by omega), hDfalse]
        rfl
      rcases List.mem_append.mp hin with hin1 | hin1
      · cases hg : muNegThreeZeroFiveCorrectGuard?
          (muNegThreeZeroFiveCorrectOwners uTri vTri) pr.1 with
        | none => rw [hg] at hin1; simp at hin1
        | some g =>
          rw [hg] at hin1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1
          exact hguard pr.1 hprb.1 hactive.1 g hg hin1
      · cases hg : muNegThreeZeroFiveCorrectGuard?
          (muNegThreeZeroFiveCorrectOwners uTri vTri) pr.2 with
        | none => rw [hg] at hin1; simp at hin1
        | some g =>
          rw [hg] at hin1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1
          exact hguard pr.2 hprb.2.1 hactive.2 g hg hin1
    · have hneg : dimacsLitValue
          (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X)
          (-Int.ofNat x) = true := by
        rw [h305Correct_dimacsLitValue_neg_ofNat hxpos, hvalx]
        simpa using hX
      have hhead : -Int.ofNat x ∈ clause := by
        rcases List.mem_append.mp hin with hin1 | hin1
        · cases hg : muNegThreeZeroFiveCorrectGuard?
            (muNegThreeZeroFiveCorrectOwners uTri vTri) pr.1 with
          | none => rw [hg] at hin1; simp at hin1
          | some g =>
            rw [hg] at hin1
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1
            rw [hin1]
            simp
        · cases hg : muNegThreeZeroFiveCorrectGuard?
            (muNegThreeZeroFiveCorrectOwners uTri vTri) pr.2 with
          | none => rw [hg] at hin1; simp at hin1
          | some g =>
            rw [hg] at hin1
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1
            rw [hin1]
            simp
      exact ⟨-Int.ofNat x, hhead, hneg⟩

private theorem h305Correct_service_shape_satisfied
    {val : DimacsValuation} {pre lits : List Int} {clause : DimacsClause}
    (hcl : clause ∈ ([pre ++ lits] ++ muNegOnePairsOf lits pre))
    (hpos : ∀ lit ∈ lits, 0 < lit) (hnodup : lits.Nodup)
    (hdisj : (∃ lit ∈ pre, dimacsLitValue val lit = true) ∨
      ((∃ lit ∈ lits, dimacsLitValue val lit = true) ∧
        (∀ l1 ∈ lits, ∀ l2 ∈ lits,
          dimacsLitValue val l1 = true →
          dimacsLitValue val l2 = true → l1 = l2))) :
    dimacsClauseSatisfied val clause := by
  rcases List.mem_append.mp hcl with hone | hpair
  · simp only [List.mem_singleton] at hone
    subst hone
    rcases hdisj with ⟨lit, hmem, hval⟩ | ⟨⟨lit, hmem, hval⟩, _⟩
    · exact ⟨lit, List.mem_append_left _ hmem, hval⟩
    · exact ⟨lit, List.mem_append_right _ hmem, hval⟩
  · simp only [muNegOnePairsOf, List.mem_flatMap, List.mem_range,
      List.mem_map, List.mem_filter] at hpair
    obtain ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩ := hpair
    have hij' : i < j := by simpa using hij
    rcases hdisj with ⟨lit, hmem, hval⟩ | ⟨_, huniq⟩
    · exact ⟨lit, List.mem_append_left _ hmem, hval⟩
    · have hgi : lits[i]! = lits[i] := getElem!_pos lits i hi
      have hgj : lits[j]! = lits[j] := getElem!_pos lits j hj
      by_cases hvi : dimacsLitValue val lits[i]! = true
      · by_cases hvj : dimacsLitValue val lits[j]! = true
        · exfalso
          have heq : lits[i]! = lits[j]! := by
            rw [hgi, hgj]
            exact huniq _ (by rw [← hgi]; rw [hgi]; exact List.getElem_mem _)
              _ (List.getElem_mem _) (by rwa [← hgi]) (by rwa [← hgj])
          rw [hgi, hgj] at heq
          exact absurd ((List.Nodup.getElem_inj_iff hnodup).mp heq)
            (by omega)
        · refine ⟨-lits[j]!, List.mem_append_right _ (by simp), ?_⟩
          exact h305Correct_dimacsLitValue_neg_of_pos
            (hpos _ (by rw [hgj]; exact List.getElem_mem _)) hvj
      · refine ⟨-lits[i]!, List.mem_append_right _ (by simp), ?_⟩
        exact h305Correct_dimacsLitValue_neg_of_pos
          (hpos _ (by rw [hgi]; exact List.getElem_mem _)) hvi

/-- The corrected exact-service clauses are satisfied by existence and
uniqueness of semantic service owners. -/
theorem muNegThreeZeroFiveCorrectServiceClauses_satisfied
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hsem : MuNegThreeZeroFiveCorrectNonCrossSemantics
      uTri vTri sigma D X) :
    let os := muNegThreeZeroFiveCorrectOwners uTri vTri
    let pairs := muNegThreeZeroFiveCorrectHitPairs uTri vTri
    ∀ clause ∈ muNegThreeZeroFiveCorrectServiceClauses os pairs,
      dimacsClauseSatisfied
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) clause := by
  dsimp only
  intro clause hclause
  simp only [muNegThreeZeroFiveCorrectServiceClauses,
    List.mem_flatMap, List.mem_range] at hclause
  obtain ⟨a, ha, w, hw, hcl⟩ := hclause
  rw [muNegThreeZeroFiveCorrectOwners_length] at ha
  refine h305Correct_service_shape_satisfied hcl ?_ ?_ ?_
  · intro lit hlit
    rw [List.mem_filterMap] at hlit
    obtain ⟨b, _, hfb⟩ := hlit
    split at hfb
    · obtain ⟨x, hx, rfl⟩ := h305Correct_xlit_eq_some hfb
      have := muNegThreeZeroFiveCorrectXVar?_bounds hx
      show (0 : Int) < (x : Int)
      exact_mod_cast by omega
    · exact absurd hfb (by simp)
  · refine List.Nodup.filterMap ?_ List.nodup_range
    intro b b' lit hb hb'
    simp only [Option.mem_def] at hb hb'
    split at hb
    · next hcond =>
      split at hb'
      · next hcond' =>
        simp only [Bool.and_eq_true, bne_iff_ne] at hcond hcond'
        obtain ⟨x, hx, rfl⟩ := h305Correct_xlit_eq_some hb
        obtain ⟨x', hx', hxx⟩ := h305Correct_xlit_eq_some hb'
        rw [Int.ofNat.inj hxx] at hx
        have hp := muNegThreeZeroFiveCorrectXVar?_inj hx hx'
        have h1 : min a b = min a b' := congrArg Prod.fst hp
        have h2 : max a b = max a b' := congrArg Prod.snd hp
        omega
      · exact absurd hb' (by simp)
    · exact absurd hb (by simp)
  · by_cases hact :
      muNegThreeZeroFiveCorrectOwnerActive uTri vTri D a = true
    · right
      constructor
      · obtain ⟨b, hb88, hbne, hpm, hkey, hX⟩ :=
          hsem.service_exists a ha hact w hw
        have hsome := muNegThreeZeroFiveCorrectXVar?_isSome_of_mem
          uTri vTri hkey
        cases hx : muNegThreeZeroFiveCorrectXVar?
            (muNegThreeZeroFiveCorrectHitPairs uTri vTri) a b with
        | none => rw [hx] at hsome; simp at hsome
        | some x =>
          refine ⟨Int.ofNat x, ?_, ?_⟩
          · rw [List.mem_filterMap]
            refine ⟨b, ?_, ?_⟩
            · rw [List.mem_range, muNegThreeZeroFiveCorrectOwners_length]
              exact hb88
            · rw [if_pos ((Bool.and_eq_true _ _).mpr
                ⟨bne_iff_ne.mpr hbne, hpm⟩)]
              unfold muNegThreeZeroFiveCorrectXLit?
              rw [hx]
              rfl
          · rw [h305Correct_dimacsLitValue_ofNat
              (by have := muNegThreeZeroFiveCorrectXVar?_bounds hx; omega),
              muNegThreeZeroFiveCorrectValOfRelations_xvar
                uTri vTri D X hx]
            exact hX
      · intro l1 h1 l2 h2 hv1 hv2
        rw [List.mem_filterMap] at h1 h2
        obtain ⟨b1, hb1r, hf1⟩ := h1
        obtain ⟨b2, hb2r, hf2⟩ := h2
        rw [List.mem_range, muNegThreeZeroFiveCorrectOwners_length] at hb1r hb2r
        split at hf1
        · next hcond1 =>
          split at hf2
          · next hcond2 =>
            simp only [Bool.and_eq_true, bne_iff_ne] at hcond1 hcond2
            obtain ⟨x1, hx1, rfl⟩ := h305Correct_xlit_eq_some hf1
            obtain ⟨x2, hx2, rfl⟩ := h305Correct_xlit_eq_some hf2
            have hX1 : X (min a b1) (max a b1) = true := by
              rw [h305Correct_dimacsLitValue_ofNat
                (by have := muNegThreeZeroFiveCorrectXVar?_bounds hx1; omega),
                muNegThreeZeroFiveCorrectValOfRelations_xvar
                  uTri vTri D X hx1] at hv1
              exact hv1
            have hX2 : X (min a b2) (max a b2) = true := by
              rw [h305Correct_dimacsLitValue_ofNat
                (by have := muNegThreeZeroFiveCorrectXVar?_bounds hx2; omega),
                muNegThreeZeroFiveCorrectValOfRelations_xvar
                  uTri vTri D X hx2] at hv2
              exact hv2
            have hb12 : b1 = b2 :=
              hsem.service_unique a ha hact w hw b1 b2
                hb1r hcond1.1 hcond1.2
                (muNegThreeZeroFiveCorrectXVar?_key_mem hx1) hX1
                hb2r hcond2.1 hcond2.2
                (muNegThreeZeroFiveCorrectXVar?_key_mem hx2) hX2
            subst hb12
            rw [hx1] at hx2
            rw [Option.some.inj hx2]
          · exact absurd hf2 (by simp)
        · exact absurd hf1 (by simp)
    · left
      cases hg : muNegThreeZeroFiveCorrectGuard?
          (muNegThreeZeroFiveCorrectOwners uTri vTri) a with
      | none =>
        exfalso
        apply hact
        unfold muNegThreeZeroFiveCorrectOwnerActive
        dsimp only
        rw [hg]
      | some g =>
        let p := (muNegThreeZeroFiveCorrectOwners uTri vTri)[a]!
        have hpBound := muNegThreeZeroFiveCorrectOwnerAt_lt_sixteen
          uTri vTri ⟨a, ha⟩
        have hp2lt : p.2 < 16 := by
          change ((muNegThreeZeroFiveCorrectOwners uTri vTri)[a]!).2 < 16
          rw [h305Correct_owner_get_eq uTri vTri ha]
          exact hpBound.2
        have hgdata : p.1 < 8 ∧ 8 ≤ p.2 ∧
            g = muNegOneDVar p.1 (p.2 - 8) := by
          unfold muNegThreeZeroFiveCorrectGuard? at hg
          dsimp only at hg
          split at hg
          · next hcond =>
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            exact ⟨hcond.1, hcond.2, (Option.some.inj hg).symm⟩
          · exact absurd hg (by simp)
        have hDtrue : D p.1 (p.2 - 8) = true := by
          unfold muNegThreeZeroFiveCorrectOwnerActive at hact
          dsimp only at hact
          rw [hg] at hact
          change ¬((!D p.1 (p.2 - 8)) = true) at hact
          simpa using hact
        refine ⟨Int.ofNat g, by simp, ?_⟩
        rw [h305Correct_dimacsLitValue_ofNat (by
          rw [hgdata.2.2]; unfold muNegOneDVar; omega),
          hgdata.2.2,
          muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X
            hgdata.1 (by omega), hDtrue]

private theorem h305Correct_xlit_props
    {uTri vTri : Bool} {D X : Nat → Nat → Bool}
    {o1 o2 : Nat} {lit : Int}
    (h : muNegThreeZeroFiveCorrectXLit?
      (muNegThreeZeroFiveCorrectHitPairs uTri vTri) o1 o2 = some lit) :
    0 < lit ∧
    dimacsLitValue
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) lit =
      X (min o1 o2) (max o1 o2) ∧
    (min o1 o2, max o1 o2) ∈
      muNegThreeZeroFiveCorrectHitPairs uTri vTri := by
  obtain ⟨x, hx, rfl⟩ := h305Correct_xlit_eq_some h
  have hb := muNegThreeZeroFiveCorrectXVar?_bounds hx
  refine ⟨by show (0 : Int) < (x : Int); exact_mod_cast by omega, ?_,
    muNegThreeZeroFiveCorrectXVar?_key_mem hx⟩
  rw [h305Correct_dimacsLitValue_ofNat (by omega),
    muNegThreeZeroFiveCorrectValOfRelations_xvar uTri vTri D X hx]

private theorem h305Correct_option_bind_inv {alpha beta : Type}
    {o : Option alpha} {f : alpha → Option beta} {c : beta}
    (h : (o >>= f) = some c) : ∃ x, o = some x ∧ f x = some c := by
  cases o with
  | none => simp at h
  | some x => exact ⟨x, rfl, h⟩

/-- Both corrected owner-C4 clause families are satisfied by the semantic
intersecting and disjoint C4 laws. -/
theorem muNegThreeZeroFiveCorrectC4Clauses_satisfied
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hsem : MuNegThreeZeroFiveCorrectNonCrossSemantics
      uTri vTri sigma D X) :
    let os := muNegThreeZeroFiveCorrectOwners uTri vTri
    let pairs := muNegThreeZeroFiveCorrectHitPairs uTri vTri
    ∀ clause ∈ muNegThreeZeroFiveCorrectC4Clauses os pairs,
      dimacsClauseSatisfied
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) clause := by
  dsimp only
  intro clause hclause
  simp only [muNegThreeZeroFiveCorrectC4Clauses, List.mem_flatMap,
    List.mem_range, List.mem_filter] at hclause
  obtain ⟨a, ha, b, ⟨hb, hab⟩, hcl⟩ := hclause
  rw [muNegThreeZeroFiveCorrectOwners_length] at ha hb
  have hab' : a < b := of_decide_eq_true hab
  split at hcl
  · next hshare =>
    rw [List.mem_filterMap] at hcl
    obtain ⟨g, hgmem, hf⟩ := hcl
    rw [List.mem_filter, List.mem_range,
      muNegThreeZeroFiveCorrectOwners_length] at hgmem
    obtain ⟨hg88, hgcond⟩ := hgmem
    simp only [Bool.and_eq_true, bne_iff_ne] at hgcond
    obtain ⟨⟨⟨hga, hgb⟩, _⟩, _⟩ := hgcond
    obtain ⟨x, hxeq, hf⟩ := h305Correct_option_bind_inv hf
    obtain ⟨y, hyeq, hf⟩ := h305Correct_option_bind_inv hf
    have hcl' : clause = [-x, -y] := (Option.some.inj hf).symm
    obtain ⟨hxpos, hxval, hxkey⟩ :=
      h305Correct_xlit_props (D := D) (X := X) hxeq
    obtain ⟨hypos, hyval, hykey⟩ :=
      h305Correct_xlit_props (D := D) (X := X) hyeq
    by_cases hvx : dimacsLitValue
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) x = true
    · by_cases hvy : dimacsLitValue
          (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) y = true
      · exact absurd (hsem.c4_intersecting a b g hab' hb hg88 hga hgb
          hshare hxkey hykey (by rw [← hxval]; exact hvx)
          (by rw [← hyval]; exact hvy)) not_false
      · exact ⟨-y, by rw [hcl']; simp,
          h305Correct_dimacsLitValue_neg_of_pos hypos hvy⟩
    · exact ⟨-x, by rw [hcl']; simp,
        h305Correct_dimacsLitValue_neg_of_pos hxpos hvx⟩
  · next hnshare =>
    have hshare_f : muNegOneShare
        ((muNegThreeZeroFiveCorrectOwners uTri vTri)[a]!)
        ((muNegThreeZeroFiveCorrectOwners uTri vTri)[b]!) = false :=
      Bool.eq_false_iff.mpr hnshare
    set ks :=
      (List.range (muNegThreeZeroFiveCorrectOwners uTri vTri).length).filter
        (fun g => g != a && g != b &&
          (muNegThreeZeroFiveCorrectXVar?
            (muNegThreeZeroFiveCorrectHitPairs uTri vTri) a g).isSome &&
          (muNegThreeZeroFiveCorrectXVar?
            (muNegThreeZeroFiveCorrectHitPairs uTri vTri) b g).isSome)
      with hks
    rw [List.mem_flatMap] at hcl
    obtain ⟨gi, hgi, hcl⟩ := hcl
    rw [List.mem_range] at hgi
    rw [List.mem_filterMap] at hcl
    obtain ⟨hi, hhim, hf⟩ := hcl
    rw [List.mem_filter, List.mem_range] at hhim
    obtain ⟨hhi, hgihi⟩ := hhim
    have hgihi' : gi < hi := of_decide_eq_true hgihi
    obtain ⟨xag, hxag, hf⟩ := h305Correct_option_bind_inv hf
    obtain ⟨xbg, hxbg, hf⟩ := h305Correct_option_bind_inv hf
    obtain ⟨xah, hxah, hf⟩ := h305Correct_option_bind_inv hf
    obtain ⟨xbh, hxbh, hf⟩ := h305Correct_option_bind_inv hf
    have hcl' : clause = [-xag, -xbg, -xah, -xbh] :=
      (Option.some.inj hf).symm
    have hgmem : ks[gi]! ∈ ks := by
      rw [getElem!_pos ks gi hgi]
      exact List.getElem_mem _
    have hhmem : ks[hi]! ∈ ks := by
      rw [getElem!_pos ks hi hhi]
      exact List.getElem_mem _
    have hgmemf : ks[gi]! ∈
        (List.range
          (muNegThreeZeroFiveCorrectOwners uTri vTri).length).filter
          (fun g => g != a && g != b &&
            (muNegThreeZeroFiveCorrectXVar?
              (muNegThreeZeroFiveCorrectHitPairs uTri vTri) a g).isSome &&
            (muNegThreeZeroFiveCorrectXVar?
              (muNegThreeZeroFiveCorrectHitPairs uTri vTri) b g).isSome) := by
      rw [← hks]
      exact hgmem
    have hhmemf : ks[hi]! ∈
        (List.range
          (muNegThreeZeroFiveCorrectOwners uTri vTri).length).filter
          (fun g => g != a && g != b &&
            (muNegThreeZeroFiveCorrectXVar?
              (muNegThreeZeroFiveCorrectHitPairs uTri vTri) a g).isSome &&
            (muNegThreeZeroFiveCorrectXVar?
              (muNegThreeZeroFiveCorrectHitPairs uTri vTri) b g).isSome) := by
      rw [← hks]
      exact hhmem
    have hksnd : ks.Nodup := by
      rw [hks]
      exact List.nodup_range.filter _
    have hgh : ks[gi]! ≠ ks[hi]! := by
      rw [getElem!_pos ks gi hgi, getElem!_pos ks hi hhi]
      exact fun h =>
        absurd ((List.Nodup.getElem_inj_iff hksnd).mp h) (by omega)
    obtain ⟨hgr, hgcond⟩ := List.mem_filter.mp hgmemf
    obtain ⟨hhr, hhcond⟩ := List.mem_filter.mp hhmemf
    rw [List.mem_range, muNegThreeZeroFiveCorrectOwners_length] at hgr hhr
    simp only [Bool.and_eq_true, bne_iff_ne] at hgcond hhcond
    obtain ⟨⟨⟨hga, hgb⟩, _⟩, _⟩ := hgcond
    obtain ⟨⟨⟨hha, hhb⟩, _⟩, _⟩ := hhcond
    obtain ⟨hp1, hv1, hk1⟩ :=
      h305Correct_xlit_props (D := D) (X := X) hxag
    obtain ⟨hp2, hv2, hk2⟩ :=
      h305Correct_xlit_props (D := D) (X := X) hxbg
    obtain ⟨hp3, hv3, hk3⟩ :=
      h305Correct_xlit_props (D := D) (X := X) hxah
    obtain ⟨hp4, hv4, hk4⟩ :=
      h305Correct_xlit_props (D := D) (X := X) hxbh
    by_cases hb1 : dimacsLitValue
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) xag = true
    · by_cases hb2 : dimacsLitValue
          (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) xbg = true
      · by_cases hb3 : dimacsLitValue
            (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) xah = true
        · by_cases hb4 : dimacsLitValue
              (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) xbh = true
          · exact absurd (hsem.c4_no_two a b ks[gi]! ks[hi]! hab' hb
              hgr hhr hgh hga hgb hha hhb hshare_f hk1 hk2 hk3 hk4
              (by rw [← hv1]; exact hb1) (by rw [← hv2]; exact hb2)
              (by rw [← hv3]; exact hb3) (by rw [← hv4]; exact hb4))
              not_false
          · exact ⟨-xbh, by rw [hcl']; simp,
              h305Correct_dimacsLitValue_neg_of_pos hp4 hb4⟩
        · exact ⟨-xah, by rw [hcl']; simp,
            h305Correct_dimacsLitValue_neg_of_pos hp3 hb3⟩
      · exact ⟨-xbg, by rw [hcl']; simp,
          h305Correct_dimacsLitValue_neg_of_pos hp2 hb2⟩
    · exact ⟨-xag, by rw [hcl']; simp,
        h305Correct_dimacsLitValue_neg_of_pos hp1 hb1⟩

private theorem h305Correct_exactlyTwo_of_countP
    {uTri vTri : Bool} {D X : Nat → Nat → Bool}
    (Dv : Nat → Bool) (f : Nat → Nat)
    (hf : ∀ x y, f x = f y → x = y) (hfpos : ∀ j, 0 < f j)
    (js : List Nat) (hnd : js.Nodup)
    (hval : ∀ j ∈ js,
      muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X (f j) = Dv j)
    (hcount : (js.countP fun j => Dv j) = 2) :
    MuNegOneExactlyTwoSemantics
      (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X)
      (js.map fun j => Int.ofNat (f j)) := by
  apply muNegOneExactlyTwoSemantics_of_two
  · exact hnd.map fun x y h => hf x y (Int.ofNat.inj h)
  · intro lit hlit
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hlit
    exact Int.natCast_pos.mpr (hfpos j)
  · rw [List.countP_map, ← hcount]
    apply List.countP_congr
    intro j hj
    simp only [Function.comp_apply]
    have hp : 0 < Int.ofNat (f j) := Int.natCast_pos.mpr (hfpos j)
    simp only [dimacsLitValue, if_pos hp]
    change muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X (f j) =
      true ↔ Dv j = true
    rw [hval j hj]

set_option maxHeartbeats 0 in
private theorem h305Correct_exactlyThree_of_countP
    {uTri vTri : Bool} {D X : Nat → Nat → Bool}
    (Dv : Nat → Bool) (f : Nat → Nat) (hfpos : ∀ j, 0 < f j)
    (js : List Nat) (hlen : js.length = 4)
    (hval : ∀ j ∈ js,
      muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X (f j) = Dv j)
    (hcount : (js.countP fun j => Dv j) = 3) :
    MuNegThreeExactlyThreeSemantics
      (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X)
      (js.map fun j => Int.ofNat (f j)) := by
  have hsemantic : ∀ {val : DimacsValuation} {lits : List Int},
      lits.length = 4 →
      (∀ lit ∈ lits, 0 < lit) →
      (lits.countP fun lit => dimacsLitValue val lit) = 3 →
      MuNegThreeExactlyThreeSemantics val lits := by
    intro val lits hlen' hpos' hcount'
    obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hlen'
    have ha : 0 < a := hpos' a (by simp)
    have hb : 0 < b := hpos' b (by simp)
    have hc : 0 < c := hpos' c (by simp)
    have hd : 0 < d := hpos' d (by simp)
    constructor
    intro clause hclause
    norm_num [muNegThreeExactlyThree] at hclause
    rcases hclause with hpairs | hneg
    · obtain ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩ := hpairs
      interval_cases i <;> interval_cases j <;> norm_num at hij ⊢ <;>
        simp only [List.countP_cons, List.countP_nil] at hcount' <;>
        simp only [dimacsClauseSatisfied, List.mem_cons, List.mem_singleton] <;>
        by_cases hva : dimacsLitValue val a = true <;>
        by_cases hvb : dimacsLitValue val b = true <;>
        by_cases hvc : dimacsLitValue val c = true <;>
        by_cases hvd : dimacsLitValue val d = true <;>
        simp_all [dimacsLitValue, ha, hb, hc, hd] <;> omega
    · subst clause
      simp only [List.countP_cons, List.countP_nil] at hcount'
      simp only [dimacsClauseSatisfied, List.mem_cons, List.mem_singleton]
      by_cases hva : dimacsLitValue val a = true <;>
      by_cases hvb : dimacsLitValue val b = true <;>
      by_cases hvc : dimacsLitValue val c = true <;>
      by_cases hvd : dimacsLitValue val d = true <;>
      simp_all [dimacsLitValue, ha, hb, hc, hd] <;> omega
  apply hsemantic
  · simpa using hlen
  · intro lit hlit
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hlit
    exact Int.natCast_pos.mpr (hfpos j)
  · rw [List.countP_map, ← hcount]
    apply List.countP_congr
    intro j hj
    simp only [Function.comp_apply]
    have hp : 0 < Int.ofNat (f j) := Int.natCast_pos.mpr (hfpos j)
    simp only [dimacsLitValue, if_pos hp]
    change muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X (f j) =
      true ↔ Dv j = true
    rw [hval j hj]

private theorem h305Correct_same_filter_length_four
    (sigma : Bool) (i : Nat) (hi : i < 8) :
    ((List.range 8).filter fun j =>
      muNegOneSign sigma i == muNegOneSign sigma (8 + j)).length = 4 := by
  interval_cases i <;> cases sigma <;> decide

private theorem h305Correct_opp_filter_length_four
    (sigma : Bool) (i : Nat) (hi : i < 8) :
    ((List.range 8).filter fun j =>
      !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).length = 4 := by
  interval_cases i <;> cases sigma <;> decide

private theorem h305Correct_opp_col_filter_length_four
    (sigma : Bool) (j : Nat) (hj : j < 8) :
    ((List.range 8).filter fun i =>
      !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).length = 4 := by
  interval_cases j <;> cases sigma <;> decide

theorem muNegThreeZeroFiveCorrectCrossRowClauses_satisfied
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hsame : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).countP
          fun j => D i j) = 2)
    (hopp : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun j => D i j) = 3) :
    ∀ clause ∈ muNegThreeZeroFiveCrossRowClauses sigma,
      dimacsClauseSatisfied
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) clause := by
  apply muNegThreeZeroFiveCrossRowClauses_satisfied
  · intro i hi
    refine h305Correct_exactlyTwo_of_countP (Dv := fun j => D i j)
      (fun j => muNegOneDVar i j) (fun x y h => ?_) (fun j => ?_)
      _ (List.nodup_range.filter _) (fun j hj => ?_) (hsame i hi)
    · unfold muNegOneDVar at h; omega
    · unfold muNegOneDVar; omega
    · exact muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X hi
        (List.mem_range.mp (List.mem_of_mem_filter hj))
  · intro i hi
    refine h305Correct_exactlyThree_of_countP (Dv := fun j => D i j)
      (fun j => muNegOneDVar i j) (fun j => ?_) _
      (h305Correct_opp_filter_length_four sigma i hi) (fun j hj => ?_)
      (hopp i hi)
    · unfold muNegOneDVar; omega
    · exact muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X hi
        (List.mem_range.mp (List.mem_of_mem_filter hj))

theorem muNegThreeZeroFiveCorrectCrossColClauses_satisfied
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hsame : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).countP
          fun i => D i j) = 2)
    (hopp : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun i => D i j) = 3) :
    ∀ clause ∈ muNegThreeZeroFiveCrossColClauses sigma,
      dimacsClauseSatisfied
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) clause := by
  apply muNegThreeZeroFiveCrossColClauses_satisfied
  · intro j hj
    refine h305Correct_exactlyTwo_of_countP (Dv := fun i => D i j)
      (fun i => muNegOneDVar i j) (fun x y h => ?_) (fun i => ?_)
      _ (List.nodup_range.filter _) (fun i hi => ?_) (hsame j hj)
    · unfold muNegOneDVar at h; omega
    · unfold muNegOneDVar; omega
    · exact muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X
        (List.mem_range.mp (List.mem_of_mem_filter hi)) hj
  · intro j hj
    refine h305Correct_exactlyThree_of_countP (Dv := fun i => D i j)
      (fun i => muNegOneDVar i j) (fun i => ?_) _
      (h305Correct_opp_col_filter_length_four sigma j hj) (fun i hi => ?_)
      (hopp j hj)
    · unfold muNegOneDVar; omega
    · exact muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X
        (List.mem_range.mp (List.mem_of_mem_filter hi)) hj

theorem muNegThreeZeroFiveCorrectIntertwineClauses_satisfied
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hsem : MuNegThreeZeroFiveCorrectNonCrossSemantics
      uTri vTri sigma D X) :
    ∀ clause ∈ muNegOneIntertwineClauses,
      dimacsClauseSatisfied
        (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X) clause := by
  apply muNegOneIntertwineClauses_satisfied
  intro i j hi hj
  have h7 : (i + 7) % 8 < 8 := Nat.mod_lt _ (by omega)
  have h1 : (i + 1) % 8 < 8 := Nat.mod_lt _ (by omega)
  have hj1 : (j + 1) % 8 < 8 := Nat.mod_lt _ (by omega)
  have hj7 : (j + 7) % 8 < 8 := Nat.mod_lt _ (by omega)
  apply muNegOneSumEq_satisfied
  · unfold muNegOneDVar; omega
  · unfold muNegOneDVar; omega
  · unfold muNegOneDVar; omega
  · unfold muNegOneDVar; omega
  · rw [muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X h7 hj,
      muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X h1 hj,
      muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X hi hj1,
      muNegThreeZeroFiveCorrectValOfRelations_dvar uTri vTri D X hi hj7]
    exact hsem.intertwine i j hi hj

theorem muNegThreeZeroFiveCorrectOwnerDimacsClauses_satisfied
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hrowSame : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).countP
          fun j => D i j) = 2)
    (hrowOpp : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun j => D i j) = 3)
    (hcolSame : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).countP
          fun i => D i j) = 2)
    (hcolOpp : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun i => D i j) = 3)
    (hsem : MuNegThreeZeroFiveCorrectNonCrossSemantics
      uTri vTri sigma D X) :
    dimacsFormulaSatisfied
      (muNegThreeZeroFiveCorrectValOfRelations uTri vTri D X)
      (muNegThreeZeroFiveCorrectOwnerDimacsClauses uTri vTri sigma) := by
  intro clause hclause
  simp only [muNegThreeZeroFiveCorrectOwnerDimacsClauses,
    List.mem_toArray] at hclause
  rcases List.mem_append.mp hclause with hclause | hclause
  · rcases List.mem_append.mp hclause with hclause | hclause
    · rcases List.mem_append.mp hclause with hclause | hclause
      · rcases List.mem_append.mp hclause with hclause | hclause
        · rcases List.mem_append.mp hclause with hrows | hcols
          · exact muNegThreeZeroFiveCorrectCrossRowClauses_satisfied
              hrowSame hrowOpp clause hrows
          · exact muNegThreeZeroFiveCorrectCrossColClauses_satisfied
              hcolSame hcolOpp clause hcols
        · exact muNegThreeZeroFiveCorrectIntertwineClauses_satisfied
            hsem clause hclause
      · exact muNegThreeZeroFiveCorrectHitActivityClauses_satisfied
          hsem clause hclause
    · exact muNegThreeZeroFiveCorrectServiceClauses_satisfied
        hsem clause hclause
  · exact muNegThreeZeroFiveCorrectC4Clauses_satisfied hsem clause hclause

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectValOfRelations_dvar
#print axioms Erdos85.muNegThreeZeroFiveCorrectValOfRelations_xvar
#print axioms Erdos85.muNegThreeZeroFiveCorrectHitActivityClauses_satisfied
#print axioms Erdos85.muNegThreeZeroFiveCorrectServiceClauses_satisfied
#print axioms Erdos85.muNegThreeZeroFiveCorrectC4Clauses_satisfied
#print axioms Erdos85.muNegThreeZeroFiveCorrectOwnerDimacsClauses_satisfied

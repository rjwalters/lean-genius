import Proofs.Erdos85MuNegThreeZeroFiveCorrectOwnerCnf
import Proofs.Erdos85MuNegThreeZeroFiveCorrectAdmissibility

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

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveCorrectValOfRelations_dvar
#print axioms Erdos85.muNegThreeZeroFiveCorrectValOfRelations_xvar
#print axioms Erdos85.muNegThreeZeroFiveCorrectHitActivityClauses_satisfied

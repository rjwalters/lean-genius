import Proofs.Erdos85MuNegThreeZeroFiveCrossSemantics

/-! # Reused non-cross finite semantics for h305 -/

namespace Erdos85

open Std Sat

structure MuNegThreeZeroFiveNonCrossSemantics
    (uTri vTri sigma : Bool) (D X : Nat → Nat → Bool) : Prop where
  intertwine : ∀ i j, i < 8 → j < 8 →
    (cond (D ((i + 7) % 8) j) 1 0) + (cond (D ((i + 1) % 8) j) 1 0) =
      (cond (D i ((j + 1) % 8)) 1 0) + (cond (D i ((j + 7) % 8)) 1 0)
  hit_active : ∀ a b, (a, b) ∈ muNegOneHitPairs uTri vTri → X a b = true →
    muNegOneOwnerActive D a = true ∧ muNegOneOwnerActive D b = true
  service_exists : ∀ a, a < 80 → muNegOneOwnerActive D a = true →
    ∀ w ∈ muNegOneTwelve ((muNegOneOwners uTri vTri)[a]!),
      ∃ b, b < 80 ∧ b ≠ a ∧
        muNegOnePairMem ((muNegOneOwners uTri vTri)[b]!) w = true ∧
        (min a b, max a b) ∈ muNegOneHitPairs uTri vTri ∧
        X (min a b) (max a b) = true
  service_unique : ∀ a, a < 80 → muNegOneOwnerActive D a = true →
    ∀ w ∈ muNegOneTwelve ((muNegOneOwners uTri vTri)[a]!),
      ∀ b c, b < 80 → b ≠ a →
        muNegOnePairMem ((muNegOneOwners uTri vTri)[b]!) w = true →
        (min a b, max a b) ∈ muNegOneHitPairs uTri vTri →
        X (min a b) (max a b) = true → c < 80 → c ≠ a →
        muNegOnePairMem ((muNegOneOwners uTri vTri)[c]!) w = true →
        (min a c, max a c) ∈ muNegOneHitPairs uTri vTri →
        X (min a c) (max a c) = true → b = c
  c4_intersecting : ∀ a b g, a < b → b < 80 → g < 80 → g ≠ a → g ≠ b →
    muNegOneShare ((muNegOneOwners uTri vTri)[a]!)
      ((muNegOneOwners uTri vTri)[b]!) = true →
    (min a g, max a g) ∈ muNegOneHitPairs uTri vTri →
    (min b g, max b g) ∈ muNegOneHitPairs uTri vTri →
    X (min a g) (max a g) = true → X (min b g) (max b g) = true → False
  c4_no_two : ∀ a b g h, a < b → b < 80 → g < 80 → h < 80 → g ≠ h →
    g ≠ a → g ≠ b → h ≠ a → h ≠ b →
    muNegOneShare ((muNegOneOwners uTri vTri)[a]!)
      ((muNegOneOwners uTri vTri)[b]!) = false →
    (min a g, max a g) ∈ muNegOneHitPairs uTri vTri →
    (min b g, max b g) ∈ muNegOneHitPairs uTri vTri →
    (min a h, max a h) ∈ muNegOneHitPairs uTri vTri →
    (min b h, max b h) ∈ muNegOneHitPairs uTri vTri →
    X (min a g) (max a g) = true → X (min b g) (max b g) = true →
    X (min a h) (max a h) = true → X (min b h) (max b h) = true → False

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

private theorem h305_dimacsLitValue_neg_of_pos {val : DimacsValuation} {l : Int}
    (hl : 0 < l) (hv : ¬ dimacsLitValue val l = true) :
    dimacsLitValue val (-l) = true := by
  simp only [dimacsLitValue, if_pos hl, Bool.not_eq_true] at hv
  rw [dimacsLitValue, if_neg (by omega), Int.natAbs_neg]
  simp [hv]

private theorem h305_dimacsLitValue_ofNat {val : DimacsValuation} {n : Nat}
    (hn : 0 < n) : dimacsLitValue val (Int.ofNat n) = val n := by
  have h : (0 : Int) < Int.ofNat n := by
    show (0 : Int) < (n : Int)
    exact_mod_cast hn
  rw [dimacsLitValue, if_pos h]
  simp

private theorem h305_dimacsLitValue_neg_ofNat {val : DimacsValuation} {n : Nat}
    (hn : 0 < n) : dimacsLitValue val (-Int.ofNat n) = !val n := by
  have h : (0 : Int) < Int.ofNat n := by
    show (0 : Int) < (n : Int)
    exact_mod_cast hn
  rw [dimacsLitValue, if_neg (by omega), Int.natAbs_neg]
  simp

theorem muNegThreeZeroFiveIntertwineClauses_satisfied_of_nonCross
    (hsem : MuNegThreeZeroFiveNonCrossSemantics uTri vTri σ D X) :
    ∀ clause ∈ muNegOneIntertwineClauses,
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X)
        clause := by
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
  · rw [muNegOneValOfRelations_dvar uTri vTri D X h7 hj,
      muNegOneValOfRelations_dvar uTri vTri D X h1 hj,
      muNegOneValOfRelations_dvar uTri vTri D X hi hj1,
      muNegOneValOfRelations_dvar uTri vTri D X hi hj7]
    exact hsem.intertwine i j hi hj
private theorem h305_eq_of_minmax {a b b' : Nat} (_hb : b ≠ a) (_hb' : b' ≠ a)
    (h : (min a b, max a b) = (min a b', max a b')) : b = b' := by
  have h1 : min a b = min a b' := congrArg Prod.fst h
  have h2 : max a b = max a b' := congrArg Prod.snd h
  omega

/-- The valuation of a generated hit variable, normalized-pair form. -/
private theorem h305_valOfRelations_xvar {uTri vTri : Bool}
    {D X : Nat → Nat → Bool} {a b x : Nat}
    (h : muNegOneXVar? (muNegOneHitPairs uTri vTri) a b = some x) :
    muNegOneValOfRelations uTri vTri D X x = X (min a b) (max a b) :=
  muNegOneValOfRelations_xvar uTri vTri D X h
section HitFamilies

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

/-- Hit-activity family of the induced valuation. -/
theorem muNegThreeZeroFiveHitActivityClauses_satisfied_of_nonCross
    (hsem : MuNegThreeZeroFiveNonCrossSemantics uTri vTri σ D X) :
    ∀ clause ∈ muNegOneHitActivityClauses uTri vTri
      (muNegOneHitPairs uTri vTri),
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X)
        clause := by
  intro clause hclause
  simp only [muNegOneHitActivityClauses, List.mem_flatMap] at hclause
  obtain ⟨pr, hpr, hin⟩ := hclause
  obtain ⟨hlt, hlt80⟩ := muNegOneHitPairs_lt hpr
  cases hx : muNegOneXVar? (muNegOneHitPairs uTri vTri) pr.1 pr.2 with
  | none => rw [hx] at hin; simp at hin
  | some x =>
  rw [hx] at hin
  have hxpos : (0 : Int) < Int.ofNat x := by
    have := muNegOneXVar?_bounds hx
    show (0 : Int) < (x : Int)
    exact_mod_cast by omega
  have hvalx : muNegOneValOfRelations uTri vTri D X x = X pr.1 pr.2 := by
    have h := h305_valOfRelations_xvar (D := D) (X := X) hx
    rwa [Nat.min_eq_left (Nat.le_of_lt hlt),
      Nat.max_eq_right (Nat.le_of_lt hlt)] at h
  by_cases hXv : X pr.1 pr.2 = true
  · -- both endpoints are active; the guarded defect literal is false.
    have hact := hsem.hit_active pr.1 pr.2 (by simpa using hpr) hXv
    have hguard : ∀ o : Nat, o < 80 →
        muNegOneOwnerActive D o = true →
        ∀ g : Nat, muNegOneGuard? uTri vTri o = some g →
        clause = [-Int.ofNat x, -Int.ofNat g] →
          dimacsClauseSatisfied
            (muNegOneValOfRelations uTri vTri D X) clause := by
      intro o ho hoact g hg hcl
      have h16' : 16 ≤ o := by
        by_contra h16
        rw [muNegOneGuard?, if_pos (by omega)] at hg
        exact absurd hg (by simp)
      have hgeq : g = muNegOneDVar ((muNegOneOwners uTri vTri)[o]!).1
          (((muNegOneOwners uTri vTri)[o]!).2 - 8) := by
        rw [muNegOneGuard?, if_neg (by omega)] at hg
        exact (Option.some.inj hg).symm
      have howner : (muNegOneOwners uTri vTri)[o]! =
          ((o - 16) / 8, 8 + (o - 16) % 8) :=
        muNegOneOwnerAt_cross uTri vTri ⟨o, ho⟩ h16'
      have hgeq' : g = muNegOneDVar ((o - 16) / 8) ((o - 16) % 8) := by
        rw [hgeq, howner]
        simp
      have hDfalse : D ((o - 16) / 8) ((o - 16) % 8) = false := by
        have h := hoact
        unfold muNegOneOwnerActive at h
        rw [if_neg (by omega)] at h
        simpa using h
      refine ⟨-Int.ofNat g, by rw [hcl]; simp, ?_⟩
      rw [h305_dimacsLitValue_neg_ofNat (by rw [hgeq']; unfold muNegOneDVar; omega),
        hgeq', muNegOneValOfRelations_dvar uTri vTri D X
          (i := (o - 16) / 8) (j := (o - 16) % 8) (by omega) (by omega),
        hDfalse]
      rfl
    rcases List.mem_append.mp hin with hin1 | hin1
    · cases hg : muNegOneGuard? uTri vTri pr.1 with
      | none => rw [hg] at hin1; simp at hin1
      | some g =>
        rw [hg] at hin1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1
        exact hguard pr.1 (by omega) hact.1 g hg hin1
    · cases hg : muNegOneGuard? uTri vTri pr.2 with
      | none => rw [hg] at hin1; simp at hin1
      | some g =>
        rw [hg] at hin1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1
        exact hguard pr.2 hlt80 hact.2 g hg hin1
  · -- the hit variable itself is false.
    have hneg : dimacsLitValue (muNegOneValOfRelations uTri vTri D X)
        (-Int.ofNat x) = true := by
      rw [h305_dimacsLitValue_neg_ofNat (by
        have := muNegOneXVar?_bounds hx; omega)]
      rw [hvalx]
      simpa using hXv
    have hhead : -Int.ofNat x ∈ clause := by
      rcases List.mem_append.mp hin with hin1 | hin1
      · cases hg : muNegOneGuard? uTri vTri pr.1 with
        | none => rw [hg] at hin1; simp at hin1
        | some g =>
          rw [hg] at hin1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1
          rw [hin1]
          simp
      · cases hg : muNegOneGuard? uTri vTri pr.2 with
        | none => rw [hg] at hin1; simp at hin1
        | some g =>
          rw [hg] at hin1
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hin1
          rw [hin1]
          simp
    exact ⟨-Int.ofNat x, hhead, hneg⟩

end HitFamilies
private theorem h305_service_shape_satisfied {val : DimacsValuation}
    {pre lits : List Int} {clause : DimacsClause}
    (hcl : clause ∈ ([pre ++ lits] ++ muNegOnePairsOf lits pre))
    (hpos : ∀ lit ∈ lits, 0 < lit)
    (hnodup : lits.Nodup)
    (hdisj : (∃ lit ∈ pre, dimacsLitValue val lit = true) ∨
      ((∃ lit ∈ lits, dimacsLitValue val lit = true) ∧
        (∀ l1 ∈ lits, ∀ l2 ∈ lits, dimacsLitValue val l1 = true →
          dimacsLitValue val l2 = true → l1 = l2))) :
    dimacsClauseSatisfied val clause := by
  rcases List.mem_append.mp hcl with hone | hpair
  · -- the at-least-one clause `pre ++ lits`.
    simp only [List.mem_singleton] at hone
    subst hone
    rcases hdisj with ⟨lit, hmem, hval⟩ | ⟨⟨lit, hmem, hval⟩, _⟩
    · exact ⟨lit, List.mem_append_left _ hmem, hval⟩
    · exact ⟨lit, List.mem_append_right _ hmem, hval⟩
  · -- one guarded at-most-one clause.
    simp only [muNegOnePairsOf, List.mem_flatMap, List.mem_range,
      List.mem_map, List.mem_filter, List.mem_range] at hpair
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
          exact h305_dimacsLitValue_neg_of_pos
            (hpos _ (by rw [hgj]; exact List.getElem_mem _)) hvj
      · refine ⟨-lits[i]!, List.mem_append_right _ (by simp), ?_⟩
        exact h305_dimacsLitValue_neg_of_pos
          (hpos _ (by rw [hgi]; exact List.getElem_mem _)) hvi
section ServiceFamily

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

/-- Service family of the induced valuation. -/
theorem muNegThreeZeroFiveServiceClauses_satisfied_of_nonCross
    (hsem : MuNegThreeZeroFiveNonCrossSemantics uTri vTri σ D X) :
    ∀ clause ∈ muNegOneServiceClauses uTri vTri
      (muNegOneHitPairs uTri vTri),
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X)
        clause := by
  intro clause hclause
  simp only [muNegOneServiceClauses, List.mem_flatMap, List.mem_range]
    at hclause
  obtain ⟨a, ha, w, hw, hcl⟩ := hclause
  rw [muNegOneOwners_length] at ha
  refine h305_service_shape_satisfied hcl ?_ ?_ ?_
  · -- positivity of the generated row literals.
    intro lit hlit
    rw [List.mem_filterMap] at hlit
    obtain ⟨b, _, hfb⟩ := hlit
    split at hfb
    · obtain ⟨x, hxv, rfl⟩ := muNegOneXLit?_eq_some hfb
      have hb := muNegOneXVar?_bounds hxv
      show (0 : Int) < (x : Int)
      exact_mod_cast by omega
    · exact absurd hfb (by simp)
  · -- the row literals are pairwise distinct.
    refine List.Nodup.filterMap ?_ List.nodup_range
    intro b b' lit hb hb'
    simp only [Option.mem_def] at hb hb'
    split at hb
    · next hcond =>
      split at hb'
      · next hcond' =>
        simp only [Bool.and_eq_true, bne_iff_ne] at hcond hcond'
        obtain ⟨x, hx, rfl⟩ := muNegOneXLit?_eq_some hb
        obtain ⟨x', hx', hxx⟩ := muNegOneXLit?_eq_some hb'
        rw [Int.ofNat.inj hxx] at hx
        exact h305_eq_of_minmax hcond.1 hcond'.1 (muNegOneXVar?_inj hx hx')
      · exact absurd hb' (by simp)
    · exact absurd hb (by simp)
  · -- guard or unique service.
    by_cases hact : muNegOneOwnerActive D a = true
    · right
      constructor
      · obtain ⟨b, hb80, hbne, hpm, hkey, hX⟩ :=
          hsem.service_exists a ha hact w hw
        have hsome := muNegOneXVar?_isSome_of_mem uTri vTri hkey
        cases hx : muNegOneXVar? (muNegOneHitPairs uTri vTri) a b with
        | none => rw [hx] at hsome; simp at hsome
        | some x =>
          refine ⟨Int.ofNat x, ?_, ?_⟩
          · rw [List.mem_filterMap]
            refine ⟨b, ?_, ?_⟩
            · rw [List.mem_range, muNegOneOwners_length]
              exact hb80
            · rw [if_pos ((Bool.and_eq_true _ _).mpr ⟨bne_iff_ne.mpr hbne, hpm⟩)]
              unfold muNegOneXLit?
              rw [hx]
              rfl
          · rw [h305_dimacsLitValue_ofNat
              (by have := muNegOneXVar?_bounds hx; omega),
              h305_valOfRelations_xvar hx]
            exact hX
      · intro l1 h1 l2 h2 hv1 hv2
        rw [List.mem_filterMap] at h1 h2
        obtain ⟨b1, hb1r, hf1⟩ := h1
        obtain ⟨b2, hb2r, hf2⟩ := h2
        rw [List.mem_range, muNegOneOwners_length] at hb1r hb2r
        split at hf1
        · next hcond1 =>
          split at hf2
          · next hcond2 =>
            simp only [Bool.and_eq_true, bne_iff_ne] at hcond1 hcond2
            obtain ⟨x1, hx1, rfl⟩ := muNegOneXLit?_eq_some hf1
            obtain ⟨x2, hx2, rfl⟩ := muNegOneXLit?_eq_some hf2
            have hX1 : X (min a b1) (max a b1) = true := by
              rw [h305_dimacsLitValue_ofNat
                (by have := muNegOneXVar?_bounds hx1; omega),
                h305_valOfRelations_xvar hx1] at hv1
              exact hv1
            have hX2 : X (min a b2) (max a b2) = true := by
              rw [h305_dimacsLitValue_ofNat
                (by have := muNegOneXVar?_bounds hx2; omega),
                h305_valOfRelations_xvar hx2] at hv2
              exact hv2
            have hb12 : b1 = b2 :=
              hsem.service_unique a ha hact w hw b1 b2
                hb1r hcond1.1 hcond1.2 (muNegOneXVar?_key_mem hx1) hX1
                hb2r hcond2.1 hcond2.2 (muNegOneXVar?_key_mem hx2) hX2
            subst hb12
            rw [hx1] at hx2
            rw [Option.some.inj hx2]
          · exact absurd hf2 (by simp)
        · exact absurd hf1 (by simp)
    · left
      have h16 : 16 ≤ a := by
        by_contra h16
        exact hact (by
          unfold muNegOneOwnerActive
          rw [if_pos (by omega)])
      cases hg : muNegOneGuard? uTri vTri a with
      | none =>
        rw [muNegOneGuard?, if_neg (by omega)] at hg
        exact absurd hg (by simp)
      | some g =>
        have hgeq : g = muNegOneDVar ((muNegOneOwners uTri vTri)[a]!).1
            (((muNegOneOwners uTri vTri)[a]!).2 - 8) := by
          rw [muNegOneGuard?, if_neg (by omega)] at hg
          exact (Option.some.inj hg).symm
        have howner : (muNegOneOwners uTri vTri)[a]! =
            ((a - 16) / 8, 8 + (a - 16) % 8) :=
          muNegOneOwnerAt_cross uTri vTri ⟨a, ha⟩ h16
        have hgeq' : g = muNegOneDVar ((a - 16) / 8) ((a - 16) % 8) := by
          rw [hgeq, howner]
          simp
        have hDtrue : D ((a - 16) / 8) ((a - 16) % 8) = true := by
          by_contra hDf
          refine hact ?_
          unfold muNegOneOwnerActive
          rw [if_neg (by omega)]
          simp only [Bool.not_eq_true] at hDf
          simp [hDf]
        refine ⟨Int.ofNat g, by simp, ?_⟩
        rw [h305_dimacsLitValue_ofNat
            (by rw [hgeq']; unfold muNegOneDVar; omega), hgeq',
          muNegOneValOfRelations_dvar uTri vTri D X
            (i := (a - 16) / 8) (j := (a - 16) % 8) (by omega) (by omega),
          hDtrue]

end ServiceFamily
section C4Family

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

/-- Positivity, valuation, and table membership of one generated hit
literal. -/
private theorem h305_xlit_props {o1 o2 : Nat} {lit : Int}
    (h : muNegOneXLit? (muNegOneHitPairs uTri vTri) o1 o2 = some lit) :
    0 < lit ∧
    dimacsLitValue (muNegOneValOfRelations uTri vTri D X) lit =
      X (min o1 o2) (max o1 o2) ∧
    (min o1 o2, max o1 o2) ∈ muNegOneHitPairs uTri vTri := by
  obtain ⟨x, hx, rfl⟩ := muNegOneXLit?_eq_some h
  have hb := muNegOneXVar?_bounds hx
  refine ⟨by show (0 : Int) < (x : Int); exact_mod_cast by omega, ?_,
    muNegOneXVar?_key_mem hx⟩
  rw [h305_dimacsLitValue_ofNat (by omega), h305_valOfRelations_xvar hx]

/-- Invert one monadic bind of an option do-block. -/
private theorem h305_option_bind_inv {α β : Type} {o : Option α}
    {f : α → Option β} {c : β}
    (h : (o >>= f) = some c) : ∃ x, o = some x ∧ f x = some c := by
  cases o with
  | none => simp at h
  | some x => exact ⟨x, rfl, h⟩

/-- Owner C4 family of the induced valuation. -/
theorem muNegThreeZeroFiveC4Clauses_satisfied_of_nonCross
    (hsem : MuNegThreeZeroFiveNonCrossSemantics uTri vTri σ D X) :
    ∀ clause ∈ muNegOneC4Clauses uTri vTri (muNegOneHitPairs uTri vTri),
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X)
        clause := by
  intro clause hclause
  simp only [muNegOneC4Clauses, List.mem_flatMap, List.mem_range,
    List.mem_filter] at hclause
  obtain ⟨a, ha, b, ⟨hb, hab⟩, hcl⟩ := hclause
  rw [muNegOneOwners_length] at ha hb
  have hab' : a < b := of_decide_eq_true hab
  split at hcl
  · next hshare =>
    rw [List.mem_filterMap] at hcl
    obtain ⟨g, hgmem, hf⟩ := hcl
    rw [List.mem_filter, List.mem_range, muNegOneOwners_length] at hgmem
    obtain ⟨hg80, hgcond⟩ := hgmem
    simp only [Bool.and_eq_true, bne_iff_ne] at hgcond
    obtain ⟨⟨⟨hga, hgb⟩, _⟩, _⟩ := hgcond
    obtain ⟨x, hxeq, hf⟩ := h305_option_bind_inv hf
    obtain ⟨y, hyeq, hf⟩ := h305_option_bind_inv hf
    have hcl' : clause = [-x, -y] := (Option.some.inj hf).symm
    obtain ⟨hxpos, hxval, hxkey⟩ := h305_xlit_props (D := D) (X := X) hxeq
    obtain ⟨hypos, hyval, hykey⟩ := h305_xlit_props (D := D) (X := X) hyeq
    by_cases hvx : dimacsLitValue
        (muNegOneValOfRelations uTri vTri D X) x = true
    · by_cases hvy : dimacsLitValue
          (muNegOneValOfRelations uTri vTri D X) y = true
      · exact absurd (hsem.c4_intersecting a b g hab' hb hg80 hga hgb
          hshare hxkey hykey (by rw [← hxval]; exact hvx)
          (by rw [← hyval]; exact hvy)) not_false
      · exact ⟨-y, by rw [hcl']; simp,
          h305_dimacsLitValue_neg_of_pos hypos hvy⟩
    · exact ⟨-x, by rw [hcl']; simp,
        h305_dimacsLitValue_neg_of_pos hxpos hvx⟩
  · next hnshare =>
    have hshare_f : muNegOneShare ((muNegOneOwners uTri vTri)[a]!)
        ((muNegOneOwners uTri vTri)[b]!) = false :=
      Bool.eq_false_iff.mpr hnshare
    set ks := (List.range (muNegOneOwners uTri vTri).length).filter
      (fun g => g != a && g != b &&
        (muNegOneXVar? (muNegOneHitPairs uTri vTri) a g).isSome &&
        (muNegOneXVar? (muNegOneHitPairs uTri vTri) b g).isSome)
      with hks
    rw [List.mem_flatMap] at hcl
    obtain ⟨gi, hgi, hcl⟩ := hcl
    rw [List.mem_range] at hgi
    rw [List.mem_filterMap] at hcl
    obtain ⟨hi, hhim, hf⟩ := hcl
    rw [List.mem_filter, List.mem_range] at hhim
    obtain ⟨hhi, hgihi⟩ := hhim
    have hgihi' : gi < hi := of_decide_eq_true hgihi
    obtain ⟨xag, hxag, hf⟩ := h305_option_bind_inv hf
    obtain ⟨xbg, hxbg, hf⟩ := h305_option_bind_inv hf
    obtain ⟨xah, hxah, hf⟩ := h305_option_bind_inv hf
    obtain ⟨xbh, hxbh, hf⟩ := h305_option_bind_inv hf
    have hcl' : clause = [-xag, -xbg, -xah, -xbh] :=
      (Option.some.inj hf).symm
    have hgmem : ks[gi]! ∈ ks := by
      rw [getElem!_pos ks gi hgi]
      exact List.getElem_mem _
    have hhmem : ks[hi]! ∈ ks := by
      rw [getElem!_pos ks hi hhi]
      exact List.getElem_mem _
    have hgmemf : ks[gi]! ∈
        (List.range (muNegOneOwners uTri vTri).length).filter
          (fun g => g != a && g != b &&
            (muNegOneXVar? (muNegOneHitPairs uTri vTri) a g).isSome &&
            (muNegOneXVar? (muNegOneHitPairs uTri vTri) b g).isSome) := by
      rw [← hks]
      exact hgmem
    have hhmemf : ks[hi]! ∈
        (List.range (muNegOneOwners uTri vTri).length).filter
          (fun g => g != a && g != b &&
            (muNegOneXVar? (muNegOneHitPairs uTri vTri) a g).isSome &&
            (muNegOneXVar? (muNegOneHitPairs uTri vTri) b g).isSome) := by
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
    rw [List.mem_range, muNegOneOwners_length] at hgr hhr
    simp only [Bool.and_eq_true, bne_iff_ne] at hgcond hhcond
    obtain ⟨⟨⟨hga, hgb⟩, _⟩, _⟩ := hgcond
    obtain ⟨⟨⟨hha, hhb⟩, _⟩, _⟩ := hhcond
    obtain ⟨hp1, hv1, hk1⟩ := h305_xlit_props (D := D) (X := X) hxag
    obtain ⟨hp2, hv2, hk2⟩ := h305_xlit_props (D := D) (X := X) hxbg
    obtain ⟨hp3, hv3, hk3⟩ := h305_xlit_props (D := D) (X := X) hxah
    obtain ⟨hp4, hv4, hk4⟩ := h305_xlit_props (D := D) (X := X) hxbh
    by_cases hb1 : dimacsLitValue
        (muNegOneValOfRelations uTri vTri D X) xag = true
    · by_cases hb2 : dimacsLitValue
          (muNegOneValOfRelations uTri vTri D X) xbg = true
      · by_cases hb3 : dimacsLitValue
            (muNegOneValOfRelations uTri vTri D X) xah = true
        · by_cases hb4 : dimacsLitValue
              (muNegOneValOfRelations uTri vTri D X) xbh = true
          · exact absurd (hsem.c4_no_two a b ks[gi]! ks[hi]! hab' hb
              hgr hhr hgh hga hgb hha hhb hshare_f hk1 hk2 hk3 hk4
              (by rw [← hv1]; exact hb1) (by rw [← hv2]; exact hb2)
              (by rw [← hv3]; exact hb3) (by rw [← hv4]; exact hb4))
              not_false
          · exact ⟨-xbh, by rw [hcl']; simp,
              h305_dimacsLitValue_neg_of_pos hp4 hb4⟩
        · exact ⟨-xah, by rw [hcl']; simp,
            h305_dimacsLitValue_neg_of_pos hp3 hb3⟩
      · exact ⟨-xbg, by rw [hcl']; simp,
          h305_dimacsLitValue_neg_of_pos hp2 hb2⟩
    · exact ⟨-xag, by rw [hcl']; simp,
        h305_dimacsLitValue_neg_of_pos hp1 hb1⟩

end C4Family


theorem muNegThreeZeroFiveOwnerConstraintSemantics_of_finite
    (hrowSame : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun j => D i j) = 2)
    (hrowOpp : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun j => D i j) = 3)
    (hcolSame : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun i => D i j) = 2)
    (hcolOpp : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun i => D i j) = 3)
    (hsem : MuNegThreeZeroFiveNonCrossSemantics uTri vTri σ D X) :
    MuNegThreeZeroFiveOwnerConstraintSemantics uTri vTri σ
      (muNegOneValOfRelations uTri vTri D X) where
  cross_rows := muNegThreeZeroFiveCrossRowClauses_satisfied_of_counts
    hrowSame hrowOpp
  cross_columns := muNegThreeZeroFiveCrossColClauses_satisfied_of_counts
    hcolSame hcolOpp
  intertwining := muNegThreeZeroFiveIntertwineClauses_satisfied_of_nonCross hsem
  hit_activity := muNegThreeZeroFiveHitActivityClauses_satisfied_of_nonCross hsem
  service := muNegThreeZeroFiveServiceClauses_satisfied_of_nonCross hsem
  exterior_c4 := muNegThreeZeroFiveC4Clauses_satisfied_of_nonCross hsem

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveOwnerConstraintSemantics_of_finite

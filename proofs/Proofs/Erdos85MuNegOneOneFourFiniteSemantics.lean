import Proofs.Erdos85MuNegOneOneFourOwnerValuation

/-!
# Finite semantics for the μ=-1 `(1,4)` owner-grid CNFs — defect families

Node: outline F.3 (μ=-1 lane; graph→valuation bridge, increment 3b-i of
the plan in squad msgs 13943/13945/13947).

`MuNegOneOneFourFiniteSemantics` is the clean handshake between graph
transport and generator-local literal bookkeeping, mirroring the
low-`8+8` bridge: two `Nat`-coded relations with count and uniqueness
facts, no DIMACS numbering.  This file embeds the three defect-side
clause families (cross rows, cross columns, intertwining) of the
induced valuation; the hit-side families follow in the next layer.
-/

namespace Erdos85

open Std Sat

/-- Finite semantic content of one `(−1,1,4)` owner grid: a cross-defect
relation `D` on shore coordinates `0..7` and an owner-vertex adjacency
relation `X` on normalized typed owner index pairs. -/
structure MuNegOneOneFourFiniteSemantics (uTri vTri σ : Bool)
    (D X : Nat → Nat → Bool) : Prop where
  row_same_two : ∀ i, i < 8 →
    (((List.range 8).filter fun j =>
      muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun j => D i j) = 2
  row_opp_two : ∀ i, i < 8 →
    (((List.range 8).filter fun j =>
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun j => D i j) = 2
  col_same_two : ∀ j, j < 8 →
    (((List.range 8).filter fun i =>
      muNegOneSign σ i == muNegOneSign σ (8 + j)).countP fun i => D i j) = 2
  col_opp_two : ∀ j, j < 8 →
    (((List.range 8).filter fun i =>
      !(muNegOneSign σ i == muNegOneSign σ (8 + j))).countP fun i => D i j) = 2
  intertwine : ∀ i j, i < 8 → j < 8 →
    (cond (D ((i + 7) % 8) j) 1 0) + (cond (D ((i + 1) % 8) j) 1 0) =
      (cond (D i ((j + 1) % 8)) 1 0) + (cond (D i ((j + 7) % 8)) 1 0)
  hit_active : ∀ a b, (a, b) ∈ muNegOneHitPairs uTri vTri →
    X a b = true →
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
        X (min a b) (max a b) = true →
        c < 80 → c ≠ a →
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

/-! ## Generic exactly-two transport -/

/-- A count split used below: predicates split along a discriminator. -/
private theorem countP_split {α : Type*} (l : List α)
    (p q : α → Bool) :
    l.countP p =
      l.countP (fun a => p a && q a) + l.countP (fun a => p a && !q a) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hp : p a
    · by_cases hq : q a <;> simp [hp, hq, ih] <;> omega
    · simp [hp, ih]

/-- A falsified positive literal satisfies its negation. -/
private theorem dimacsLitValue_neg_of_pos {val : DimacsValuation} {l : Int}
    (hl : 0 < l) (hv : ¬ dimacsLitValue val l = true) :
    dimacsLitValue val (-l) = true := by
  simp only [dimacsLitValue, if_pos hl, Bool.not_eq_true] at hv
  rw [dimacsLitValue, if_neg (by omega), Int.natAbs_neg]
  simp [hv]

/-- Positive nodup literal rows with exactly two satisfied literals meet
the generator's exactly-two block semantics. -/
theorem muNegOneExactlyTwoSemantics_of_two
    {val : DimacsValuation} {lits : List Int}
    (hnodup : lits.Nodup) (hpos : ∀ lit ∈ lits, 0 < lit)
    (htwo : (lits.countP fun l => dimacsLitValue val l) = 2) :
    MuNegOneExactlyTwoSemantics val lits := by
  constructor
  · -- drop-one: at least two true literals survive removing one value.
    intro x hx
    have hsplit := countP_split lits
      (fun l => dimacsLitValue val l) (fun l => l == x)
    have hcnt_eq : lits.countP (fun l => dimacsLitValue val l && l == x) ≤
        lits.count x := by
      rw [List.count]
      exact List.countP_mono_left fun l _ h => by
        have := (Bool.and_eq_true _ _).mp h
        simpa using this.2
    have hone : lits.count x ≤ 1 := List.nodup_iff_count_le_one.mp hnodup x
    have hpos' : 0 < lits.countP
        (fun l => dimacsLitValue val l && !(l == x)) := by omega
    obtain ⟨lit, hmem, hlit⟩ := List.countP_pos_iff.mp hpos'
    obtain ⟨hval, hne⟩ := (Bool.and_eq_true _ _).mp hlit
    exact ⟨lit, List.mem_filter.mpr ⟨hmem, by simpa using hne⟩, hval⟩
  · -- no-three: three positions cannot all be satisfied.
    intro i j k hi hj hk hij hjk
    by_cases hvi : dimacsLitValue val lits[i]! = true
    · by_cases hvj : dimacsLitValue val lits[j]! = true
      · by_cases hvk : dimacsLitValue val lits[k]! = true
        · exfalso
          have hgi : lits[i]! = lits[i] := getElem!_pos lits i hi
          have hgj : lits[j]! = lits[j] := getElem!_pos lits j hj
          have hgk : lits[k]! = lits[k] := getElem!_pos lits k hk
          have hij' : lits[i] ≠ lits[j] := fun h =>
            absurd ((List.Nodup.getElem_inj_iff hnodup).mp h) (by omega)
          have hjk' : lits[j] ≠ lits[k] := fun h =>
            absurd ((List.Nodup.getElem_inj_iff hnodup).mp h) (by omega)
          have hik' : lits[i] ≠ lits[k] := fun h =>
            absurd ((List.Nodup.getElem_inj_iff hnodup).mp h) (by omega)
          have hsub : [lits[i], lits[j], lits[k]] ⊆
              lits.filter fun l => dimacsLitValue val l := by
            intro l hl
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
            rcases hl with rfl | rfl | rfl <;>
              exact List.mem_filter.mpr ⟨List.getElem_mem _, by
                first
                  | simpa [← hgi] using hvi
                  | simpa [← hgj] using hvj
                  | simpa [← hgk] using hvk⟩
          have hnd : ([lits[i], lits[j], lits[k]] : List Int).Nodup := by
            simp [hij', hjk', hik']
          have hlen := List.Subperm.length_le (hnd.subperm hsub)
          have hlen3 : ([lits[i], lits[j], lits[k]] : List Int).length = 3 :=
            rfl
          rw [← List.countP_eq_length_filter] at hlen
          omega
        · refine ⟨-lits[k]!, by simp, dimacsLitValue_neg_of_pos ?_ hvk⟩
          exact hpos _ (by
            rw [getElem!_pos lits k hk]; exact List.getElem_mem _)
      · refine ⟨-lits[j]!, by simp, dimacsLitValue_neg_of_pos ?_ hvj⟩
        exact hpos _ (by
          rw [getElem!_pos lits j hj]; exact List.getElem_mem _)
    · refine ⟨-lits[i]!, by simp, dimacsLitValue_neg_of_pos ?_ hvi⟩
      exact hpos _ (by
        rw [getElem!_pos lits i hi]; exact List.getElem_mem _)

/-! ## Defect-family embeddings -/

/-- The four Boolean implications of one intertwining cell. -/
private theorem bool_sum_eq_cases {A B C E : Bool}
    (h : (cond A 1 0) + (cond B 1 0) = (cond C 1 0) + (cond E 1 0)) :
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

private theorem dimacsLitValue_ofNat {val : DimacsValuation} {n : Nat}
    (hn : 0 < n) : dimacsLitValue val (Int.ofNat n) = val n := by
  have h : (0 : Int) < Int.ofNat n := by
    show (0 : Int) < (n : Int)
    exact_mod_cast hn
  rw [dimacsLitValue, if_pos h]
  simp

private theorem dimacsLitValue_neg_ofNat {val : DimacsValuation} {n : Nat}
    (hn : 0 < n) : dimacsLitValue val (-Int.ofNat n) = !val n := by
  have h : (0 : Int) < Int.ofNat n := by
    show (0 : Int) < (n : Int)
    exact_mod_cast hn
  rw [dimacsLitValue, if_neg (by omega), Int.natAbs_neg]
  simp

/-- All eight clauses of one equal-sum cell hold when the counted
valuation values balance. -/
theorem muNegOneSumEq_satisfied {val : DimacsValuation} {a b c d : Nat}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcount : (cond (val a) 1 0) + (cond (val b) 1 0) =
      (cond (val c) 1 0) + (cond (val d) 1 0)) :
    ∀ clause ∈ muNegOneSumEq (Int.ofNat a) (Int.ofNat b)
      (Int.ofNat c) (Int.ofNat d),
      dimacsClauseSatisfied val clause := by
  obtain ⟨hAcd, hBcd, hCab, hDab, hABc, hABd, hCDa, hCDb⟩ :=
    bool_sum_eq_cases hcount
  intro clause hclause
  simp only [muNegOneSumEq, List.mem_cons, List.not_mem_nil, or_false]
    at hclause
  rcases hclause with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · by_cases hA : val a = true
    · rcases hAcd hA with h | h
      · exact ⟨Int.ofNat c, by simp, by rw [dimacsLitValue_ofNat hc, h]⟩
      · exact ⟨Int.ofNat d, by simp, by rw [dimacsLitValue_ofNat hd, h]⟩
    · exact ⟨-Int.ofNat a, by simp, by
        rw [dimacsLitValue_neg_ofNat ha]; simpa using hA⟩
  · by_cases hB : val b = true
    · rcases hBcd hB with h | h
      · exact ⟨Int.ofNat c, by simp, by rw [dimacsLitValue_ofNat hc, h]⟩
      · exact ⟨Int.ofNat d, by simp, by rw [dimacsLitValue_ofNat hd, h]⟩
    · exact ⟨-Int.ofNat b, by simp, by
        rw [dimacsLitValue_neg_ofNat hb]; simpa using hB⟩
  · by_cases hC : val c = true
    · rcases hCab hC with h | h
      · exact ⟨Int.ofNat a, by simp, by rw [dimacsLitValue_ofNat ha, h]⟩
      · exact ⟨Int.ofNat b, by simp, by rw [dimacsLitValue_ofNat hb, h]⟩
    · exact ⟨-Int.ofNat c, by simp, by
        rw [dimacsLitValue_neg_ofNat hc]; simpa using hC⟩
  · by_cases hD : val d = true
    · rcases hDab hD with h | h
      · exact ⟨Int.ofNat a, by simp, by rw [dimacsLitValue_ofNat ha, h]⟩
      · exact ⟨Int.ofNat b, by simp, by rw [dimacsLitValue_ofNat hb, h]⟩
    · exact ⟨-Int.ofNat d, by simp, by
        rw [dimacsLitValue_neg_ofNat hd]; simpa using hD⟩
  · by_cases hA : val a = true
    · by_cases hB : val b = true
      · exact ⟨Int.ofNat c, by simp, by
          rw [dimacsLitValue_ofNat hc, hABc hA hB]⟩
      · exact ⟨-Int.ofNat b, by simp, by
          rw [dimacsLitValue_neg_ofNat hb]; simpa using hB⟩
    · exact ⟨-Int.ofNat a, by simp, by
        rw [dimacsLitValue_neg_ofNat ha]; simpa using hA⟩
  · by_cases hA : val a = true
    · by_cases hB : val b = true
      · exact ⟨Int.ofNat d, by simp, by
          rw [dimacsLitValue_ofNat hd, hABd hA hB]⟩
      · exact ⟨-Int.ofNat b, by simp, by
          rw [dimacsLitValue_neg_ofNat hb]; simpa using hB⟩
    · exact ⟨-Int.ofNat a, by simp, by
        rw [dimacsLitValue_neg_ofNat ha]; simpa using hA⟩
  · by_cases hC : val c = true
    · by_cases hD : val d = true
      · exact ⟨Int.ofNat a, by simp, by
          rw [dimacsLitValue_ofNat ha, hCDa hC hD]⟩
      · exact ⟨-Int.ofNat d, by simp, by
          rw [dimacsLitValue_neg_ofNat hd]; simpa using hD⟩
    · exact ⟨-Int.ofNat c, by simp, by
        rw [dimacsLitValue_neg_ofNat hc]; simpa using hC⟩
  · by_cases hC : val c = true
    · by_cases hD : val d = true
      · exact ⟨Int.ofNat b, by simp, by
          rw [dimacsLitValue_ofNat hb, hCDb hC hD]⟩
      · exact ⟨-Int.ofNat d, by simp, by
          rw [dimacsLitValue_neg_ofNat hd]; simpa using hD⟩
    · exact ⟨-Int.ofNat c, by simp, by
        rw [dimacsLitValue_neg_ofNat hc]; simpa using hC⟩

section Families

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

/-- Exactly-two semantics for one defect row or column list. -/
private theorem muNegOneExactlyTwo_of_countP (Dv : Nat → Bool)
    (f : Nat → Nat) (hf : ∀ x y, f x = f y → x = y)
    (hfpos : ∀ j, 0 < f j) (js : List Nat) (hnd : js.Nodup)
    (hval : ∀ j ∈ js,
      muNegOneValOfRelations uTri vTri D X (f j) = Dv j)
    (hcount : (js.countP fun j => Dv j) = 2) :
    MuNegOneExactlyTwoSemantics
      (muNegOneValOfRelations uTri vTri D X)
      (js.map fun j => Int.ofNat (f j)) := by
  apply muNegOneExactlyTwoSemantics_of_two
  · exact hnd.map fun x y h => hf x y (Int.ofNat.inj h)
  · intro lit hlit
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hlit
    show (0 : Int) < (f j : Int)
    exact_mod_cast hfpos j
  · rw [List.countP_map]
    rw [← hcount]
    apply List.countP_congr
    intro j hj
    simp only [Function.comp_apply]
    rw [dimacsLitValue_ofNat (hfpos j), hval j hj]

/-- Cross-row family of the induced valuation. -/
theorem muNegOneCrossRowClauses_satisfied_of_finite
    (hsem : MuNegOneOneFourFiniteSemantics uTri vTri σ D X) :
    ∀ clause ∈ muNegOneCrossRowClauses σ,
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X)
        clause := by
  apply muNegOneCrossRowClauses_satisfied
  · intro i hi
    refine muNegOneExactlyTwo_of_countP (Dv := fun j => D i j)
      (fun j => muNegOneDVar i j) (fun x y h => ?_) (fun j => ?_)
      _ (List.nodup_range.filter _) (fun j hj => ?_)
      (hsem.row_same_two i hi)
    · unfold muNegOneDVar at h
      omega
    · unfold muNegOneDVar
      omega
    · have hj8 : j < 8 :=
        List.mem_range.mp (List.mem_of_mem_filter hj)
      exact muNegOneValOfRelations_dvar uTri vTri D X hi hj8
  · intro i hi
    refine muNegOneExactlyTwo_of_countP (Dv := fun j => D i j)
      (fun j => muNegOneDVar i j) (fun x y h => ?_) (fun j => ?_)
      _ (List.nodup_range.filter _) (fun j hj => ?_)
      (hsem.row_opp_two i hi)
    · unfold muNegOneDVar at h
      omega
    · unfold muNegOneDVar
      omega
    · have hj8 : j < 8 :=
        List.mem_range.mp (List.mem_of_mem_filter hj)
      exact muNegOneValOfRelations_dvar uTri vTri D X hi hj8

/-- Cross-column family of the induced valuation. -/
theorem muNegOneCrossColClauses_satisfied_of_finite
    (hsem : MuNegOneOneFourFiniteSemantics uTri vTri σ D X) :
    ∀ clause ∈ muNegOneCrossColClauses σ,
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X)
        clause := by
  apply muNegOneCrossColClauses_satisfied
  · intro j hj
    refine muNegOneExactlyTwo_of_countP (Dv := fun i => D i j)
      (fun i => muNegOneDVar i j) (fun x y h => ?_) (fun i => ?_)
      _ (List.nodup_range.filter _) (fun i hi => ?_)
      (hsem.col_same_two j hj)
    · unfold muNegOneDVar at h
      omega
    · unfold muNegOneDVar
      omega
    · have hi8 : i < 8 :=
        List.mem_range.mp (List.mem_of_mem_filter hi)
      exact muNegOneValOfRelations_dvar uTri vTri D X hi8 hj
  · intro j hj
    refine muNegOneExactlyTwo_of_countP (Dv := fun i => D i j)
      (fun i => muNegOneDVar i j) (fun x y h => ?_) (fun i => ?_)
      _ (List.nodup_range.filter _) (fun i hi => ?_)
      (hsem.col_opp_two j hj)
    · unfold muNegOneDVar at h
      omega
    · unfold muNegOneDVar
      omega
    · have hi8 : i < 8 :=
        List.mem_range.mp (List.mem_of_mem_filter hi)
      exact muNegOneValOfRelations_dvar uTri vTri D X hi8 hj

/-- Intertwining family of the induced valuation. -/
theorem muNegOneIntertwineClauses_satisfied_of_finite
    (hsem : MuNegOneOneFourFiniteSemantics uTri vTri σ D X) :
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

end Families

/-! ## Hit-side helpers -/

set_option maxHeartbeats 0 in
theorem muNegOneHitPairs_wf :
    ∀ uTri vTri : Bool, ((muNegOneHitPairs uTri vTri).all fun p =>
      decide (p.1 < p.2) && decide (p.2 < 80)) = true := by
  native_decide

theorem muNegOneHitPairs_lt {uTri vTri : Bool} {p : Nat × Nat}
    (hp : p ∈ muNegOneHitPairs uTri vTri) : p.1 < p.2 ∧ p.2 < 80 := by
  have h := List.all_eq_true.mp (muNegOneHitPairs_wf uTri vTri) p hp
  simpa using h

private theorem pair_norm (a b : Nat) :
    (if a < b then (a, b) else (b, a)) = (min a b, max a b) := by
  rcases Nat.lt_or_ge a b with h | h
  · simp [h, Nat.min_eq_left (Nat.le_of_lt h),
      Nat.max_eq_right (Nat.le_of_lt h)]
  · simp [Nat.not_lt.mpr h, Nat.min_eq_right h, Nat.max_eq_left h]

theorem muNegOneXVar?_bounds {pairs : List (Nat × Nat)} {a b x : Nat}
    (h : muNegOneXVar? pairs a b = some x) : 65 ≤ x := by
  unfold muNegOneXVar? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨k, _, rfl⟩ := h
  omega

theorem muNegOneXVar?_key_mem {pairs : List (Nat × Nat)} {a b x : Nat}
    (h : muNegOneXVar? pairs a b = some x) :
    (min a b, max a b) ∈ pairs := by
  unfold muNegOneXVar? at h
  rw [pair_norm, Option.map_eq_some_iff] at h
  obtain ⟨k, hk, _⟩ := h
  exact List.mem_of_getElem? (list_idxOf?_some_getElem? hk)

theorem muNegOneXVar?_inj {pairs : List (Nat × Nat)} {a b b' x : Nat}
    (h : muNegOneXVar? pairs a b = some x)
    (h' : muNegOneXVar? pairs a b' = some x) :
    (min a b, max a b) = (min a b', max a b') := by
  unfold muNegOneXVar? at h h'
  rw [pair_norm, Option.map_eq_some_iff] at h h'
  obtain ⟨k, hk, hkx⟩ := h
  obtain ⟨k', hk', hk'x⟩ := h'
  have hkk : k = k' := by omega
  subst hkk
  have e1 := list_idxOf?_some_getElem? hk
  have e2 := list_idxOf?_some_getElem? hk'
  rw [e1] at e2
  exact Option.some.inj e2

private theorem eq_of_minmax {a b b' : Nat} (_hb : b ≠ a) (_hb' : b' ≠ a)
    (h : (min a b, max a b) = (min a b', max a b')) : b = b' := by
  have h1 : min a b = min a b' := congrArg Prod.fst h
  have h2 : max a b = max a b' := congrArg Prod.snd h
  omega

/-- The valuation of a generated hit variable, normalized-pair form. -/
private theorem valOfRelations_xvar' {uTri vTri : Bool}
    {D X : Nat → Nat → Bool} {a b x : Nat}
    (h : muNegOneXVar? (muNegOneHitPairs uTri vTri) a b = some x) :
    muNegOneValOfRelations uTri vTri D X x = X (min a b) (max a b) :=
  muNegOneValOfRelations_xvar uTri vTri D X h

section HitFamilies

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

/-- Hit-activity family of the induced valuation. -/
theorem muNegOneHitActivityClauses_satisfied_of_finite
    (hsem : MuNegOneOneFourFiniteSemantics uTri vTri σ D X) :
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
    have h := valOfRelations_xvar' (D := D) (X := X) hx
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
      rw [dimacsLitValue_neg_ofNat (by rw [hgeq']; unfold muNegOneDVar; omega),
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
      rw [dimacsLitValue_neg_ofNat (by
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


end Erdos85

#print axioms Erdos85.muNegOneCrossRowClauses_satisfied_of_finite
#print axioms Erdos85.muNegOneCrossColClauses_satisfied_of_finite
#print axioms Erdos85.muNegOneIntertwineClauses_satisfied_of_finite
#print axioms Erdos85.muNegOneHitActivityClauses_satisfied_of_finite

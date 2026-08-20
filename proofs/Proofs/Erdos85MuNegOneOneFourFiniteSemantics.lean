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

/-! ## Service family -/

/-- Unfold one generated hit literal to its variable. -/
theorem muNegOneXLit?_eq_some {pairs : List (Nat × Nat)} {a b : Nat}
    {lit : Int} (h : muNegOneXLit? pairs a b = some lit) :
    ∃ x : Nat, muNegOneXVar? pairs a b = some x ∧ lit = Int.ofNat x := by
  unfold muNegOneXLit? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

/-- One guarded exact-service block is satisfied as soon as either the
guard fires or the row holds a unique true literal. -/
private theorem service_shape_satisfied {val : DimacsValuation}
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
          exact dimacsLitValue_neg_of_pos
            (hpos _ (by rw [hgj]; exact List.getElem_mem _)) hvj
      · refine ⟨-lits[i]!, List.mem_append_right _ (by simp), ?_⟩
        exact dimacsLitValue_neg_of_pos
          (hpos _ (by rw [hgi]; exact List.getElem_mem _)) hvi

section ServiceFamily

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

/-- Service family of the induced valuation. -/
theorem muNegOneServiceClauses_satisfied_of_finite
    (hsem : MuNegOneOneFourFiniteSemantics uTri vTri σ D X) :
    ∀ clause ∈ muNegOneServiceClauses uTri vTri
      (muNegOneHitPairs uTri vTri),
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X)
        clause := by
  intro clause hclause
  simp only [muNegOneServiceClauses, List.mem_flatMap, List.mem_range]
    at hclause
  obtain ⟨a, ha, w, hw, hcl⟩ := hclause
  rw [muNegOneOwners_length] at ha
  refine service_shape_satisfied hcl ?_ ?_ ?_
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
        exact eq_of_minmax hcond.1 hcond'.1 (muNegOneXVar?_inj hx hx')
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
          · rw [dimacsLitValue_ofNat
              (by have := muNegOneXVar?_bounds hx; omega),
              valOfRelations_xvar' hx]
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
              rw [dimacsLitValue_ofNat
                (by have := muNegOneXVar?_bounds hx1; omega),
                valOfRelations_xvar' hx1] at hv1
              exact hv1
            have hX2 : X (min a b2) (max a b2) = true := by
              rw [dimacsLitValue_ofNat
                (by have := muNegOneXVar?_bounds hx2; omega),
                valOfRelations_xvar' hx2] at hv2
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
        rw [dimacsLitValue_ofNat
            (by rw [hgeq']; unfold muNegOneDVar; omega), hgeq',
          muNegOneValOfRelations_dvar uTri vTri D X
            (i := (a - 16) / 8) (j := (a - 16) % 8) (by omega) (by omega),
          hDtrue]

end ServiceFamily

/-! ## Owner C4 family and assembly -/

section C4Family

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

/-- Positivity, valuation, and table membership of one generated hit
literal. -/
private theorem xlit_props {o1 o2 : Nat} {lit : Int}
    (h : muNegOneXLit? (muNegOneHitPairs uTri vTri) o1 o2 = some lit) :
    0 < lit ∧
    dimacsLitValue (muNegOneValOfRelations uTri vTri D X) lit =
      X (min o1 o2) (max o1 o2) ∧
    (min o1 o2, max o1 o2) ∈ muNegOneHitPairs uTri vTri := by
  obtain ⟨x, hx, rfl⟩ := muNegOneXLit?_eq_some h
  have hb := muNegOneXVar?_bounds hx
  refine ⟨by show (0 : Int) < (x : Int); exact_mod_cast by omega, ?_,
    muNegOneXVar?_key_mem hx⟩
  rw [dimacsLitValue_ofNat (by omega), valOfRelations_xvar' hx]

/-- Invert one monadic bind of an option do-block. -/
private theorem option_bind_inv {α β : Type} {o : Option α}
    {f : α → Option β} {c : β}
    (h : (o >>= f) = some c) : ∃ x, o = some x ∧ f x = some c := by
  cases o with
  | none => simp at h
  | some x => exact ⟨x, rfl, h⟩

/-- Owner C4 family of the induced valuation. -/
theorem muNegOneC4Clauses_satisfied_of_finite
    (hsem : MuNegOneOneFourFiniteSemantics uTri vTri σ D X) :
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
    obtain ⟨x, hxeq, hf⟩ := option_bind_inv hf
    obtain ⟨y, hyeq, hf⟩ := option_bind_inv hf
    have hcl' : clause = [-x, -y] := (Option.some.inj hf).symm
    obtain ⟨hxpos, hxval, hxkey⟩ := xlit_props (D := D) (X := X) hxeq
    obtain ⟨hypos, hyval, hykey⟩ := xlit_props (D := D) (X := X) hyeq
    by_cases hvx : dimacsLitValue
        (muNegOneValOfRelations uTri vTri D X) x = true
    · by_cases hvy : dimacsLitValue
          (muNegOneValOfRelations uTri vTri D X) y = true
      · exact absurd (hsem.c4_intersecting a b g hab' hb hg80 hga hgb
          hshare hxkey hykey (by rw [← hxval]; exact hvx)
          (by rw [← hyval]; exact hvy)) not_false
      · exact ⟨-y, by rw [hcl']; simp,
          dimacsLitValue_neg_of_pos hypos hvy⟩
    · exact ⟨-x, by rw [hcl']; simp,
        dimacsLitValue_neg_of_pos hxpos hvx⟩
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
    obtain ⟨xag, hxag, hf⟩ := option_bind_inv hf
    obtain ⟨xbg, hxbg, hf⟩ := option_bind_inv hf
    obtain ⟨xah, hxah, hf⟩ := option_bind_inv hf
    obtain ⟨xbh, hxbh, hf⟩ := option_bind_inv hf
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
    obtain ⟨hp1, hv1, hk1⟩ := xlit_props (D := D) (X := X) hxag
    obtain ⟨hp2, hv2, hk2⟩ := xlit_props (D := D) (X := X) hxbg
    obtain ⟨hp3, hv3, hk3⟩ := xlit_props (D := D) (X := X) hxah
    obtain ⟨hp4, hv4, hk4⟩ := xlit_props (D := D) (X := X) hxbh
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
              dimacsLitValue_neg_of_pos hp4 hb4⟩
        · exact ⟨-xah, by rw [hcl']; simp,
            dimacsLitValue_neg_of_pos hp3 hb3⟩
      · exact ⟨-xbg, by rw [hcl']; simp,
          dimacsLitValue_neg_of_pos hp2 hb2⟩
    · exact ⟨-xag, by rw [hcl']; simp,
        dimacsLitValue_neg_of_pos hp1 hb1⟩

end C4Family

section Assembly

variable {uTri vTri σ : Bool} {D X : Nat → Nat → Bool}

/-- Assembled constraint semantics of the induced valuation. -/
theorem muNegOneOneFourConstraintSemantics_of_finite
    (hsem : MuNegOneOneFourFiniteSemantics uTri vTri σ D X) :
    MuNegOneOneFourOwnerConstraintSemantics uTri vTri σ
      (muNegOneValOfRelations uTri vTri D X) where
  cross_rows := muNegOneCrossRowClauses_satisfied_of_finite hsem
  cross_columns := muNegOneCrossColClauses_satisfied_of_finite hsem
  intertwining := muNegOneIntertwineClauses_satisfied_of_finite hsem
  hit_activity := muNegOneHitActivityClauses_satisfied_of_finite hsem
  service := muNegOneServiceClauses_satisfied_of_finite hsem
  exterior_c4 := muNegOneC4Clauses_satisfied_of_finite hsem

/-- **Finite-relation contradiction socket.**  Any pair of `Nat`-coded
relations meeting the finite semantics of a canonical `(−1,1,4)` sector
pair is impossible. -/
theorem muNegOneOneFourFiniteSemantics_false
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true))
    (hsem : MuNegOneOneFourFiniteSemantics uTri vTri σ D X) : False :=
  muNegOneOneFourOwnerConstraintSemantics_false' hcanon
    (muNegOneOneFourConstraintSemantics_of_finite hsem)

end Assembly




end Erdos85

#print axioms Erdos85.muNegOneCrossRowClauses_satisfied_of_finite
#print axioms Erdos85.muNegOneCrossColClauses_satisfied_of_finite
#print axioms Erdos85.muNegOneIntertwineClauses_satisfied_of_finite
#print axioms Erdos85.muNegOneHitActivityClauses_satisfied_of_finite
#print axioms Erdos85.muNegOneServiceClauses_satisfied_of_finite
#print axioms Erdos85.muNegOneC4Clauses_satisfied_of_finite
#print axioms Erdos85.muNegOneOneFourFiniteSemantics_false

import Mathlib
import Proofs.InclusionExclusionBonferroniGeneral

/-
# The Second Bonferroni Inequality in Union Form, with a Sharp Tightness Criterion

## What This Proves
Let `A : ι → Finset α` be a finite family of finite sets. Write

    U   = ⋃_i A i                         (the union),
    S₁  = Σ_i |A i|                        (sum of sizes),
    S₂  = Σ_{i<j} |A i ∩ A j|              (sum of pairwise intersection sizes).

The **second Bonferroni inequality** is the lower bound

    |U|  ≥  S₁ − S₂.                                            (`second_bonferroni`)

This is the `m = 2` truncation of inclusion–exclusion, dual to the first Bonferroni
inequality `|U| ≤ S₁` proved in the parent gallery file. We go further and pin down the
**exact defect** of the bound by a single non-negative sum over the union:

    |U| − (S₁ − S₂)  =  Σ_{x ∈ U}  C(deg x − 1, 2),            (`union_card_sub_eq_gap`)

where `deg x = #{i : x ∈ A i}` is the number of sets containing `x`. Since each term is a
binomial coefficient, the inequality is immediate, and equality is characterised sharply:

    |U| = S₁ − S₂   ⟺   every element lies in at most two sets  (∀ x, deg x ≤ 2)
                    ⟺   all triple intersections are empty.     (`second_bonferroni_eq_iff`,
                                                                  `deg_le_two_iff_no_triple`)

## A correction to the folklore tightness claim
The bound is *often* stated to be tight exactly for **disjoint** families. That is wrong: it
is only a *sufficient* condition. The truncated sieve already collapses as soon as no point is
covered three or more times — pairwise overlaps are harmless. We prove disjointness is
sufficient (`disjoint_imp_tight`) and exhibit a concrete family with a non-empty pairwise
intersection for which the second Bonferroni bound is nonetheless *exact*
(`exFam`, over `Fin 3`: `{0,1}` and `{1,2}` overlap in `1`, yet `|U| = 3 = S₁ − S₂`). The
genuinely sharp criterion is "no triple overlaps", which is strictly weaker than disjointness.

## Proof Strategy
Everything is reduced to the per-element reindexing already established in the gallery file
`InclusionExclusionBonferroniGeneral`. That file proves
`bonf A m = Σ_x altPartial (deg A x) m` and `bonf A m − noneCard A = Σ_x term`, where `bonf A 2`
is the `m = 2` truncated sieve and `noneCard A` counts points in no set. We

1. evaluate `bonf A 2 = |α| − S₁ + S₂` (the three layers `S₀ = |α|`, `S₁`, `S₂`);
2. note `|U| = |α| − noneCard A` (a point is in the union iff its degree is positive);
3. evaluate each per-element error term at `m = 2` to `C(deg x − 1, 2)`;

and combine. The whole development is `sorry`-free and `axiom`-free (the worked numerical
witnesses use `decide`, not `native_decide`).

## Relationship to the Gallery
Parent `inclusion-exclusion-oq-01-oq-01` (`InclusionExclusionGeneral`) proves the *first*
Bonferroni inequality `|U| ≤ S₁` and lists "prove the second Bonferroni inequality and
characterise tightness" as an explicit open question; this file answers it, and corrects the
"disjoint families" guess to the sharp "no triple overlaps" criterion. The truncated-sieve
machinery is reused from sibling `InclusionExclusionBonferroniGeneral`.
-/

namespace InclusionExclusionSecondBonferroni

open Finset InclusionExclusionBonferroniGeneral

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-
## Part I: The union and the two sieve sums in readable form
-/

/-- The union `⋃_i A i`, described as the set of elements of positive degree. -/
def unionSet (A : ι → Finset α) : Finset α := (univ : Finset α).filter (fun x => 0 < deg A x)

/-- `unionSet` really is the indexed union `⋃_i A i`. -/
theorem unionSet_eq_biUnion (A : ι → Finset α) :
    unionSet A = (univ : Finset ι).biUnion A := by
  ext x
  simp only [unionSet, mem_filter, mem_univ, true_and, mem_biUnion, deg, Finset.card_pos,
    Finset.filter_nonempty_iff]

/-- `S₁ = Σ_i |A i|`, the sum of the set sizes (the first Bonferroni term). -/
def S1 (A : ι → Finset α) : ℤ := ∑ i : ι, ((A i).card : ℤ)

/-- `S₂ = Σ_{|J| = 2} |⋂_{i ∈ J} A i|`, the sum of pairwise intersection sizes
(the second Bonferroni term). This is exactly the `k = 2` inclusion–exclusion layer. -/
def S2 (A : ι → Finset α) : ℤ := sieveLayer A 2

/-- **Transparency for `S₂`.** Each size-two layer term is the cardinality of an honest
pairwise intersection: for `i ≠ j`, `|⋂_{l ∈ {i,j}} A l| = |A i ∩ A j|`. -/
theorem interCard_pair (A : ι → Finset α) {i j : ι} (hij : i ≠ j) :
    interCard A {i, j} = (A i ∩ A j).card := by
  unfold interCard
  congr 1
  ext x
  simp only [mem_filter, mem_univ, true_and, mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h; exact ⟨h i (Or.inl rfl), h j (Or.inr rfl)⟩
  · rintro ⟨hi, hj⟩ l (rfl | rfl)
    · exact hi
    · exact hj

/-
## Part II: The two layers in terms of degrees
-/

/-- An element of degree `0` is one lying in no set. -/
theorem deg_eq_zero_iff (A : ι → Finset α) (x : α) : deg A x = 0 ↔ ∀ i, x ∉ A i := by
  rw [deg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact ⟨fun h i => h (mem_univ i), fun h i _ => h i⟩

/-- Double counting: `Σ_i |A i| = Σ_x deg x`. -/
theorem sum_card_eq_sum_deg (A : ι → Finset α) :
    ∑ i : ι, ((A i).card : ℤ) = ∑ x : α, (deg A x : ℤ) := by
  have hA : ∀ i, ((A i).card : ℤ) = ∑ x : α, (if x ∈ A i then (1 : ℤ) else 0) := by
    intro i
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hd : ∀ x, (deg A x : ℤ) = ∑ i : ι, (if x ∈ A i then (1 : ℤ) else 0) := by
    intro x
    rw [Finset.sum_boole, deg]
  simp_rw [hA, hd]
  rw [Finset.sum_comm]

/-- `S₁` is the first inclusion–exclusion layer. -/
theorem S1_eq_sieveLayer (A : ι → Finset α) : S1 A = sieveLayer A 1 := by
  rw [S1, sum_card_eq_sum_deg, sieveLayer_eq_sum_choose]
  simp [Nat.choose_one_right]

/-- The zeroth layer is the size of the whole universe. -/
theorem sieveLayer_zero (A : ι → Finset α) : sieveLayer A 0 = (Fintype.card α : ℤ) := by
  rw [sieveLayer_eq_sum_choose]
  simp only [Nat.choose_zero_right, Nat.cast_one]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The second truncated sieve equals `|α| − S₁ + S₂`. -/
theorem bonf_two_eq (A : ι → Finset α) :
    bonf A 2 = (Fintype.card α : ℤ) - S1 A + S2 A := by
  have h : bonf A 2 = sieveLayer A 0 - sieveLayer A 1 + sieveLayer A 2 := by
    rw [bonf, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  rw [h, sieveLayer_zero, ← S1_eq_sieveLayer, S2]

/-- The union and the no-set elements partition the universe. -/
theorem unionSet_card_add_noneCard (A : ι → Finset α) :
    (unionSet A).card + noneCard A = Fintype.card α := by
  have hnone : noneCard A = (univ.filter (fun x => ¬ (0 < deg A x))).card := by
    unfold noneCard
    congr 1
    apply Finset.filter_congr
    intro x _
    constructor
    · intro h
      simp only [not_lt, Nat.le_zero]
      exact (deg_eq_zero_iff A x).mpr h
    · intro h
      rw [not_lt, Nat.le_zero] at h
      exact (deg_eq_zero_iff A x).mp h
  rw [hnone, unionSet, Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_univ]

/-
## Part III: The exact Bonferroni defect
-/

/-- The per-element truncation error at `m = 2`. An element in no set contributes `0`; an
element of degree `f+1 ≥ 1` contributes `C(f, 2) = C(deg − 1, 2)`. -/
theorem term_two (A : ι → Finset α) (x : α) :
    altPartial (deg A x) 2 - (if deg A x = 0 then (1 : ℤ) else 0)
      = (if deg A x = 0 then (0 : ℤ) else ((deg A x - 1).choose 2 : ℤ)) := by
  rcases Nat.eq_zero_or_pos (deg A x) with h0 | hpos
  · rw [h0, altPartial_zero]; simp
  · obtain ⟨f, hf⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hf, altPartial_succ, if_neg (Nat.succ_ne_zero f), if_neg (Nat.succ_ne_zero f), sub_zero]
    have hfeq : f + 1 - 1 = f := by omega
    rw [hfeq]
    norm_num

/-- **The exact second-Bonferroni defect.** The slack in `|U| ≥ S₁ − S₂` is a single
non-negative sum over the union:

    |U| − (S₁ − S₂)  =  Σ_{x ∈ U} C(deg x − 1, 2).

An element covered `d` times contributes `C(d−1, 2)`, which vanishes precisely when `d ≤ 2`. -/
theorem union_card_sub_eq_gap (A : ι → Finset α) :
    ((unionSet A).card : ℤ) - (S1 A - S2 A)
      = ∑ x ∈ unionSet A, ((deg A x - 1).choose 2 : ℤ) := by
  have hbsn := bonf_sub_noneCard A 2
  rw [Finset.sum_congr rfl (fun x (_ : x ∈ (univ : Finset α)) => term_two A x)] at hbsn
  have hsum : (∑ x : α, (if deg A x = 0 then (0 : ℤ) else ((deg A x - 1).choose 2 : ℤ)))
      = ∑ x ∈ unionSet A, ((deg A x - 1).choose 2 : ℤ) := by
    rw [unionSet, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : deg A x = 0
    · simp [h]
    · have hpos : 0 < deg A x := Nat.pos_of_ne_zero h
      simp [h, hpos]
  rw [hsum] at hbsn
  rw [bonf_two_eq] at hbsn
  have hcard : ((unionSet A).card : ℤ) + (noneCard A : ℤ) = (Fintype.card α : ℤ) := by
    have h := unionSet_card_add_noneCard A
    exact_mod_cast h
  linarith [hbsn, hcard]

/-
## Part IV: The inequality and its sharp tightness criterion
-/

/-- **The second Bonferroni inequality (union form).** `S₁ − S₂ ≤ |U|`, i.e.

    |⋃_i A i|  ≥  Σ_i |A i|  −  Σ_{i<j} |A i ∩ A j|. -/
theorem second_bonferroni (A : ι → Finset α) :
    S1 A - S2 A ≤ ((unionSet A).card : ℤ) := by
  have h := union_card_sub_eq_gap A
  have hnn : 0 ≤ ∑ x ∈ unionSet A, ((deg A x - 1).choose 2 : ℤ) :=
    Finset.sum_nonneg (fun x _ => by positivity)
  linarith [h, hnn]

/-- **Sharp tightness.** The second Bonferroni bound is exact iff every element lies in at
most two of the sets (equivalently, no element is triple-covered). -/
theorem second_bonferroni_eq_iff (A : ι → Finset α) :
    ((unionSet A).card : ℤ) = S1 A - S2 A ↔ ∀ x, deg A x ≤ 2 := by
  rw [← sub_eq_zero, union_card_sub_eq_gap A,
    Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by positivity)]
  constructor
  · intro h x
    by_cases hx : x ∈ unionSet A
    · have hxz : (deg A x - 1).choose 2 = 0 := by exact_mod_cast h x hx
      rw [Nat.choose_eq_zero_iff] at hxz
      omega
    · simp only [unionSet, mem_filter, mem_univ, true_and, not_lt, Nat.le_zero] at hx
      omega
  · intro h x _
    have hxle : deg A x ≤ 2 := h x
    have : (deg A x - 1).choose 2 = 0 := by rw [Nat.choose_eq_zero_iff]; omega
    exact_mod_cast this

/-- The sharp criterion restated geometrically: **all triple intersections are empty.** -/
theorem deg_le_two_iff_no_triple (A : ι → Finset α) :
    (∀ x, deg A x ≤ 2) ↔
      ∀ i j k : ι, i ≠ j → i ≠ k → j ≠ k → A i ∩ A j ∩ A k = ∅ := by
  constructor
  · intro h i j k hij hik hjk
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨x, hx⟩
    rw [Finset.mem_inter, Finset.mem_inter] at hx
    obtain ⟨⟨hi, hj⟩, hk⟩ := hx
    have hsub : ({i, j, k} : Finset ι) ⊆ univ.filter (fun l => x ∈ A l) := by
      intro l hl
      simp only [mem_filter, mem_univ, true_and]
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hi
      rcases Finset.mem_insert.mp hl with rfl | hl
      · exact hj
      · rw [Finset.mem_singleton] at hl; subst hl; exact hk
    have hcard3 : ({i, j, k} : Finset ι).card = 3 :=
      Finset.card_eq_three.mpr ⟨i, j, k, hij, hik, hjk, rfl⟩
    have h3 : 3 ≤ deg A x := by
      rw [deg, ← hcard3]; exact Finset.card_le_card hsub
    have := h x; omega
  · intro h x
    by_contra hgt
    push_neg at hgt
    rw [deg] at hgt
    obtain ⟨i, j, k, hi, hj, hk, hij, hik, hjk⟩ := Finset.two_lt_card_iff.mp hgt
    rw [mem_filter] at hi hj hk
    have hempty : A i ∩ A j ∩ A k = ∅ := h i j k hij hik hjk
    have hx : x ∈ A i ∩ A j ∩ A k := by
      rw [Finset.mem_inter, Finset.mem_inter]; exact ⟨⟨hi.2, hj.2⟩, hk.2⟩
    rw [hempty] at hx
    exact absurd hx (Finset.not_mem_empty x)

/-- The same criterion as the vanishing of the third inclusion–exclusion layer. -/
theorem deg_le_two_iff_sieveLayer_three (A : ι → Finset α) :
    (∀ x, deg A x ≤ 2) ↔ sieveLayer A 3 = 0 := by
  rw [sieveLayer_eq_sum_choose, Finset.sum_eq_zero_iff_of_nonneg (fun x _ => by positivity)]
  constructor
  · intro h x _
    have : (deg A x).choose 3 = 0 := by rw [Nat.choose_eq_zero_iff]; have := h x; omega
    exact_mod_cast this
  · intro h x
    have hx : (deg A x).choose 3 = 0 := by exact_mod_cast h x (mem_univ x)
    rw [Nat.choose_eq_zero_iff] at hx
    omega

/-
## Part V: Disjointness is sufficient but not necessary
-/

/-- **Disjointness is sufficient.** A pairwise-disjoint family makes the second Bonferroni
bound exact (then `S₂ = 0` and `|U| = S₁`). -/
theorem disjoint_imp_tight (A : ι → Finset α)
    (h : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    ((unionSet A).card : ℤ) = S1 A - S2 A := by
  rw [second_bonferroni_eq_iff]
  intro x
  by_contra hgt
  push_neg at hgt
  rw [deg] at hgt
  obtain ⟨i, j, _, hi, hj, _, hij, _, _⟩ := Finset.two_lt_card_iff.mp hgt
  rw [mem_filter] at hi hj
  exact (Finset.disjoint_left.mp (h i j hij) hi.2) hj.2

/-
## Part VI: A concrete witness that disjointness is *not* necessary

The family `A 0 = {0,1}`, `A 1 = {1,2}` over `Fin 3` overlaps in the point `1`, so it is not
disjoint; yet every point has degree ≤ 2, so the second Bonferroni bound is exact:
`|U| = 3`, `S₁ = 4`, `S₂ = 1`, and `3 = 4 − 1`. All checked by `decide` (axiom-free).
-/

/-- The overlapping example family `A 0 = {0,1}`, `A 1 = {1,2}` over `Fin 3`. -/
def exFam : Fin 2 → Finset (Fin 3) := fun i => if i = 0 then {0, 1} else {1, 2}

/-- The two sets are **not** disjoint — they share the point `1`. -/
example : ¬ Disjoint (exFam 0) (exFam 1) := by decide

/-- The shared point has degree `2`. -/
example : deg exFam (1 : Fin 3) = 2 := by decide

/-- Despite the overlap, the second Bonferroni bound is **exact**: `|U| = S₁ − S₂` (`3 = 4 − 1`). -/
example : ((unionSet exFam).card : ℤ) = S1 exFam - S2 exFam := by decide

#check @second_bonferroni
#check @union_card_sub_eq_gap
#check @second_bonferroni_eq_iff
#check @deg_le_two_iff_no_triple
#check @disjoint_imp_tight

end InclusionExclusionSecondBonferroni

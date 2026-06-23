import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

/-
# Higher Bonferroni Inequalities for an Arbitrary Finite Set Family

## What This Proves
Let `A : ι → Finset α` be a finite family of finite sets (so `ι` and `α` are finite). The
classical inclusion–exclusion principle computes the number of elements lying in **none** of
the sets,

    noneCard A  =  Σ_{J ⊆ ι} (-1)^|J| · |⋂_{i ∈ J} A i|        (⋂ over ∅ = the whole universe).

The **higher Bonferroni inequalities** assert that truncating this alternating sieve after the
size-`m` index sets,

    bonf A m  :=  Σ_{k=0}^m (-1)^k · S_k,        S_k := Σ_{|J| = k} |⋂_{i ∈ J} A i|,

brackets the true count alternately from above and below as `m` grows:

    m even  ⟹  noneCard A ≤ bonf A m      (truncating after a `+` layer over-counts)
    m odd   ⟹  bonf A m ≤ noneCard A      (truncating after a `-` layer under-counts)

Equivalently, the single signed statement `(-1)^m · (bonf A m − noneCard A) ≥ 0` holds for
every truncation index `m`, and the bound becomes exact once `m ≥ |ι|`.

## Proof Strategy (per-element reindexing)
The whole argument reduces to a **pointwise** fact. For an element `x`, let
`deg A x = #{i : x ∈ A i}` be the number of sets containing `x`. A size-`k` index set `J`
contributes `x` to the layer `S_k` exactly when `J ⊆ {i : x ∈ A i}`, and the number of such
size-`k` index sets is `C(deg A x, k)`. Exchanging the order of summation (`Finset.sum_comm`)
collapses the family `A` entirely, leaving only element degrees:

    bonf A m  =  Σ_{x}  altPartial (deg A x) m ,    altPartial f m := Σ_{j=0}^m (-1)^j C(f, j).

The partial alternating binomial sum is pinned by Pascal telescoping:

    altPartial 0 m = 1,            altPartial (f+1) m = (-1)^m · C(f, m).

An element in *no* set has `deg = 0` and contributes `altPartial 0 m = 1`, reproducing
`noneCard A` exactly; an element with `deg = f+1 ≥ 1` contributes the single signed term
`(-1)^m C(f, m)`. Hence

    bonf A m − noneCard A  =  (-1)^m · Σ_{x : deg ≥ 1} C(deg A x − 1, m) ,

whose sign is `(-1)^m` because binomial coefficients are non-negative. The inequalities follow,
and at `m ≥ |ι| ≥ deg A x` every `C(deg − 1, m)` vanishes, giving the exact sieve.

## Relationship to the Gallery
This is the **general theorem** of which the gallery derangement-Bonferroni file
`InclusionExclusionSieveDerangementsBonferroni` (slug `inclusion-exclusion-oq-04-oq-01-oq-02`)
is the instance `A i = {σ : σ i = i}`: the per-element reindexing here mirrors that file's
per-permutation reindexing exactly, with `x ↔ σ` and `deg A x ↔ #fixed points`. Mathlib has the
*exact* inclusion–exclusion identity but no truncated / one-sided Bonferroni bound on the count
of elements in no set of a general finite family.

## Status
- [x] Complete proof, no `sorry`, no `axiom`.
- [x] No `native_decide`; the worked example uses `decide`, so the file is axiom-free.
-/

namespace InclusionExclusionBonferroniGeneral

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-
## Part I: The partial alternating binomial sum

`altPartial f m = Σ_{j=0}^m (-1)^j C(f,j)` is the truncated binomial expansion of `(1-1)^f`.
Two facts drive everything:

* `altPartial 0 m = 1`           (the empty "containing index set" contributes the full `+1`);
* `altPartial (f+1) m = (-1)^m C(f,m)`  (Pascal telescoping — sign `(-1)^m`, magnitude ≥ 0).
-/

/-- The partial alternating binomial sum `Σ_{j=0}^m (-1)^j · C(f, j)` (over `ℤ`). -/
def altPartial (f m : ℕ) : ℤ := ∑ j ∈ Finset.range (m + 1), (-1 : ℤ) ^ j * (f.choose j : ℤ)

/-- With `f = 0` only the `j = 0` term survives, giving `1`. -/
theorem altPartial_zero (m : ℕ) : altPartial 0 m = 1 := by
  unfold altPartial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hj)]
    simp
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h

/-- **Pascal telescoping.** For a positive upper index `f+1`, the partial alternating
binomial sum collapses to a single signed term:

    Σ_{j=0}^m (-1)^j · C(f+1, j)  =  (-1)^m · C(f, m).

Proved by induction on `m` using Pascal's rule `C(f+1,m+1) = C(f,m) + C(f,m+1)`. -/
theorem altPartial_succ (f m : ℕ) : altPartial (f + 1) m = (-1 : ℤ) ^ m * (f.choose m : ℤ) := by
  induction m with
  | zero => simp [altPartial]
  | succ m ih =>
      unfold altPartial at ih ⊢
      rw [Finset.sum_range_succ, ih]
      have hpascal : ((f + 1).choose (m + 1) : ℤ) = (f.choose m : ℤ) + (f.choose (m + 1) : ℤ) := by
        have := Nat.choose_succ_succ f m
        exact_mod_cast this
      rw [hpascal, pow_succ]
      ring

/-- Once the truncation index reaches the upper binomial index, the partial alternating sum is
the exact indicator of `f = 0`: `altPartial f m = [f = 0]` whenever `f ≤ m`. This is the
endpoint that turns the Bonferroni bound into the exact inclusion–exclusion identity. -/
theorem altPartial_of_le {f m : ℕ} (h : f ≤ m) :
    altPartial f m = (if f = 0 then (1 : ℤ) else 0) := by
  rcases Nat.eq_zero_or_pos f with h0 | hpos
  · rw [h0, altPartial_zero]; simp
  · obtain ⟨g, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [altPartial_succ, if_neg (Nat.succ_ne_zero g),
      Nat.choose_eq_zero_of_lt (by omega : g < m)]
    simp

/-
## Part II: Layers, the truncated sieve, and per-element reindexing

`interCard A J = |⋂_{i ∈ J} A i|` is the number of elements lying in every set indexed by `J`
(with `J = ∅` giving the whole universe). `sieveLayer A k = Σ_{|J| = k} interCard A J` is the
`k`-th inclusion–exclusion layer `S_k`, and `bonf A m = Σ_{k=0}^m (-1)^k S_k` is the sieve
truncated after layer `m`.
-/

/-- `deg A x` is the number of sets in the family that contain `x`. -/
def deg (A : ι → Finset α) (x : α) : ℕ := (univ.filter (fun i => x ∈ A i)).card

/-- `interCard A J = |⋂_{i ∈ J} A i|`, the number of elements contained in every `A i` for
`i ∈ J` (the empty intersection is the whole universe). -/
def interCard (A : ι → Finset α) (J : Finset ι) : ℕ :=
  (univ.filter (fun x : α => ∀ i ∈ J, x ∈ A i)).card

/-- The `k`-th inclusion–exclusion layer `S_k = Σ_{|J| = k} |⋂_{i ∈ J} A i|` (over `ℤ`). -/
def sieveLayer (A : ι → Finset α) (k : ℕ) : ℤ :=
  ∑ J ∈ (univ : Finset ι).powersetCard k, (interCard A J : ℤ)

/-- The truncated inclusion–exclusion sieve `bonf A m = Σ_{k=0}^m (-1)^k · S_k` (over `ℤ`). -/
def bonf (A : ι → Finset α) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * sieveLayer A k

/-- The number of elements lying in **none** of the sets of the family. -/
def noneCard (A : ι → Finset α) : ℕ := (univ.filter (fun x : α => ∀ i, x ∉ A i)).card

/-- For a fixed element `x`, the size-`k` index sets `J` all of whose sets contain `x` are
exactly the size-`k` subsets of the "containing set" `{i : x ∈ A i}`. -/
private theorem filter_subset_eq_powersetCard (A : ι → Finset α) (x : α) (k : ℕ) :
    ((univ : Finset ι).powersetCard k).filter (fun J => ∀ i ∈ J, x ∈ A i)
      = (univ.filter (fun i => x ∈ A i)).powersetCard k := by
  ext J
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, hmem⟩
    refine ⟨?_, hcard⟩
    intro i hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hmem i hi⟩
  · rintro ⟨hsub, hcard⟩
    refine ⟨⟨Finset.subset_univ J, hcard⟩, ?_⟩
    intro i hi
    have h := hsub hi
    rw [Finset.mem_filter] at h
    exact h.2

/-- **Layer count.** Each layer is a sum over elements of a single binomial coefficient:
`S_k = Σ_x C(deg A x, k)`. A size-`k` index set contributes `x` to `S_k` iff it is contained in
the `deg A x` indices whose set contains `x`. -/
theorem sieveLayer_eq_sum_choose (A : ι → Finset α) (k : ℕ) :
    sieveLayer A k = ∑ x : α, ((deg A x).choose k : ℤ) := by
  unfold sieveLayer deg
  have h1 : ∀ J ∈ (univ : Finset ι).powersetCard k,
      (interCard A J : ℤ) = ∑ x : α, (if (∀ i ∈ J, x ∈ A i) then (1 : ℤ) else 0) := by
    intro J _
    unfold interCard
    rw [Finset.card_filter]
    push_cast
    simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter, Finset.sum_const, filter_subset_eq_powersetCard,
    Finset.card_powersetCard, nsmul_eq_mul, mul_one]

/-- **Per-element reindexing.** The truncated sieve equals the sum over elements of their
partial alternating binomial sums: `bonf A m = Σ_x altPartial (deg A x) m`. -/
theorem bonf_eq_sum_altPartial (A : ι → Finset α) (m : ℕ) :
    bonf A m = ∑ x : α, altPartial (deg A x) m := by
  unfold bonf
  simp_rw [sieveLayer_eq_sum_choose, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [altPartial]

/-- The count of elements in no set, as an indicator sum: `noneCard A = Σ_x [deg A x = 0]`. -/
theorem noneCard_eq_indicator_sum (A : ι → Finset α) :
    (noneCard A : ℤ) = ∑ x : α, (if deg A x = 0 then (1 : ℤ) else 0) := by
  have hfilter : (univ.filter (fun x : α => deg A x = 0))
      = univ.filter (fun x : α => ∀ i, x ∉ A i) := by
    apply Finset.filter_congr
    intro x _
    unfold deg
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · intro h i; exact h (Finset.mem_univ i)
    · intro h i _; exact h i
  unfold noneCard
  rw [← hfilter, Finset.card_filter]
  push_cast
  simp

/-
## Part III: The Bonferroni inequalities

`bonf A m − noneCard A` is a sum over elements whose `x`-term is
`altPartial (deg A x) m − [deg A x = 0]`. For an element in no set this is `1 − 1 = 0`; for an
element in `f+1 ≥ 1` sets it is `(-1)^m · C(f, m)`. In both cases the term, multiplied by
`(-1)^m`, is non-negative — hence so is the whole sum.
-/

/-- The signed truncation error is a single sum over elements. -/
theorem bonf_sub_noneCard (A : ι → Finset α) (m : ℕ) :
    bonf A m - (noneCard A : ℤ)
      = ∑ x : α, (altPartial (deg A x) m - (if deg A x = 0 then (1 : ℤ) else 0)) := by
  rw [bonf_eq_sum_altPartial, noneCard_eq_indicator_sum, ← Finset.sum_sub_distrib]

/-- **Key sign lemma.** Each element's contribution to the truncation error, multiplied by
`(-1)^m`, is non-negative: an element in no set contributes `0`, and an element in `f+1 ≥ 1`
sets contributes `C(f, m) ≥ 0`. -/
theorem neg_one_pow_mul_term_nonneg (A : ι → Finset α) (x : α) (m : ℕ) :
    0 ≤ (-1 : ℤ) ^ m * (altPartial (deg A x) m - (if deg A x = 0 then (1 : ℤ) else 0)) := by
  rcases Nat.eq_zero_or_pos (deg A x) with h0 | hpos
  · rw [h0, altPartial_zero]; simp
  · obtain ⟨f, hf⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hf, altPartial_succ, if_neg (Nat.succ_ne_zero f), sub_zero]
    have hsq : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
    have : (-1 : ℤ) ^ m * ((-1 : ℤ) ^ m * (f.choose m : ℤ)) = (f.choose m : ℤ) := by
      rw [← mul_assoc, hsq, one_mul]
    rw [this]; positivity

/-- **Core non-negativity.** `(-1)^m · (bonf A m − noneCard A) ≥ 0` for every truncation `m`. -/
theorem neg_one_pow_mul_bonf_sub_nonneg (A : ι → Finset α) (m : ℕ) :
    0 ≤ (-1 : ℤ) ^ m * (bonf A m - (noneCard A : ℤ)) := by
  rw [bonf_sub_noneCard, Finset.mul_sum]
  exact Finset.sum_nonneg (fun x _ => neg_one_pow_mul_term_nonneg A x m)

/-- **Bonferroni upper bound.** Truncating the sieve after an *even*-size layer over-counts the
elements in no set: `noneCard A ≤ Σ_{k=0}^m (-1)^k S_k`. -/
theorem bonferroni_even (A : ι → Finset α) {m : ℕ} (hm : Even m) :
    (noneCard A : ℤ) ≤ bonf A m := by
  have h := neg_one_pow_mul_bonf_sub_nonneg A m
  rw [hm.neg_one_pow, one_mul] at h
  linarith

/-- **Bonferroni lower bound.** Truncating the sieve after an *odd*-size layer under-counts the
elements in no set: `Σ_{k=0}^m (-1)^k S_k ≤ noneCard A`. -/
theorem bonferroni_odd (A : ι → Finset α) {m : ℕ} (hm : Odd m) :
    bonf A m ≤ (noneCard A : ℤ) := by
  have h := neg_one_pow_mul_bonf_sub_nonneg A m
  rw [hm.neg_one_pow] at h
  linarith

/-
## Part IV: The exact endpoint

Each element belongs to at most `|ι|` sets, so once `m ≥ |ι|` every binomial error term
`C(deg − 1, m)` vanishes and the truncated sieve becomes the exact inclusion–exclusion count.
-/

/-- An element belongs to at most `|ι|` of the sets. -/
theorem deg_le_card (A : ι → Finset α) (x : α) : deg A x ≤ Fintype.card ι := by
  unfold deg
  calc (univ.filter (fun i => x ∈ A i)).card
      ≤ (univ : Finset ι).card := Finset.card_filter_le _ _
    _ = Fintype.card ι := Finset.card_univ

/-- **Exact inclusion–exclusion.** Once the truncation reaches the size of the index family,
the sieve is exact: `bonf A m = noneCard A` for `m ≥ |ι|`. This is the `m = |ι|` endpoint of
the Bonferroni ladder. -/
theorem bonf_eq_noneCard_of_card_le (A : ι → Finset α) {m : ℕ} (hm : Fintype.card ι ≤ m) :
    bonf A m = (noneCard A : ℤ) := by
  rw [bonf_eq_sum_altPartial, noneCard_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [altPartial_of_le (le_trans (deg_le_card A x) hm)]

/-
## Part V: Concrete check (axiom-free)

Take `ι = Fin 2`, `α = Fin 4`, with `A 0 = {0,1}` and `A 1 = {1,2}`. Degrees are
`deg 0 = 1, deg 1 = 2, deg 2 = 1, deg 3 = 0`, so element `3` lies in no set: `noneCard = 1`.
The layers are `S_0 = 4, S_1 = 4, S_2 = 1`, giving the Bonferroni ladder

    bonf 0 = 4  ≥  noneCard = 1  ≥  bonf 1 = 0,        bonf 2 = 1 = noneCard.

Upper bound at even `m`, lower bound at odd `m`, exact at `m = |ι| = 2`. All values are checked
by `decide` (no `native_decide`), so the file is axiom-free.
-/

/-- The example family `A 0 = {0,1}`, `A 1 = {1,2}` over `Fin 4`. -/
def exFamily : Fin 2 → Finset (Fin 4) := fun i => if i = 0 then {0, 1} else {1, 2}

example : noneCard exFamily = 1 := by decide
example : bonf exFamily 0 = 4 := by decide
example : bonf exFamily 1 = 0 := by decide
example : bonf exFamily 2 = 1 := by decide

/-- The even truncation `bonf 0 = 4` is an upper bound for `noneCard = 1`. -/
example : (noneCard exFamily : ℤ) ≤ bonf exFamily 0 :=
  bonferroni_even exFamily (by decide)

/-- The odd truncation `bonf 1 = 0` is a lower bound for `noneCard = 1`. -/
example : bonf exFamily 1 ≤ (noneCard exFamily : ℤ) :=
  bonferroni_odd exFamily (by decide)

#check @bonferroni_even
#check @bonferroni_odd
#check @bonf_eq_sum_altPartial
#check @bonf_eq_noneCard_of_card_le
#check @altPartial_succ

end InclusionExclusionBonferroniGeneral

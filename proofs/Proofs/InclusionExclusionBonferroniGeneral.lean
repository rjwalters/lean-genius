import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-
# Higher Bonferroni Inequalities for a General Finite Set Family

## What This Proves
Let `A : ι → Finset α` be an arbitrary finite family of finite sets over a finite
universe `α` (with `ι` a finite index type). The **inclusion–exclusion sieve sum**

    Σ_{k=0}^N (-1)^k · S_k,      S_k := Σ_{|J|=k} |⋂_{i∈J} A i|   (S_0 = |α|)

equals the number of elements lying in **none** of the sets `A i`. The **higher
Bonferroni inequalities** state that *truncating* this alternating sum at level `m`
gives a one-sided estimate of that count, with direction governed by the parity of `m`:

    m even  ⟹  noneCard A ≤ bonf A m      (truncating after a `+` layer over-counts)
    m odd   ⟹  bonf A m ≤ noneCard A      (truncating after a `-` layer under-counts)

Equivalently, the single signed statement `(-1)^m · (bonf A m − noneCard A) ≥ 0`
holds for every truncation level `m`. At `m ≥ |ι|` the truncation is the full sieve and
the two sides coincide (the exact inclusion–exclusion principle).

## Proof Strategy (pointwise / per-element reindexing)
This is the *general* form behind the gallery's derangement-specific Bonferroni file
(`InclusionExclusionSieveDerangementsBonferroni`, which is the special case
`A i = {σ : σ i = i}`). The argument is purely combinatorial and element-by-element.

For each `x : α` let `deg A x := #{i : x ∈ A i}` be the number of sets containing `x`.
A size-`k` index set `J` contributes `x` to `S_k` exactly when `J ⊆ {i : x ∈ A i}`, so

    S_k = Σ_{x} C(deg A x, k),

and exchanging the order of summation (`Finset.sum_comm`) turns the truncated sieve into

    bonf A m = Σ_{x} altPartial (deg A x) m,      altPartial f m := Σ_{j=0}^m (-1)^j C(f,j).

The partial alternating binomial sum collapses by Pascal's rule:

    altPartial 0 m = 1,        altPartial (f+1) m = (-1)^m · C(f, m).

An element in no set has `deg = 0`, contributing `altPartial 0 m = 1`; every element in at
least one set has `deg = f+1 ≥ 1` and contributes the single signed term `(-1)^m C(f,m)`.
Hence

    bonf A m − noneCard A = (-1)^m · Σ_{x : deg ≥ 1} C(deg A x − 1, m),

whose sign is `(-1)^m` since binomial coefficients are non-negative. The inequalities follow.

## Why This Is Not Already in the Gallery / Mathlib
Mathlib has the *exact* inclusion–exclusion identity but no truncated / Bonferroni
one-sided bound. The gallery has the Bonferroni bracketing only for the derangement sieve;
this file proves it for an **arbitrary** finite family of sets — the general higher
Bonferroni inequalities — self-contained and axiom-free.
-/

namespace InclusionExclusionBonferroniGeneral

open Finset

variable {α : Type*} {ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-! ## Part I: The partial alternating binomial sum

`altPartial f m = Σ_{j=0}^m (-1)^j C(f,j)`, the alternating binomial sum truncated at `m`.
These two collapse lemmas are the only number-theoretic input to the whole argument. -/

/-- The alternating binomial sum truncated after the size-`m` term. -/
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

    Σ_{j=0}^m (-1)^j · C(f+1, j)  =  (-1)^m · C(f, m). -/
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

/-- For `m ≥ f` the partial alternating sum is the full alternating sum, which is the
indicator of `f = 0`. (Used for the exact-sieve consistency check.) -/
theorem altPartial_of_le {f m : ℕ} (hfm : f ≤ m) :
    altPartial f m = if f = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos f with h0 | hpos
  · rw [h0, altPartial_zero]; simp
  · obtain ⟨g, hg⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    subst hg
    rw [altPartial_succ, if_neg (Nat.succ_ne_zero g),
      Nat.choose_eq_zero_of_lt (Nat.lt_of_succ_le hfm)]
    simp

/-! ## Part II: The family, its degrees, and the truncated sieve -/

/-- `deg A x` is the number of sets in the family `A` that contain `x`. -/
def deg (A : ι → Finset α) (x : α) : ℕ := (univ.filter (fun i => x ∈ A i)).card

/-- `S_k = Σ_{|J|=k} |⋂_{i∈J} A i|`, the `k`-th sieve layer.  The intersection over `J` is
recorded as the set of `x` lying in `A i` for every `i ∈ J`; for `J = ∅` this is all of `α`. -/
def sieveLayer (A : ι → Finset α) (k : ℕ) : ℤ :=
  ∑ J ∈ (univ : Finset ι).powersetCard k,
    ((univ.filter (fun x : α => ∀ i ∈ J, x ∈ A i)).card : ℤ)

/-- The inclusion–exclusion sieve sum truncated after the size-`m` layer:
`bonf A m = Σ_{k=0}^m (-1)^k S_k`. -/
def bonf (A : ι → Finset α) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * sieveLayer A k

/-- The number of elements lying in **none** of the sets `A i`. -/
def noneCard (A : ι → Finset α) : ℕ := (univ.filter (fun x : α => ∀ i, x ∉ A i)).card

/-! ## Part III: The per-element reindexing

`bonf A m = Σ_{x} altPartial (deg A x) m`: each element contributes the partial alternating
binomial sum of the number of sets containing it. -/

/-- For a fixed element `x`, the size-`k` index sets `J` all of whose members contain `x` are
exactly the size-`k` subsets of `{i : x ∈ A i}`. -/
private theorem filter_forall_eq_powersetCard (A : ι → Finset α) (x : α) (k : ℕ) :
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

/-- **Reindexing.** Exchanging the order of summation, the truncated sieve becomes a sum over
elements: `bonf A m = Σ_x altPartial (deg A x) m`. -/
theorem bonf_eq_sum_altPartial (A : ι → Finset α) (m : ℕ) :
    bonf A m = ∑ x : α, altPartial (deg A x) m := by
  unfold bonf sieveLayer
  -- each layer's `|⋂|` is an indicator sum over `x`
  have hcard : ∀ J : Finset ι,
      ((univ.filter (fun x : α => ∀ i ∈ J, x ∈ A i)).card : ℤ)
        = ∑ x : α, (if (∀ i ∈ J, x ∈ A i) then (1 : ℤ) else 0) := by
    intro J
    rw [Finset.card_filter]
    push_cast
    simp
  -- push the sign in, expand, and bring the `x`-sum outside
  have hstep : ∀ k ∈ Finset.range (m + 1),
      ((-1 : ℤ) ^ k * ∑ J ∈ (univ : Finset ι).powersetCard k,
            ((univ.filter (fun x : α => ∀ i ∈ J, x ∈ A i)).card : ℤ))
        = ∑ x : α,
            ∑ J ∈ (univ : Finset ι).powersetCard k,
              (if (∀ i ∈ J, x ∈ A i) then (-1 : ℤ) ^ k else 0) := by
    intro k _hk
    rw [Finset.mul_sum, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J _hJ
    rw [hcard J, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  -- for each `x`, collapse the inner double sum to `altPartial (deg A x) m`
  apply Finset.sum_congr rfl
  intro x _hx
  unfold altPartial deg
  apply Finset.sum_congr rfl
  intro k _hk
  -- on `powersetCard k`, `|J| = k`, so the sign is the constant `(-1)^k`
  have hsign : ∀ J ∈ (univ : Finset ι).powersetCard k,
      (if (∀ i ∈ J, x ∈ A i) then (-1 : ℤ) ^ k else 0)
        = (-1 : ℤ) ^ k * (if (∀ i ∈ J, x ∈ A i) then (1 : ℤ) else 0) := by
    intro J _hJ; split <;> simp
  rw [Finset.sum_congr rfl hsign, ← Finset.mul_sum]
  congr 1
  -- `Σ_{J ∈ powersetCard k} [J ⊆ deg-set x] = #(deg-set x).powersetCard k = C(deg A x, k)`
  rw [← Finset.sum_filter, Finset.sum_const, filter_forall_eq_powersetCard,
    Finset.card_powersetCard, nsmul_eq_mul, mul_one]

/-! ## Part IV: The Bonferroni inequalities -/

/-- `noneCard A` as an indicator sum over the universe: `x` is in no set iff `deg A x = 0`. -/
theorem noneCard_eq_indicator_sum (A : ι → Finset α) :
    (noneCard A : ℤ) = ∑ x : α, (if deg A x = 0 then (1 : ℤ) else 0) := by
  unfold noneCard
  have hfilter : (univ.filter (fun x : α => deg A x = 0))
      = univ.filter (fun x : α => ∀ i, x ∉ A i) := by
    apply Finset.filter_congr
    intro x _
    unfold deg
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · intro h i; exact h (Finset.mem_univ i)
    · intro h i _; exact h i
  rw [← hfilter, Finset.card_filter]
  push_cast
  simp

/-- The signed truncation error is a single sum over the universe. -/
theorem bonf_sub_noneCard (A : ι → Finset α) (m : ℕ) :
    bonf A m - (noneCard A : ℤ)
      = ∑ x : α, (altPartial (deg A x) m - (if deg A x = 0 then (1 : ℤ) else 0)) := by
  rw [bonf_eq_sum_altPartial, noneCard_eq_indicator_sum, ← Finset.sum_sub_distrib]

/-- **Key sign lemma.** Each element's contribution to the truncation error, multiplied by
`(-1)^m`, is non-negative: an element in no set contributes `0`, and one in `f+1 ≥ 1` sets
contributes `C(f, m) ≥ 0`. -/
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

/-- **Core non-negativity.** `(-1)^m · (bonf A m − noneCard A) ≥ 0` for every truncation
level `m`. -/
theorem neg_one_pow_mul_bonf_sub_nonneg (A : ι → Finset α) (m : ℕ) :
    0 ≤ (-1 : ℤ) ^ m * (bonf A m - (noneCard A : ℤ)) := by
  rw [bonf_sub_noneCard, Finset.mul_sum]
  exact Finset.sum_nonneg (fun x _ => neg_one_pow_mul_term_nonneg A x m)

/-- **Bonferroni upper bound.** Truncating the sieve after an *even* layer over-counts the
number of elements in no set: `noneCard A ≤ Σ_{k=0}^m (-1)^k S_k`. -/
theorem bonferroni_even (A : ι → Finset α) {m : ℕ} (hm : Even m) :
    (noneCard A : ℤ) ≤ bonf A m := by
  have h := neg_one_pow_mul_bonf_sub_nonneg A m
  rw [hm.neg_one_pow, one_mul] at h
  linarith

/-- **Bonferroni lower bound.** Truncating the sieve after an *odd* layer under-counts the
number of elements in no set: `Σ_{k=0}^m (-1)^k S_k ≤ noneCard A`. -/
theorem bonferroni_odd (A : ι → Finset α) {m : ℕ} (hm : Odd m) :
    bonf A m ≤ (noneCard A : ℤ) := by
  have h := neg_one_pow_mul_bonf_sub_nonneg A m
  rw [hm.neg_one_pow] at h
  linarith

/-! ## Part V: Consistency with the exact inclusion–exclusion principle

For `m ≥ |ι|` every `deg A x ≤ |ι| ≤ m`, so each `altPartial (deg A x) m` is the full
alternating sum `[deg A x = 0]`, and the truncated sieve recovers `noneCard A` exactly. -/

/-- The degree of any element is at most the number of indices. -/
theorem deg_le_card (A : ι → Finset α) (x : α) : deg A x ≤ Fintype.card ι := by
  unfold deg
  calc (univ.filter (fun i => x ∈ A i)).card ≤ (univ : Finset ι).card :=
        Finset.card_filter_le _ _
    _ = Fintype.card ι := Finset.card_univ

/-- **Exact inclusion–exclusion.** Once the truncation reaches the number of indices, the
truncated sieve equals the true count of elements in no set: `bonf A m = noneCard A` for
`m ≥ |ι|`. -/
theorem bonf_eq_noneCard_of_card_le (A : ι → Finset α) {m : ℕ} (hm : Fintype.card ι ≤ m) :
    bonf A m = (noneCard A : ℤ) := by
  rw [bonf_eq_sum_altPartial, noneCard_eq_indicator_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact altPartial_of_le (le_trans (deg_le_card A x) hm)

end InclusionExclusionBonferroniGeneral

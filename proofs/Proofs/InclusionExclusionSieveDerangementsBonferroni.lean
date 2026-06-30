import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import Proofs.InclusionExclusionSieveDerangements

/-
# Bonferroni Inequalities for the Derangement Sieve

## What This Proves
The parent file `InclusionExclusionSieveDerangements` derives the **exact** sieve form of
the derangement count,

    D_n  =  Σ_{k=0}^n (-1)^k · C(n,k) · (n-k)!.

This file proves the corresponding **Bonferroni inequalities**: the *truncated* sieve sums

    B(n,m)  :=  Σ_{k=0}^m (-1)^k · C(n,k) · (n-k)!        (0 ≤ m ≤ n)

bracket the true count `D_n`, alternately from above and below as `m` increases:

    m even  ⟹  D_n ≤ B(n,m)          (truncating after a `+` term over-counts)
    m odd   ⟹  B(n,m) ≤ D_n          (truncating after a `-` term under-counts)

This is the prototypical Bonferroni phenomenon for inclusion–exclusion: stopping the
alternating sieve early gives a one-sided estimate whose direction is the parity of the
last index included. Equivalently, the single signed statement

    (-1)^m · (B(n,m) - D_n)  ≥  0

holds for every `m`.

## Proof Strategy (per-permutation reindexing)
Each binomial term `C(n,k)(n-k)!` counts pairs `(t, σ)` with `|t| = k`, `t ⊆ Fin n`, and
`σ` a permutation fixing every point of `t` (the crux count `card_fixesOn` from the parent).
Summing the truncated sieve and exchanging the order of summation (`Finset.sum_comm`),

    B(n,m)  =  Σ_{σ ∈ Perm (Fin n)}  A(f_σ, m),     A(f, m) := Σ_{j=0}^m (-1)^j C(f, j),

where `f_σ = #{i : σ i = i}` is the number of fixed points of `σ`. The partial alternating
binomial sum collapses by Pascal's rule:

    A(0, m) = 1,            A(f+1, m) = (-1)^m · C(f, m).

A derangement is exactly a `σ` with `f_σ = 0`, contributing `A(0,m) = 1`; so the derangements
reproduce `D_n`, and every *non*-derangement contributes the single signed term
`(-1)^m C(f_σ - 1, m)`. Hence

    B(n,m) - D_n  =  (-1)^m · Σ_{σ : f_σ ≥ 1} C(f_σ - 1, m)  ,

whose sign is `(-1)^m` because the binomial coefficients are non-negative. The inequalities
follow.

## Why This Is Not Already in the Gallery / Mathlib
Mathlib has the *exact* inclusion–exclusion identity (`Finset.inclusion_exclusion_*`) but no
truncated / Bonferroni one-sided bound. The parent gallery file proves the exact derangement
sieve; the alternating *bracketing* by partial sums — the quantitative content of Bonferroni
— is proved here for the first time in the gallery.

## Status
- [x] Complete proof, no `sorry`, no `axiom`
- [x] No `native_decide`; worked examples use `decide`, so the file is axiom-free.
-/

namespace InclusionExclusionSieveDerangementsBonferroni

open Equiv Finset
open InclusionExclusionSieveDerangements

variable {n : ℕ}

/-
## Part I: The partial alternating binomial sum

`altPartial f m = Σ_{j=0}^m (-1)^j C(f,j)` is the truncated binomial expansion of `(1-1)^f`.
Two facts drive everything:

* `altPartial 0 m = 1`           (the empty "bad set" contributes the full `+1`);
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

/-
## Part II: The truncated sieve and its per-permutation reindexing

`truncSieve n m` is the alternating sieve sum truncated after the size-`m` subsets,

    B(n,m)  =  Σ_{k=0}^m (-1)^k · C(n,k) · (n-k)!.

We first rewrite it as a double sum over subsets `t` with `|t| ≤ m` (each binomial term
`C(n,k)(n-k)!` is `Σ_{|t|=k}` of the crux count `card_fixesOn t = (n-|t|)!`), then exchange
the order of summation to land on `Σ_σ altPartial (f_σ) m`.
-/

/-- `fixCard σ` is the number of fixed points of the permutation `σ`. -/
def fixCard (σ : Perm (Fin n)) : ℕ := (univ.filter (fun i => σ i = i)).card

/-- The truncated sieve sum `B(n,m) = Σ_{k=0}^m (-1)^k · C(n,k) · (n-k)!` over `ℤ`. -/
def truncSieve (n m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) * ((n - k).factorial : ℤ)

/-- Cardinality of the set of permutations fixing every point of `t`, as the crux count. -/
private theorem card_fixesOn_int (t : Finset (Fin n)) :
    ((univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ t, σ i = i)).card : ℤ)
      = ((n - t.card).factorial : ℤ) := by
  rw [card_fixesOn t]

/-- **Step 1 — subset form.** Each truncated binomial term is the sum over size-`k`
subsets `t` of the signed crux count `(-1)^|t| · #{σ fixing t}`. -/
theorem truncSieve_eq_subset_sum (n m : ℕ) :
    truncSieve n m =
      ∑ k ∈ Finset.range (m + 1),
        ∑ t ∈ (univ : Finset (Fin n)).powersetCard k,
          (-1 : ℤ) ^ t.card
            * ((univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ t, σ i = i)).card : ℤ) := by
  unfold truncSieve
  apply Finset.sum_congr rfl
  intro k _hk
  have hconst : ∀ t ∈ (univ : Finset (Fin n)).powersetCard k,
      (-1 : ℤ) ^ t.card
          * ((univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ t, σ i = i)).card : ℤ)
        = (-1 : ℤ) ^ k * ((n - k).factorial : ℤ) := by
    intro t ht
    have htk : t.card = k := (Finset.mem_powersetCard.mp ht).2
    rw [card_fixesOn_int, htk]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- For a fixed permutation `σ`, the subsets of `Fin n` all of whose points `σ` fixes are
exactly the subsets of the fixed-point set `Fix σ = {i : σ i = i}`. -/
private theorem filter_subset_eq_powersetCard (σ : Perm (Fin n)) (k : ℕ) :
    ((univ : Finset (Fin n)).powersetCard k).filter
        (fun t => ∀ i ∈ t, σ i = i)
      = (univ.filter (fun i => σ i = i)).powersetCard k := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨_, hcard⟩, hfix⟩
    refine ⟨?_, hcard⟩
    intro i hi
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ i, hfix i hi⟩
  · rintro ⟨hsub, hcard⟩
    refine ⟨⟨Finset.subset_univ t, hcard⟩, ?_⟩
    intro i hi
    have h := hsub hi
    rw [Finset.mem_filter] at h
    exact h.2

/-- **Step 2 — Fubini.** Exchanging the order of summation in the subset form, the truncated
sieve equals `Σ_σ altPartial (fixCard σ) m`: each permutation `σ` contributes the partial
alternating binomial sum of its number of fixed points. -/
theorem truncSieve_eq_sum_altPartial (n m : ℕ) :
    truncSieve n m = ∑ σ : Perm (Fin n), altPartial (fixCard σ) m := by
  rw [truncSieve_eq_subset_sum]
  -- expand the crux count as a sum of indicators over σ
  have hcard : ∀ (t : Finset (Fin n)),
      ((univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ t, σ i = i)).card : ℤ)
        = ∑ σ : Perm (Fin n), (if (∀ i ∈ t, σ i = i) then (1 : ℤ) else 0) := by
    intro t
    rw [Finset.card_filter]
    push_cast
    simp
  -- rewrite each summand and push the sign inside the σ-sum
  have hstep : ∀ k ∈ Finset.range (m + 1),
      (∑ t ∈ (univ : Finset (Fin n)).powersetCard k,
          (-1 : ℤ) ^ t.card
            * ((univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ t, σ i = i)).card : ℤ))
        = ∑ σ : Perm (Fin n),
            ∑ t ∈ (univ : Finset (Fin n)).powersetCard k,
              (if (∀ i ∈ t, σ i = i) then (-1 : ℤ) ^ t.card else 0) := by
    intro k _hk
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _ht
    rw [hcard t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _hσ
    rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  -- now: Σ_σ Σ_k Σ_{t ∈ powersetCard k} (if t ⊆ Fix σ then (-1)^|t| else 0) = Σ_σ altPartial ..
  apply Finset.sum_congr rfl
  intro σ _hσ
  unfold altPartial fixCard
  apply Finset.sum_congr rfl
  intro k _hk
  -- on powersetCard k, |t| = k, so the sign is the constant (-1)^k; collect the indicators
  have hsign : ∀ t ∈ (univ : Finset (Fin n)).powersetCard k,
      (if (∀ i ∈ t, σ i = i) then (-1 : ℤ) ^ t.card else 0)
        = (-1 : ℤ) ^ k * (if (∀ i ∈ t, σ i = i) then (1 : ℤ) else 0) := by
    intro t ht
    have htk : t.card = k := (Finset.mem_powersetCard.mp ht).2
    rw [htk]; split <;> simp
  rw [Finset.sum_congr rfl hsign, ← Finset.mul_sum]
  congr 1
  -- Σ_{t ∈ powersetCard k} (if t ⊆ Fix σ then 1 else 0) = #(Fix σ).powersetCard k = C(f, k)
  rw [← Finset.sum_filter, Finset.sum_const, filter_subset_eq_powersetCard,
    Finset.card_powersetCard, nsmul_eq_mul, mul_one]

/-
## Part III: Derangements are the `f = 0` contribution

A permutation is a derangement iff it has no fixed point, i.e. `fixCard σ = 0`. The
derangement count is therefore the indicator sum `Σ_σ [fixCard σ = 0]`, and `altPartial 0 m = 1`
shows these terms reproduce `D_n` exactly inside `Σ_σ altPartial (fixCard σ) m`.
-/

/-- The permutations with no fixed point are exactly the derangements: their count is
`numDerangements n`. (This mirrors the parent's `card_avoid_eq_numDerangements`, phrased as a
filter cardinality.) -/
theorem card_deranged_filter (n : ℕ) :
    (univ.filter (fun σ : Perm (Fin n) => ∀ i, σ i ≠ i)).card = numDerangements n := by
  rw [← Fintype.card_subtype (fun σ : Perm (Fin n) => ∀ i, σ i ≠ i)]
  have hd : Fintype.card (derangements (Fin n)) = numDerangements n := by
    rw [card_derangements_eq_numDerangements, Fintype.card_fin]
  rw [← hd]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun _ => Iff.rfl))

/-- The derangement count as an indicator sum over all permutations. -/
theorem numDerangements_eq_indicator_sum (n : ℕ) :
    (numDerangements n : ℤ) = ∑ σ : Perm (Fin n), (if fixCard σ = 0 then (1 : ℤ) else 0) := by
  have hfilter : (univ.filter (fun σ : Perm (Fin n) => fixCard σ = 0))
      = univ.filter (fun σ : Perm (Fin n) => ∀ i, σ i ≠ i) := by
    apply Finset.filter_congr
    intro σ _
    unfold fixCard
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    constructor
    · intro h i; exact h (Finset.mem_univ i)
    · intro h i _; exact h i
  rw [← card_deranged_filter, ← hfilter, Finset.card_filter]
  push_cast
  simp

/-
## Part IV: The Bonferroni inequalities

`truncSieve n m - D_n` is a sum over permutations whose `σ`-term is
`altPartial (fixCard σ) m - [fixCard σ = 0]`. For derangements this is `1 - 1 = 0`; for a
permutation with `f_σ = f+1 ≥ 1` fixed points it is `(-1)^m · C(f, m)`. In both cases the term,
multiplied by `(-1)^m`, is non-negative — hence so is the whole sum.
-/

/-- The signed truncation error is a single sum over permutations. -/
theorem truncSieve_sub_numDerangements (n m : ℕ) :
    truncSieve n m - (numDerangements n : ℤ)
      = ∑ σ : Perm (Fin n),
          (altPartial (fixCard σ) m - (if fixCard σ = 0 then (1 : ℤ) else 0)) := by
  rw [truncSieve_eq_sum_altPartial, numDerangements_eq_indicator_sum, ← Finset.sum_sub_distrib]

/-- **Key sign lemma.** Each permutation's contribution to the truncation error, multiplied
by `(-1)^m`, is non-negative: a derangement contributes `0`, and a permutation with
`f+1 ≥ 1` fixed points contributes `C(f,m) ≥ 0`. -/
theorem neg_one_pow_mul_term_nonneg (σ : Perm (Fin n)) (m : ℕ) :
    0 ≤ (-1 : ℤ) ^ m * (altPartial (fixCard σ) m - (if fixCard σ = 0 then (1 : ℤ) else 0)) := by
  rcases Nat.eq_zero_or_pos (fixCard σ) with h0 | hpos
  · rw [h0, altPartial_zero]; simp
  · obtain ⟨f, hf⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hf, altPartial_succ, if_neg (Nat.succ_ne_zero f), sub_zero]
    have hsq : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
    have : (-1 : ℤ) ^ m * ((-1 : ℤ) ^ m * (f.choose m : ℤ)) = (f.choose m : ℤ) := by
      rw [← mul_assoc, hsq, one_mul]
    rw [this]; positivity

/-- **Core non-negativity.** `(-1)^m · (B(n,m) - D_n) ≥ 0` for every truncation index `m`. -/
theorem neg_one_pow_mul_truncSieve_sub_nonneg (n m : ℕ) :
    0 ≤ (-1 : ℤ) ^ m * (truncSieve n m - (numDerangements n : ℤ)) := by
  rw [truncSieve_sub_numDerangements, Finset.mul_sum]
  exact Finset.sum_nonneg (fun σ _ => neg_one_pow_mul_term_nonneg σ m)

/-- **Bonferroni upper bound.** Truncating the derangement sieve after an *even*-size layer
over-counts: `D_n ≤ Σ_{k=0}^m (-1)^k C(n,k)(n-k)!`. -/
theorem bonferroni_even (n : ℕ) {m : ℕ} (hm : Even m) :
    (numDerangements n : ℤ) ≤ truncSieve n m := by
  have h := neg_one_pow_mul_truncSieve_sub_nonneg n m
  rw [hm.neg_one_pow, one_mul] at h
  linarith

/-- **Bonferroni lower bound.** Truncating the derangement sieve after an *odd*-size layer
under-counts: `Σ_{k=0}^m (-1)^k C(n,k)(n-k)! ≤ D_n`. -/
theorem bonferroni_odd (n : ℕ) {m : ℕ} (hm : Odd m) :
    truncSieve n m ≤ (numDerangements n : ℤ) := by
  have h := neg_one_pow_mul_truncSieve_sub_nonneg n m
  rw [hm.neg_one_pow] at h
  linarith

/-- **Consistency.** At `m = n` the truncation is the full sieve, recovering the exact count
`B(n,n) = D_n` (the parent's `numDerangements_eq_sieve_sum`). -/
theorem truncSieve_self (n : ℕ) : truncSieve n n = (numDerangements n : ℤ) :=
  (numDerangements_eq_sieve_sum n).symm

/-
## Part V: Concrete check (axiom-free)

For `n = 4` (`D_4 = 9`) the truncated sieves form the Bonferroni ladder

    B(4,0)=24 ≥ B(4,2)=12 ≥ D_4=9 ≥ B(4,3)=8 ≥ B(4,1)=0,

upper bounds at even `m`, lower bounds at odd `m`. All values are checked with `norm_num`
(no `native_decide`), so the file is axiom-free.
-/

example : truncSieve 4 0 = 24 := by decide
example : truncSieve 4 1 = 0 := by decide
example : truncSieve 4 2 = 12 := by decide
example : truncSieve 4 3 = 8 := by decide

/-- `D_4 = 9`, obtained from the full sieve `B(4,4)`. -/
example : (numDerangements 4 : ℤ) = 9 := by
  rw [← truncSieve_self]; decide

/-- The even truncation `B(4,2) = 12` is indeed an upper bound for `D_4 = 9`. -/
example : (numDerangements 4 : ℤ) ≤ truncSieve 4 2 :=
  bonferroni_even 4 (by decide)

/-- The odd truncation `B(4,3) = 8` is indeed a lower bound for `D_4 = 9`. -/
example : truncSieve 4 3 ≤ (numDerangements 4 : ℤ) :=
  bonferroni_odd 4 (by decide)

#check @bonferroni_even
#check @bonferroni_odd
#check @truncSieve_eq_sum_altPartial
#check @altPartial_succ

end InclusionExclusionSieveDerangementsBonferroni

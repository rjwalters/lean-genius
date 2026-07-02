/-
# Bonferroni Inequalities

Truncating the inclusion–exclusion series for the cardinality of a finite union
of finite sets at an **odd** number of terms *overestimates* the true
cardinality, and at an **even** number of terms *underestimates* it.

This resolves the standing TODO in Mathlib's
`Mathlib/Combinatorics/Enumerative/InclusionExclusion.lean`:

> Prove that truncating the series alternatively gives an upper/lower bound to
> the true value.

## Strategy

The engine is a *partial* alternating binomial identity that Mathlib does not
yet contain (it only has the full sum `Int.alternating_sum_range_choose`):
`∑_{k=0}^{m} (-1)^k C(n+1, k) = (-1)^m C(n, m)`.

Fix an element `a` lying in exactly `N ≥ 1` of the sets. The truncated
inclusion–exclusion value *at `a`* is
`∑_{k=1}^{m} (-1)^{k+1} C(N, k) = 1 - (-1)^m C(N-1, m)`,
which is `≥ 1` for odd `m` (overestimate) and `≤ 1` for even `m`
(underestimate). Summing this pointwise bound over all elements of the union,
the count of size-`k` subsets whose intersection contains `a` becomes
`C(N, k)` (via `Finset.card_powersetCard`), yielding the set-level inequalities.
-/
import Mathlib

open Finset

namespace Bonferroni

/-! ## Part 1: the partial alternating binomial identity -/

/-- **Partial alternating sum of binomial coefficients.**
`∑_{k=0}^{m} (-1)^k C(n+1, k) = (-1)^m C(n, m)`.

Writing the top argument as `n + 1` (rather than a hypothesis `1 ≤ n`) sidesteps
natural-number subtraction. Mathlib only provides the *full* sum
(`Int.alternating_sum_range_choose`); this is the truncated version. -/
theorem alternating_sum_range_choose_partial (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * ((n + 1).choose k) =
      (-1) ^ m * (n.choose m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' n m]
    push_cast
    ring

/-- The truncated inclusion–exclusion value carried by a single element that
lies in `n + 1` of the sets:
`∑_{k=1}^{m} (-1)^{k+1} C(n+1, k) = 1 - (-1)^m C(n, m)`. -/
theorem bonferroni_pointwise (n m : ℕ) :
    ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (k + 1) * ((n + 1).choose k) =
      1 - (-1) ^ m * (n.choose m) := by
  have h1 := alternating_sum_range_choose_partial n m
  have hsplit : Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert (by simp)] at h1
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
  -- h1 : 1 + ∑ k ∈ Icc 1 m, (-1)^k * C(n+1,k) = (-1)^m * C(n,m)
  have hIcc : ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ k * ((n + 1).choose k) =
      (-1) ^ m * (n.choose m) - 1 := by linear_combination h1
  calc ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (k + 1) * ((n + 1).choose k)
      = ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) * ((-1) ^ k * ((n + 1).choose k)) := by
        apply Finset.sum_congr rfl; intro k _; rw [pow_succ]; ring
    _ = (-1) * ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ k * ((n + 1).choose k) := by
        rw [← Finset.mul_sum]
    _ = 1 - (-1) ^ m * (n.choose m) := by rw [hIcc]; ring

/-- Odd truncation overestimates at the level of a single element. -/
theorem bonferroni_pointwise_odd (n m : ℕ) (hm : Odd m) :
    (1 : ℤ) ≤ ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (k + 1) * ((n + 1).choose k) := by
  rw [bonferroni_pointwise, hm.neg_one_pow]
  have : (0 : ℤ) ≤ (n.choose m) := Nat.cast_nonneg _
  linarith

/-- Even truncation underestimates at the level of a single element. -/
theorem bonferroni_pointwise_even (n m : ℕ) (hm : Even m) :
    ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (k + 1) * ((n + 1).choose k) ≤ 1 := by
  rw [bonferroni_pointwise, hm.neg_one_pow]
  have : (0 : ℤ) ≤ (n.choose m) := Nat.cast_nonneg _
  linarith

/-! ## Part 2: aggregation to the cardinality of a union -/

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- The number of elements of the union `⋃_{i∈s} S i` that lie in every `S i`
for `i ∈ t`. For a nonempty `t ⊆ s` this is exactly `#(⋂_{i∈t} S i)`; phrasing
it via a filter over the union avoids `Finset.inf'` bookkeeping. -/
def interCard (s : Finset ι) (S : ι → Finset α) (t : Finset ι) : ℕ :=
  ((s.biUnion S).filter (fun a => ∀ i ∈ t, a ∈ S i)).card

/-- The truncated inclusion–exclusion sum for `#(⋃_{i∈s} S i)`, keeping subsets
of size `1 … m`:
`∑_{k=1}^{m} (-1)^{k+1} ∑_{t ⊆ s, |t|=k} #(⋂_{i∈t} S i)`. -/
def truncIE (s : Finset ι) (S : ι → Finset α) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 m,
    (-1) ^ (k + 1) * ∑ t ∈ s.powersetCard k, (interCard s S t : ℤ)

/-- The multiplicity of an element `a`: the number of sets `S i`, `i ∈ s`, that
contain it. -/
def mult (s : Finset ι) (S : ι → Finset α) (a : α) : ℕ :=
  (s.filter (fun i => a ∈ S i)).card

/-- **Counting lemma.** For a fixed element `a`, the number of size-`k` subsets
`t ⊆ s` all of whose sets contain `a` is `C(mult a, k)`. -/
theorem card_powersetCard_filter (s : Finset ι) (S : ι → Finset α) (a : α) (k : ℕ) :
    ((s.powersetCard k).filter (fun t => ∀ i ∈ t, a ∈ S i)).card =
      (mult s S a).choose k := by
  rw [mult, ← Finset.card_powersetCard]
  congr 1
  ext t
  simp only [Finset.mem_filter, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨hts, hcard⟩, hall⟩
    refine ⟨?_, hcard⟩
    intro x hx
    exact Finset.mem_filter.2 ⟨hts hx, hall x hx⟩
  · rintro ⟨hsub, hcard⟩
    refine ⟨⟨?_, hcard⟩, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.1 (hsub hx)).1
    · intro x hx
      exact (Finset.mem_filter.1 (hsub hx)).2

/-- The counting lemma in `if-then-else` (indicator) form. -/
theorem sum_powersetCard_boole (s : Finset ι) (S : ι → Finset α) (a : α) (k : ℕ) :
    ∑ t ∈ s.powersetCard k, (if (∀ i ∈ t, a ∈ S i) then (1 : ℤ) else 0) =
      ((mult s S a).choose k : ℤ) := by
  rw [Finset.sum_boole, card_powersetCard_filter]

/-- The truncated inclusion–exclusion sum equals the sum over elements of the
union of their pointwise truncated values. -/
theorem truncIE_eq_sum_over_union (s : Finset ι) (S : ι → Finset α) (m : ℕ) :
    truncIE s S m =
      ∑ a ∈ s.biUnion S,
        ∑ k ∈ Finset.Icc 1 m, (-1) ^ (k + 1) * ((mult s S a).choose k : ℤ) := by
  -- Rewrite each interCard as a sum of indicators over the union.
  have hcard : ∀ t : Finset ι, (interCard s S t : ℤ) =
      ∑ a ∈ s.biUnion S, (if (∀ i ∈ t, a ∈ S i) then (1 : ℤ) else 0) := by
    intro t; rw [interCard, ← Finset.sum_boole]
  -- First rewrite `truncIE` with the outer sum ranging over `k` then `a`.
  have step1 : truncIE s S m =
      ∑ k ∈ Finset.Icc 1 m, ∑ a ∈ s.biUnion S,
        (-1) ^ (k + 1) * ((mult s S a).choose k : ℤ) := by
    unfold truncIE
    apply Finset.sum_congr rfl
    intro k _
    have hR : ∑ a ∈ s.biUnion S, (-1 : ℤ) ^ (k + 1) * ((mult s S a).choose k) =
        ∑ a ∈ s.biUnion S, ∑ t ∈ s.powersetCard k,
          (-1) ^ (k + 1) * (if (∀ i ∈ t, a ∈ S i) then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← sum_powersetCard_boole s S a k, Finset.mul_sum]
    rw [Finset.mul_sum, hR, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [hcard t, Finset.mul_sum]
  rw [step1, Finset.sum_comm]

/-- Rewriting `#(⋃ S i)` as a sum of ones over the union. -/
private theorem card_biUnion_eq_sum_ones (s : Finset ι) (S : ι → Finset α) :
    ((s.biUnion S).card : ℤ) = ∑ _a ∈ s.biUnion S, (1 : ℤ) := by
  simp

/-- Every element of the union lies in at least one of the sets. -/
theorem one_le_mult {s : Finset ι} {S : ι → Finset α} {a : α}
    (ha : a ∈ s.biUnion S) : 1 ≤ mult s S a := by
  rw [Finset.mem_biUnion] at ha
  obtain ⟨i, hi, hai⟩ := ha
  rw [mult, Nat.one_le_iff_ne_zero, Finset.card_ne_zero]
  exact ⟨i, Finset.mem_filter.2 ⟨hi, hai⟩⟩

/-! ## Part 3: the Bonferroni inequalities -/

/-- **Bonferroni inequality (odd truncation).** Truncating the inclusion–exclusion
series at an odd number of terms *overestimates* the cardinality of the union. -/
theorem card_biUnion_le_truncIE_odd (s : Finset ι) (S : ι → Finset α) {m : ℕ}
    (hm : Odd m) : ((s.biUnion S).card : ℤ) ≤ truncIE s S m := by
  rw [truncIE_eq_sum_over_union, card_biUnion_eq_sum_ones]
  apply Finset.sum_le_sum
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n, mult s S a = n + 1 :=
    ⟨mult s S a - 1, by have := one_le_mult ha; omega⟩
  rw [hn]
  exact bonferroni_pointwise_odd n m hm

/-- **Bonferroni inequality (even truncation).** Truncating the inclusion–exclusion
series at an even number of terms *underestimates* the cardinality of the union. -/
theorem truncIE_le_card_biUnion_even (s : Finset ι) (S : ι → Finset α) {m : ℕ}
    (hm : Even m) : truncIE s S m ≤ ((s.biUnion S).card : ℤ) := by
  rw [truncIE_eq_sum_over_union, card_biUnion_eq_sum_ones]
  apply Finset.sum_le_sum
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n, mult s S a = n + 1 :=
    ⟨mult s S a - 1, by have := one_le_mult ha; omega⟩
  rw [hn]
  exact bonferroni_pointwise_even n m hm

end Bonferroni

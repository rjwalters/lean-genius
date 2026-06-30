/-
# Erdős Problem #1, OQ-03 (completion): general two-sided bounds on f(n)

Erdős #1 asks about f(n) = the least N such that some n-element set
A ⊆ {0,…,N} has *distinct subset sums* (all 2ⁿ subset sums are different).
The sibling file `Erdos1OQ03.lean` only computes f(n) for the five hardcoded
values n ≤ 5 (via `native_decide`), and the construction-side infrastructure in
`Erdos1WIP01.lean` no longer compiles against current Mathlib.

This file gives a SELF-CONTAINED, working development that bounds f(n) for
*every* n, with the explicit two-sided sandwich

    (2ⁿ − 1)/n  ≤  f(n)  ≤  2^(n−1)        (n ≥ 1).

The lower bound is the classical pigeonhole counting bound (reusing
`erdos_1_counting_bound` from `Erdos1Problem`, which still compiles). The upper
bound is the powers-of-two construction {1,2,4,…,2^(n−1)}, re-derived here in a
working form via a superincreasing-extension lemma.

## Main results

- `dss_insert_of_sum_lt` : superincreasing extension (b > sum A ⟹ insert b A is DSS)
- `powersTwo_dss`        : {2⁰,…,2^(n−1)} has distinct subset sums
- `f` (= sInf of valid bounds), with
  - `f_le_two_pow`      : f n ≤ 2ⁿ
  - `f_le_two_pow_pred` : f n ≤ 2^(n−1)  (n ≥ 1)   [powers-of-two upper bound]
  - `two_pow_le`        : 2ⁿ ≤ n·f n + 1            [counting lower bound]
  - `f_ge`              : (2ⁿ − 1)/n ≤ f n  (n ≥ 1)
  - `f_sandwich`        : the combined two-sided bound
  - `f_one`             : f 1 = 1 (bounds coincide)

## Honest scope

This establishes the *baseline* sandwich. Conway–Guy (1968) improve the upper
bound to ≈ 0.22009·2ⁿ; whether a matching lower bound f(n) ≥ c·2ⁿ holds is the
OPEN $500 Erdős conjecture and is NOT proved here. All results below are fully
machine-checked: 0 sorries, 0 `axiom` declarations.

## References

- Erdős (1955), Problems in additive number theory
- Conway, Guy (1968), upper-bound construction; OEIS A005318
- Dubroff, Fox, Xu (2021), best known lower bound Ω(2ⁿ/√n)
-/

import Proofs.Erdos1Problem
import Mathlib

open Finset

namespace Erdos1OQ03Incomplete01

/- ## §1. Superincreasing extension lemma

   Appending an element larger than the whole current sum preserves DSS. -/

/-- If `A` has distinct subset sums and `b > sum A` with `b ∉ A`, then
    `insert b A` has distinct subset sums. -/
theorem dss_insert_of_sum_lt {A : Finset ℕ} (hA : hasDistinctSubsetSums A)
    {b : ℕ} (hb : A.sum id < b) (hbA : b ∉ A) :
    hasDistinctSubsetSums (insert b A) := by
  -- A subset containing `b` has sum ≥ b > sum A ≥ (sum of any subset of A).
  have key : ∀ S T : Finset ℕ, S ⊆ insert b A → T ⊆ insert b A →
      b ∈ S → b ∉ T → S.sum id ≠ T.sum id := by
    intro S T hS hT hbS hbT
    have hT_sub : T ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp (hT hx) with rfl | hxA
      · exact absurd hx hbT
      · exact hxA
    have hb_le_S : b ≤ S.sum id :=
      Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hbS
    have hT_le : T.sum id ≤ A.sum id := Finset.sum_le_sum_of_subset hT_sub
    omega
  intro S T hS hT heq
  by_cases hbS : b ∈ S <;> by_cases hbT : b ∈ T
  · -- both contain b: erase, use DSS of A, reinsert
    have hSe : S.erase b ⊆ A := by
      intro x hx
      have hxne := Finset.ne_of_mem_erase hx
      rcases Finset.mem_insert.mp (hS (Finset.mem_of_mem_erase hx)) with rfl | hxA
      · exact absurd rfl hxne
      · exact hxA
    have hTe : T.erase b ⊆ A := by
      intro x hx
      have hxne := Finset.ne_of_mem_erase hx
      rcases Finset.mem_insert.mp (hT (Finset.mem_of_mem_erase hx)) with rfl | hxA
      · exact absurd rfl hxne
      · exact hxA
    have hse : (S.erase b).sum id = (T.erase b).sum id := by
      -- normalise every `id`/`.sum id`/`∑ x, id x` to one identity-lambda form
      -- so omega sees consistent atoms, then cancel the shared `b` term.
      have hS' := Finset.add_sum_erase S id hbS
      have hT' := Finset.add_sum_erase T id hbT
      simp only [Function.id_def] at hS' hT' heq ⊢
      omega
    have hEr := hA _ _ hSe hTe hse
    rw [← Finset.insert_erase hbS, ← Finset.insert_erase hbT, hEr]
  · exact absurd heq (key S T hS hT hbS hbT)
  · exact absurd heq.symm (key T S hT hS hbT hbS)
  · -- neither contains b: both subsets of A
    have hS_sub : S ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp (hS hx) with rfl | hxA
      · exact absurd hx hbS
      · exact hxA
    have hT_sub : T ⊆ A := by
      intro x hx
      rcases Finset.mem_insert.mp (hT hx) with rfl | hxA
      · exact absurd hx hbT
      · exact hxA
    exact hA S T hS_sub hT_sub heq

/- ## §2. The powers-of-two construction has distinct subset sums -/

/-- Geometric sum: `(∑_{i<n} 2ⁱ) + 1 = 2ⁿ`. -/
private lemma sum_two_pow_succ (n : ℕ) :
    (∑ i ∈ Finset.range n, (2 : ℕ) ^ i) + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- `{2⁰, 2¹, …, 2^(n−1)}` has distinct subset sums (binary representation). -/
theorem powersTwo_dss (n : ℕ) :
    hasDistinctSubsetSums ((Finset.range n).image (2 ^ · : ℕ → ℕ)) := by
  induction n with
  | zero =>
    intro S T hS hT _
    rw [Finset.range_zero, Finset.image_empty] at hS hT
    rw [Finset.subset_empty.mp hS, Finset.subset_empty.mp hT]
  | succ n ih =>
    rw [Finset.range_add_one, Finset.image_insert]
    apply dss_insert_of_sum_lt ih
    · -- 2ⁿ exceeds the sum of {2⁰,…,2^(n−1)}
      have hsum : ((Finset.range n).image (2 ^ · : ℕ → ℕ)).sum id =
          ∑ i ∈ Finset.range n, (2 : ℕ) ^ i := by
        rw [Finset.sum_image (fun i _ j _ h => Nat.pow_right_injective (by norm_num) h)]
        simp [id_eq]
      rw [hsum]
      have := sum_two_pow_succ n
      omega
    · -- 2ⁿ ∉ {2⁰,…,2^(n−1)}
      intro hmem
      simp only [Finset.mem_image, Finset.mem_range] at hmem
      obtain ⟨i, hi, hEq⟩ := hmem
      have : i = n := Nat.pow_right_injective (by norm_num) hEq
      omega

/- ## §3. The Erdős function f(n) and its two-sided bounds -/

/-- The set of valid bounds: `N` admits an `n`-element DSS set in `{0,…,N}`. -/
def dssBounds (n : ℕ) : Set ℕ :=
  {N | ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a ≤ N) ∧ hasDistinctSubsetSums A}

/-- The powers-of-two set has cardinality `n`. -/
lemma powersTwo_card (n : ℕ) :
    ((Finset.range n).image (2 ^ · : ℕ → ℕ)).card = n := by
  rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (by norm_num : 2 ≤ 2)),
      Finset.card_range]

/-- `2ⁿ` is a valid bound (witnessed by the powers-of-two construction). -/
lemma two_pow_mem_dssBounds (n : ℕ) : 2 ^ n ∈ dssBounds n := by
  refine ⟨(Finset.range n).image (2 ^ · : ℕ → ℕ), powersTwo_card n, ?_, powersTwo_dss n⟩
  intro a ha
  simp only [Finset.mem_image, Finset.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact Nat.pow_le_pow_right (by norm_num) (le_of_lt hi)

lemma dssBounds_nonempty (n : ℕ) : (dssBounds n).Nonempty :=
  ⟨2 ^ n, two_pow_mem_dssBounds n⟩

/-- **f(n)**: the least `N` admitting an `n`-element distinct-subset-sums set in
    `{0,…,N}`. This is the function in Erdős Problem #1. -/
noncomputable def f (n : ℕ) : ℕ := sInf (dssBounds n)

/-- **Upper bound** `f n ≤ 2ⁿ`. -/
theorem f_le_two_pow (n : ℕ) : f n ≤ 2 ^ n :=
  Nat.sInf_le (two_pow_mem_dssBounds n)

/-- **Sharp powers-of-two upper bound** `f n ≤ 2^(n−1)` for `n ≥ 1`: the set
    `{1,2,…,2^(n−1)}` works and has maximum element `2^(n−1)`. -/
theorem f_le_two_pow_pred {n : ℕ} (hn : 1 ≤ n) : f n ≤ 2 ^ (n - 1) := by
  apply Nat.sInf_le
  refine ⟨(Finset.range n).image (2 ^ · : ℕ → ℕ), powersTwo_card n, ?_, powersTwo_dss n⟩
  intro a ha
  simp only [Finset.mem_image, Finset.mem_range] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The minimiser is attained: there is an `n`-element DSS set bounded by `f n`. -/
theorem f_spec (n : ℕ) :
    ∃ A : Finset ℕ, A.card = n ∧ (∀ a ∈ A, a ≤ f n) ∧ hasDistinctSubsetSums A :=
  Nat.sInf_mem (dssBounds_nonempty n)

/-- **Counting lower bound** `2ⁿ ≤ n·f n + 1` (pigeonhole on the `2ⁿ` distinct
    subset sums, all lying in `{0,…,n·f n}`). -/
theorem two_pow_le (n : ℕ) : 2 ^ n ≤ n * f n + 1 := by
  obtain ⟨A, hcard, hbound, hDSS⟩ := f_spec n
  have hcount := erdos_1_counting_bound hbound hDSS
  rwa [hcard] at hcount

/-- **Lower bound** `(2ⁿ − 1)/n ≤ f n` for `n ≥ 1`. -/
theorem f_ge (n : ℕ) (hn : 1 ≤ n) : (2 ^ n - 1) / n ≤ f n := by
  have h := two_pow_le n
  have hge : 2 ^ n - 1 ≤ n * f n := by omega
  calc (2 ^ n - 1) / n
      ≤ (n * f n) / n := Nat.div_le_div_right hge
    _ = f n := Nat.mul_div_cancel_left _ hn

/-- **The two-sided sandwich**: `(2ⁿ − 1)/n ≤ f n ≤ 2^(n−1)` for `n ≥ 1`. -/
theorem f_sandwich {n : ℕ} (hn : 1 ≤ n) :
    (2 ^ n - 1) / n ≤ f n ∧ f n ≤ 2 ^ (n - 1) :=
  ⟨f_ge n hn, f_le_two_pow_pred hn⟩

/-- **f(1) = 1**: the two bounds coincide. -/
theorem f_one : f 1 = 1 := by
  have hu := f_le_two_pow_pred (n := 1) (le_refl 1)
  have hl := f_ge 1 (le_refl 1)
  norm_num at hu hl
  omega

end Erdos1OQ03Incomplete01

/-
# Erdős Problem #124 — the critical case of Brown's criterion

Brown's criterion (formalized in the parent entry `erdos-124-complete-sequences`)
states that a sequence `f : ℕ → ℕ` with `f 0 = 1` and the *small-gap* property

  `f (n+1) ≤ 1 + ∑_{i < n+1} f i`

is *complete*: every natural number is a subset sum `∑_{i ∈ s} f i`.

The follow-up open question for #124 asks what happens *at the boundary* of the
reciprocal-sum condition `∑ 1/(dᵢ - 1) ≥ 1`, i.e. when the sum is exactly `1`.
This file studies the abstract sharp boundary of Brown's criterion itself: the
**critical (tight-gap) case**, where the gap inequality holds with equality.

The results below show the critical case is completely rigid:

* `brown_le_pow2`     — `2^n` is the pointwise upper envelope of *every* Brown
                        sequence with `f 0 = 1`;
* `critical_eq_pow2`  — a sequence with the *tight* gap `f (n+1) = 1 + ∑_{i<n+1} f i`
                        is forced to be exactly `f n = 2^n`;
* `sum_two_pow_injective` / `exists_sum_two_pow` / `unique_representation`
                      — on the critical sequence `2^n` every natural number has a
                        *unique* binary subset-sum representation, so completeness
                        holds with no redundancy at all.

Thus the boundary case of Brown's criterion is exactly binary representation:
maximally efficient (it attains the bound) and rigid (representations are unique),
whereas strictly above the threshold representations become redundant.  The single
base `d = 2` has reciprocal sum `1/(2-1) = 1` and realises this extremal sequence.

This is a self-contained companion to the parent proof: nothing here is imported
from the parent file.  The binary-uniqueness backbone is built on Mathlib's
`Nat.bitIndices` API.
-/

import Mathlib

open Finset

namespace Erdos124OQ02OQ01

/-! ## Geometric sum of powers of two -/

/-- The partial sums of the binary sequence: `∑_{i < n} 2^i = 2^n - 1`. -/
lemma sum_range_two_pow (n : ℕ) : ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-! ## The Brown bound and its critical (tight) case -/

/-- `2^n` is the pointwise upper envelope of every Brown sequence with `f 0 = 1`:
any sequence satisfying the small-gap inequality lies below the binary sequence. -/
theorem brown_le_pow2 {f : ℕ → ℕ} (h0 : f 0 = 1)
    (hgap : ∀ n, f (n + 1) ≤ 1 + ∑ i ∈ Finset.range (n + 1), f i) :
    ∀ n, f n ≤ 2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simp [h0]
    · refine (hgap m).trans ?_
      have hsum : ∑ i ∈ Finset.range (m + 1), f i ≤ ∑ i ∈ Finset.range (m + 1), 2 ^ i :=
        Finset.sum_le_sum (fun i hi => ih i (Finset.mem_range.mp hi))
      rw [sum_range_two_pow] at hsum
      have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      omega

/-- **Rigidity of the critical case.** A sequence with `f 0 = 1` saturating the
Brown gap, `f (n+1) = 1 + ∑_{i < n+1} f i`, is forced to be the binary sequence
`f n = 2^n`.  This is the unique sequence attaining the Brown bound with equality. -/
theorem critical_eq_pow2 {f : ℕ → ℕ} (h0 : f 0 = 1)
    (hgap : ∀ n, f (n + 1) = 1 + ∑ i ∈ Finset.range (n + 1), f i) :
    ∀ n, f n = 2 ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · simpa using h0
    · rw [hgap m]
      have hsum : ∑ i ∈ Finset.range (m + 1), f i = ∑ i ∈ Finset.range (m + 1), 2 ^ i :=
        Finset.sum_congr rfl (fun i hi => ih i (Finset.mem_range.mp hi))
      rw [hsum, sum_range_two_pow]
      have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      omega

/-! ## Uniqueness of binary subset-sum representations

On the critical sequence `2^n`, completeness holds with **no redundancy**: every
natural number is a subset sum in exactly one way (binary representation).  The
backbone is the `Nat.bitIndices` API: `bitIndices` of a binary subset sum recovers
the (sorted) index set, giving injectivity directly. -/

/-- Bridge: a `Finset` sum equals the sum over its sorted list. -/
lemma sum_eq_sortMap (s : Finset ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ s, f i = ((s.sort (· ≤ ·)).map f).sum := by
  rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.sort_eq]
  rfl

/-- The bit-indices of a binary subset sum recover the sorted index set. -/
lemma bitIndices_sum_two_pow (s : Finset ℕ) :
    (∑ i ∈ s, 2 ^ i).bitIndices = s.sort (· ≤ ·) := by
  rw [sum_eq_sortMap s (fun i => 2 ^ i)]
  exact Nat.bitIndices_twoPowsum (Finset.sortedLT_sort s)

/-- **Injectivity.** Distinct index sets give distinct binary subset sums. -/
theorem sum_two_pow_injective :
    Function.Injective (fun s : Finset ℕ => ∑ i ∈ s, 2 ^ i) := by
  intro s t h
  have hsort : s.sort (· ≤ ·) = t.sort (· ≤ ·) := by
    rw [← bitIndices_sum_two_pow s, ← bitIndices_sum_two_pow t]
    exact congrArg Nat.bitIndices h
  have := congrArg List.toFinset hsort
  simpa [Finset.sort_toFinset] using this

/-- **Existence.** Every natural number is a binary subset sum (binary expansion). -/
theorem exists_sum_two_pow (m : ℕ) : ∃ s : Finset ℕ, m = ∑ i ∈ s, 2 ^ i := by
  refine ⟨m.bitIndices.toFinset, ?_⟩
  rw [List.sum_toFinset _ Nat.bitIndices_sorted.nodup]
  exact (Nat.twoPowSum_bitIndices m).symm

/-- **Unique representation in the critical case.** Every natural number has
exactly one binary subset-sum representation: completeness with zero redundancy. -/
theorem unique_representation (m : ℕ) :
    ∃! s : Finset ℕ, m = ∑ i ∈ s, 2 ^ i := by
  obtain ⟨s, hs⟩ := exists_sum_two_pow m
  refine ⟨s, hs, fun t ht => ?_⟩
  exact sum_two_pow_injective (ht.symm.trans hs)

/-! ## The critical sequence, characterised -/

/-- **Sharp boundary of Brown's criterion.** A sequence attaining the Brown gap
with equality (`f 0 = 1`, `f (n+1) = 1 + ∑_{i<n+1} f i`) is exactly `n ↦ 2^n`,
and on it every natural number has a *unique* subset-sum representation. -/
theorem critical_sequence_characterization {f : ℕ → ℕ} (h0 : f 0 = 1)
    (hgap : ∀ n, f (n + 1) = 1 + ∑ i ∈ Finset.range (n + 1), f i) :
    (∀ n, f n = 2 ^ n) ∧ (∀ m, ∃! s : Finset ℕ, m = ∑ i ∈ s, f i) := by
  have hpow := critical_eq_pow2 h0 hgap
  refine ⟨hpow, fun m => ?_⟩
  simp only [hpow]
  exact unique_representation m

/-- The single base `d = 2` has reciprocal sum `1/(2-1) = 1` (the boundary value),
and its greedy power sequence is the critical sequence `n ↦ 2^n`. -/
example : (1 : ℚ) / (2 - 1) = 1 := by norm_num

end Erdos124OQ02OQ01

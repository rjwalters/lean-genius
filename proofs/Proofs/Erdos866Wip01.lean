import Proofs.Erdos866Problem

/-
# Erdős Problem #866 — the uniform parity lower bound `g_k(N) ≥ 1`

## The problem

For `k ≥ 3`, Erdős #866 asks for the minimal threshold `g_k(N)` such that **every**
`A ⊆ {1,…,2N}` with `|A| ≥ N + g_k(N)` contains all pairwise sums `b_i + b_j` of some
`k`-element family `b_1,…,b_k`.  The exact growth of `g_k` is open for every `k ≥ 4`
(known: `g_3 = 2`, `g_4 ≤ 2032`, `g_5 ≍ log N`, `g_6 ≍ √N`).

## What this file proves

The base file `Erdos866Problem.lean` proves `oddNumbers_no_triple`: the `N` odd numbers in
`{1,…,2N}` contain the three pairwise sums of **no** `3`-element family (among any three
integers two share parity, so one pairwise sum is even, hence not odd).  This file turns
that observation into the clean, uniform lower bound it actually establishes:

* `oddNumbers_no_config` — the odd numbers admit **no** `k`-configuration for **any**
  `k ≥ 3` (a `k`-family contains a `3`-subfamily, and the parity obstruction already kills
  that).
* `exists_large_set_without_config` — there is a set `A ⊆ {1,…,2N}` of size `≥ N` with no
  `k`-configuration; so `|A| = N` never forces one.
* `Guarantees` / `not_guarantees_zero` / `g_k_ge_one` — packaging this as the threshold
  statement: a threshold of `0` does **not** guarantee a configuration, i.e. every valid
  threshold satisfies `g_k(N) ≥ 1` for all `k ≥ 3`.

## Honesty / scope

This is the *trivial* lower bound `g_k ≥ 1` — the one the parity construction gives
uniformly in `k`.  It is not the deep content of #866 (the `log N` / `√N` growth for
`k = 5, 6` needs Sidon/multiplicative constructions, and the upper bounds need extremal
arguments — all open or hard).  The contribution here is a fully machine-checked,
axiom-free, `k`-uniform statement of the elementary lower bound, generalizing the base
file's single `k = 3` instance.

Theorems: 5, Axioms: 0, Sorries: 0
-/

open Finset

namespace Erdos866Wip01

open Erdos866

/-- The odd numbers in `{1,…,2N}` form a subset of the interval. -/
theorem oddNumbers_subset (N : ℕ) : oddNumbers N ⊆ Erdos866.Interval N :=
  Finset.filter_subset _ _

/-!
## The uniform parity obstruction

Among any three integers two share parity, so one of their pairwise sums is even and thus
not odd.  Since any `k`-family with `k ≥ 3` contains a 3-subfamily (indices `0, 1, 2`), the
odd numbers contain a full pairwise-sum configuration of no `k`-family.
-/

/-- **Uniform parity lower bound.** For every `k ≥ 3`, the odd numbers in `{1,…,2N}`
contain all pairwise sums of no `k`-element family.

This generalizes `Erdos866.oddNumbers_no_triple` (the `k = 3` case) to all `k ≥ 3`: a
`k`-family with `k ≥ 3` has at least three members, and among the first three two share
parity, forcing one pairwise sum to be even and hence absent from the odd numbers. -/
theorem oddNumbers_no_config (N : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    ¬ ∃ b : Fin k → ℤ, HasAllPairwiseSums (oddNumbers N) b := by
  rintro ⟨b, hb⟩
  -- Every pairwise sum that lands in the odd numbers is odd as a natural number.
  have hodd : ∀ i j : Fin k, i < j → (b i + b j).toNat % 2 = 1 := by
    intro i j hij
    have hmem := hb i j hij
    simp only [oddNumbers, Erdos866.Interval, Finset.mem_filter] at hmem
    exact hmem.2
  -- The three indices `0, 1, 2`, valid because `k ≥ 3`.
  have h01 := hodd ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  have h02 := hodd ⟨0, by omega⟩ ⟨2, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  have h12 := hodd ⟨1, by omega⟩ ⟨2, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
  -- Among `b 0, b 1, b 2` two share parity ⇒ an even sum ⇒ a `% 2 = 0` contradiction.
  omega

/-!
## Threshold reformulation: `g_k(N) ≥ 1`
-/

/-- There is a set `A ⊆ {1,…,2N}` of size at least `N` containing all pairwise sums of no
`k`-element family (for `k ≥ 3`).  The witness is the `N` odd numbers. -/
theorem exists_large_set_without_config (N : ℕ) {k : ℕ} (hk : 3 ≤ k) :
    ∃ A : Finset ℕ, A ⊆ Erdos866.Interval N ∧ N ≤ A.card ∧
      ¬ ∃ b : Fin k → ℤ, HasAllPairwiseSums A b :=
  ⟨oddNumbers N, oddNumbers_subset N, (oddNumbers_card N).ge, oddNumbers_no_config N hk⟩

/-- `Guarantees N k g` means: every `A ⊆ {1,…,2N}` with `|A| ≥ N + g` contains all
pairwise sums of some `k`-element family.  The Erdős threshold `g_k(N)` is the least `g`
with `Guarantees N k g`. -/
def Guarantees (N k g : ℕ) : Prop :=
  ∀ A : Finset ℕ, A ⊆ Erdos866.Interval N → N + g ≤ A.card →
    ∃ b : Fin k → ℤ, HasAllPairwiseSums A b

/-- A threshold of `0` does **not** guarantee a configuration, for any `k ≥ 3`: the `N`
odd numbers are a set of size `N = N + 0` with no `k`-configuration. -/
theorem not_guarantees_zero (N : ℕ) {k : ℕ} (hk : 3 ≤ k) : ¬ Guarantees N k 0 := by
  intro hG
  exact oddNumbers_no_config N hk
    (hG (oddNumbers N) (oddNumbers_subset N) (by simp [oddNumbers_card]))

/-- **`g_k(N) ≥ 1` for all `k ≥ 3`.** Any threshold that actually guarantees a
`k`-configuration must be at least `1`; equivalently, the minimal threshold is positive. -/
theorem g_k_ge_one (N : ℕ) {k g : ℕ} (hk : 3 ≤ k) (hG : Guarantees N k g) : 1 ≤ g := by
  rcases Nat.eq_zero_or_pos g with h | h
  · exact absurd (h ▸ hG) (not_guarantees_zero N hk)
  · exact h

end Erdos866Wip01

import Proofs.ShannonSourceCodingOQ04

/-
# Method of Types: the Type Partition Identity and the Multinomial Theorem

## Context (parent shannon-source-coding-oq-04)

The parent file formalizes the method-of-types proof of Shannon's source coding theorem. It
proves, for an alphabet `Fin k` and block length `n`:

* `type_class_size_eq_multinomial`: `|T_f| = multinomial(f) = n! / ∏(f i)!`;
* `type_class_size_le_entropy_pow`: `|T_f| ≤ exp(n·H(f/n))`;
* `count_types_le`: there are at most `(n+1)^k` distinct types;
* `total_sequences_eq`: there are `k^n` sequences in total.

What the parent never does is **sum over the types**. The whole point of the method of types is
that the type classes *partition* the sequence space, so the `k^n` sequences are accounted for,
class by class. This file supplies that missing identity:

> **`k^n = ∑_{types f} |T_f| = ∑_{types f} multinomial(f)`.**

This is exactly the **multinomial theorem** (`(1 + 1 + ⋯ + 1)^n = k^n`) realized combinatorially
through the empirical-distribution partition. It is the bookkeeping backbone the source coding
argument rests on, and it closes the loop between `total_sequences_eq` and
`type_class_size_eq_multinomial`.

Tags: information-theory, combinatorics, method-of-types, multinomial, partition, source-coding
-/

open Finset BigOperators

namespace ShannonSourceCodingOQ04Incomplete01

open MethodOfTypes

variable {k : ℕ} [NeZero k]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: INDEXING THE TYPES

A type is an empirical distribution: a function `Fin k → ℕ` summing to `n` with each entry
`≤ n`. We index types by `Fin k → Fin (n+1)` (each count lives in `{0,…,n}`) constrained to
sum to `n`. This is precisely the index set behind the parent's `count_types_le`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- Each empirical count is at most the block length `n`. -/
theorem empDist_le (n : ℕ) (x : Fin n → Fin k) (i : Fin k) : empDist n x i ≤ n := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp [Finset.card_univ, Fintype.card_fin]

/-- The set of valid types: `Fin k → Fin (n+1)` whose entries sum to `n`.
    Its cardinality is bounded by `(n+1)^k` (parent's `count_types_le`). -/
def typeIndex (n : ℕ) : Finset (Fin k → Fin (n + 1)) :=
  Finset.univ.filter fun g => ∑ i, (g i : ℕ) = n

/-- The type map sending a sequence to its empirical distribution, valued in `Fin (n+1)`. -/
def typeMap (n : ℕ) (x : Fin n → Fin k) : Fin k → Fin (n + 1) :=
  fun i => ⟨empDist n x i, Nat.lt_succ_of_le (empDist_le n x i)⟩

/-- The type map lands in the type index: empirical counts sum to `n`. -/
theorem typeMap_mem (n : ℕ) (x : Fin n → Fin k) : typeMap n x ∈ typeIndex (k := k) n := by
  simp only [typeIndex, typeMap, Finset.mem_filter, Finset.mem_univ, true_and]
  simpa using empDist_sum n x

/-- A type index `g` recovers a count function summing to `n`. -/
theorem typeIndex_sum {n : ℕ} {g : Fin k → Fin (n + 1)} (hg : g ∈ typeIndex (k := k) n) :
    ∑ i, ((g i : ℕ)) = n := (Finset.mem_filter.mp hg).2

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE FIBER OF THE TYPE MAP IS A TYPE CLASS

The sequences mapping to a given type `g` are exactly the type class `T_{g}`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The fiber of `typeMap` over a type `g` is exactly the type class of `g`. -/
theorem fiber_eq_typeClass (n : ℕ) (g : Fin k → Fin (n + 1)) (hg : ∑ i, ((g i : ℕ)) = n) :
    (Finset.univ.filter fun x : Fin n → Fin k => typeMap n x = g) =
      typeClass n (fun i => (g i : ℕ)) hg := by
  ext x
  simp only [typeClass, typeMap, Finset.mem_filter, Finset.mem_univ, true_and, funext_iff,
    Fin.ext_iff]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE TYPE PARTITION IDENTITY

`k^n = ∑_{types g} |T_g| = ∑_{types g} multinomial(g)`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Type partition (counting form)**: the `k^n` sequences split, class by class, across the
    distinct types — `k^n = ∑_{types g} |T_g|`. The type classes partition the sequence space. -/
theorem total_eq_sum_type_class_card (n : ℕ) :
    (k : ℕ) ^ n =
      ∑ g ∈ typeIndex (k := k) n,
        (Finset.univ.filter fun x : Fin n → Fin k => typeMap n x = g).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n → Fin k))) (t := typeIndex (k := k) n)
    (f := typeMap n) (fun x _ => typeMap_mem n x)
  rwa [total_sequences_eq] at h

/-- **Type partition (multinomial form) = the Multinomial Theorem.**
    `k^n = ∑_{types g} multinomial(g)`. Each type class has multinomial size, and the classes
    partition the `k^n` sequences, so the multinomial coefficients of all types summing to `n`
    add up to `k^n`. This is `(1 + ⋯ + 1)^n = k^n` read through the empirical-distribution
    partition. -/
theorem total_eq_sum_multinomial (n : ℕ) :
    (k : ℕ) ^ n =
      ∑ g ∈ typeIndex (k := k) n, Nat.multinomial Finset.univ (fun i => (g i : ℕ)) := by
  rw [total_eq_sum_type_class_card]
  refine Finset.sum_congr rfl fun g hg => ?_
  rw [fiber_eq_typeClass n g (typeIndex_sum hg), type_class_size_eq_multinomial]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: CONSEQUENCES

A dominant type class is large; and the partition gives a clean alternative route to the
parent's lower bound `k^n / (n+1)^k`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- The number of valid types is at most `(n+1)^k` (the parent's `count_types_le`, restated
    for `typeIndex`). -/
theorem typeIndex_card_le (n : ℕ) : (typeIndex (k := k) n).card ≤ (n + 1) ^ k :=
  count_types_le n

/-- **A dominant type class exists**, via the partition: since `k^n = ∑_{types g} |T_g|` over at
    most `(n+1)^k` types, some type class has at least the average, `k^n ≤ (n+1)^k · |T_g|`.
    This recovers the parent's `dominant_type_lower_bound` directly from the partition identity
    (no separate pigeonhole over sequences needed). -/
theorem exists_dominant_type_class (n : ℕ) :
    ∃ g ∈ typeIndex (k := k) n,
      (k : ℕ) ^ n ≤ (n + 1) ^ k *
        (Finset.univ.filter fun x : Fin n → Fin k => typeMap n x = g).card := by
  by_cases hempty : (typeIndex (k := k) n) = ∅
  · -- impossible: typeMap of any sequence lands in typeIndex, so it is nonempty
    exact absurd (typeMap_mem n (fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩))
      (hempty ▸ Finset.notMem_empty _)
  · obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image (typeIndex (k := k) n)
      (fun g => (Finset.univ.filter fun x : Fin n → Fin k => typeMap n x = g).card)
      (Finset.nonempty_of_ne_empty hempty)
    refine ⟨g, hg, ?_⟩
    calc (k : ℕ) ^ n
        = ∑ g' ∈ typeIndex (k := k) n,
            (Finset.univ.filter fun x : Fin n → Fin k => typeMap n x = g').card :=
          total_eq_sum_type_class_card n
      _ ≤ ∑ _g' ∈ typeIndex (k := k) n,
            (Finset.univ.filter fun x : Fin n → Fin k => typeMap n x = g).card :=
          Finset.sum_le_sum fun g' hg' => hmax g' hg'
      _ = (typeIndex (k := k) n).card *
            (Finset.univ.filter fun x : Fin n → Fin k => typeMap n x = g).card := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (n + 1) ^ k *
            (Finset.univ.filter fun x : Fin n → Fin k => typeMap n x = g).card :=
          Nat.mul_le_mul_right _ (typeIndex_card_le n)

end ShannonSourceCodingOQ04Incomplete01

/-
## Summary

The missing bookkeeping identity of the method of types — the type classes partition the
sequence space:

- `total_eq_sum_type_class_card`: `k^n = ∑_{types g} |T_g|`.
- `total_eq_sum_multinomial`:     `k^n = ∑_{types g} multinomial(g)` — the multinomial theorem
  realized through the empirical-distribution partition.
- `exists_dominant_type_class`:   `∃ g, k^n ≤ (n+1)^k · |T_g|` — the dominant-type lower bound,
  obtained directly from the partition (averaging over ≤ (n+1)^k types).

Built on the parent's `type_class_size_eq_multinomial`, `total_sequences_eq`, and
`count_types_le`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

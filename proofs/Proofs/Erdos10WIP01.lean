import Proofs.Erdos10OQ02
import Proofs.Erdos10OQ02Popcount

/-
# Erdős #10 — WIP: subadditivity of representation and binary popcount

## Context (parent Erdős Problem #10: sums of a prime and powers of 2)

The Erdős–Graham question asks for a constant `k` with every large integer a prime plus at
most `k` powers of 2. The gallery's `Erdos10OQ02` thread built the machinery:

* `RepWithAtMost k n` — `n` is a sum of at most `k` powers of 2;
* `repWithAtMost_iff_repDistinct` — `≤ k` powers ⟺ `≤ k` *distinct* powers (reduction lemma);
* `repWithAtMost_iff_bitIndices_length` — `RepWithAtMost k n ↔ popcount(n) ≤ k`, where
  `popcount(n) = (Nat.bitIndices n).length` is the binary popcount.

This file adds the **additive structure** that thread was missing:

> **`RepWithAtMost` is subadditive**: if `a` needs `≤ j` powers and `b` needs `≤ k`, then
> `a + b` needs `≤ j + k` (`repWithAtMost_add`).

Concatenating the two exponent multisets witnesses it. Feeding the *minimal* representations
(the popcount ones) through this gives, with no extra work, the classical arithmetic fact

> **binary popcount is subadditive**: `popcount(a + b) ≤ popcount(a) + popcount(b)`
> (`bitIndices_length_add_le`),

— a carry-counting statement here proved purely through the powers-of-2 representation lemma.
We close with the prime-plus-popcount characterization `isPrimePlusKPowers_iff_popcount`, the
`O(log)` form of the Erdős #10 predicate that the witness searches (e.g. Grechuk's
`1117175146`) ultimately rest on.

Tags: number-theory, primes, powers-of-two, binary, popcount, additive-combinatorics, erdos
-/

namespace Erdos10WIP01

open Erdos10OQ02

/-- Shorthand for the binary popcount `(Nat.bitIndices n).length`: the minimal number of
    *distinct* powers of two summing to `n`. -/
abbrev popcount (n : ℕ) : ℕ := (Nat.bitIndices n).length

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: SUBADDITIVITY OF REPRESENTATION

Concatenating exponent multisets adds both the term counts and the sums.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Subadditivity of `RepWithAtMost`.** If `a` is a sum of at most `j` powers of two and
    `b` is a sum of at most `k`, then `a + b` is a sum of at most `j + k`: just take the
    union (multiset sum) of the two exponent multisets. -/
theorem repWithAtMost_add {j k a b : ℕ}
    (ha : RepWithAtMost j a) (hb : RepWithAtMost k b) :
    RepWithAtMost (j + k) (a + b) := by
  obtain ⟨s, hs_card, hs_sum⟩ := ha
  obtain ⟨t, ht_card, ht_sum⟩ := hb
  refine ⟨s + t, ?_, ?_⟩
  · rw [Multiset.card_add]; exact Nat.add_le_add hs_card ht_card
  · rw [powSum_add, hs_sum, ht_sum]

/-- A single power of two is a sum of one power of two. -/
theorem repWithAtMost_one_pow (a : ℕ) : RepWithAtMost 1 (2 ^ a) :=
  ⟨{a}, by simp, by simp [powSum]⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: BINARY POPCOUNT IS SUBADDITIVE

The popcount representation is the minimal one; subadditivity of representation passes
straight to subadditivity of popcount.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- Every `n` is a sum of exactly `popcount(n)` distinct powers of two — its binary
    representation. (The `k = popcount n` case of the characterization.) -/
theorem repWithAtMost_popcount (n : ℕ) : RepWithAtMost (popcount n) n :=
  (repWithAtMost_iff_bitIndices_length (popcount n) n).2 le_rfl

/-- `popcount n ≤ k` exactly when `n` is a sum of at most `k` powers of two — the popcount
    is the *minimal* number of powers needed. -/
theorem popcount_le_iff (k n : ℕ) : popcount n ≤ k ↔ RepWithAtMost k n :=
  (repWithAtMost_iff_bitIndices_length k n).symm

/-- **Binary popcount is subadditive**: `popcount(a + b) ≤ popcount(a) + popcount(b)`.

    Proof via representation: `a` is a sum of `popcount(a)` powers and `b` of `popcount(b)`,
    so by `repWithAtMost_add` their sum `a + b` is a sum of `popcount(a) + popcount(b)` powers,
    whence its minimal count `popcount(a + b)` is at most that. The carries in binary addition
    can only *merge* bits (`2^a + 2^a = 2^{a+1}`), never create them. -/
theorem bitIndices_length_add_le (a b : ℕ) :
    popcount (a + b) ≤ popcount a + popcount b :=
  (popcount_le_iff _ _).2 (repWithAtMost_add (repWithAtMost_popcount a) (repWithAtMost_popcount b))

/-- Iterated subadditivity: `popcount(∑ aᵢ) ≤ ∑ popcount(aᵢ)` over a list. -/
theorem bitIndices_length_sum_le (l : List ℕ) :
    popcount l.sum ≤ (l.map popcount).sum := by
  induction l with
  | nil => simp [popcount]
  | cons a t ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (bitIndices_length_add_le a t.sum).trans (Nat.add_le_add_left ih _)

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE PRIME-PLUS-POPCOUNT CHARACTERIZATION

The Erdős #10 predicate in its O(log)-checkable form.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Prime-plus-popcount characterization.** `n` is a prime plus at most `k` powers of two
    iff there is a prime `p ≤ n` whose offset `n − p` has binary popcount at most `k`. This is
    the efficient (`O(log)` per prime) form behind the concrete witness searches for Erdős #10
    (e.g. the smallest even integer needing 3 powers, `906`, and Grechuk's `1117175146`). -/
theorem isPrimePlusKPowers_iff_popcount (k n : ℕ) :
    IsPrimePlusKPowers k n ↔ ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ popcount (n - p) ≤ k := by
  constructor
  · rintro ⟨p, hp, m, hm, rfl⟩
    exact ⟨p, hp, Nat.le_add_right p m,
      by rw [Nat.add_sub_cancel_left]; exact (popcount_le_iff k m).2 hm⟩
  · rintro ⟨p, hp, hpn, hpc⟩
    exact ⟨p, hp, n - p, (popcount_le_iff k (n - p)).1 hpc, by omega⟩

end Erdos10WIP01

/-
## Summary

Adding the additive structure to the Erdős #10 powers-of-two thread:

- `repWithAtMost_add`: `RepWithAtMost` is subadditive — `a` needs `≤ j`, `b` needs `≤ k`
  ⟹ `a + b` needs `≤ j + k` (union of exponent multisets).
- `bitIndices_length_add_le`: **binary popcount is subadditive**,
  `popcount(a + b) ≤ popcount(a) + popcount(b)`, derived purely through the representation
  lemma (carries only merge bits). `bitIndices_length_sum_le` is the list version.
- `isPrimePlusKPowers_iff_popcount`: the Erdős #10 predicate as `∃ prime p ≤ n, popcount(n−p) ≤ k`
  — the `O(log)` form the concrete witness searches rely on.

Built on `Erdos10OQ02` (`RepWithAtMost`, `powSum_add`, `IsPrimePlusKPowers`) and
`Erdos10OQ02Popcount` (`repWithAtMost_iff_bitIndices_length`).

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

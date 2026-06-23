/-
Erdős Problem #1054: Construction D — OQ-01

## The sum-of-divisors function is always representable

The parent file `Erdos1054ConstructionD` proves, case by case via `native_decide`,
that specific values such as `1 + p + p²` (= σ(p²) for a prime `p`) and the Mersenne
numbers `2^{k+1} - 1` (= σ(2^k)) are *representable* — i.e. each appears as a partial
sum of the sorted divisors of some `m ≥ 1`.

This file isolates the **structural reason** behind every one of those verifications
and turns it into a single fully general, axiom-free theorem:

> **For every `m ≥ 1`, the sum of divisors `σ(m) = ∑_{d ∣ m} d` is representable.**

The proof is one observation: the *last* partial sum of the sorted divisor list is the
total sum of all divisors, which is exactly `σ(m)`. Concretely, `partialDivisorSums m`
is the tail of `scanl (·+·) 0 (sortedDivisors m)`, whose last entry equals
`foldl (·+·) 0 (sortedDivisors m) = (sortedDivisors m).sum = σ(m)`.

This subsumes the parent's concrete checks **without** `native_decide` (hence
`Lean.ofReduceBool`-free): the prime-square case is `m = p²`, the Mersenne case is
`m = 2^k`, and we additionally obtain a clean prime-power corollary
`∑_{i=0}^{k} p^i` is representable for every prime `p` and every `k`.

## Results
- `foldl_add_acc`              — accumulator identity `foldl (+) a L = a + L.sum`
- `sortedDivisors_sum`         — `(sortedDivisors m).sum = ∑_{d ∣ m} d`
- `sum_divisors_mem_partialSums` — `σ(m) ∈ partialDivisorSums m` for `m ≥ 1`
- `sum_divisors_representable` — `σ(m)` is representable for every `m ≥ 1`  (headline)
- `geom_sum_representable`     — `∑_{i=0}^{k} p^i` representable for prime `p`
- `prime_sq_sum_representable'` — recovers the parent's `1 + p + p²` case
- `mersenne_representable`     — recovers the Mersenne case `2^{k+1} - 1`
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open Nat Finset

namespace Erdos1054ConstructionDOQ01

-- ============================================================
-- Definitions (mirrored from `Erdos1054ConstructionD` so this file is
-- self-contained; the parent's concrete checks use `native_decide`, which
-- we deliberately avoid here to keep these results `Lean.ofReduceBool`-free).
-- ============================================================

/-- The divisors of `m`, listed in increasing order. -/
def sortedDivisors (m : ℕ) : List ℕ :=
  m.divisors.sort (· ≤ ·)

/-- The running (cumulative) sums of the sorted divisors of `m`. -/
def partialDivisorSums (m : ℕ) : List ℕ :=
  ((sortedDivisors m).scanl (· + ·) 0).tail

/-- `n` is *representable* if it occurs as a partial divisor sum of some `m ≥ 1`. -/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ n ∈ (partialDivisorSums m)

-- ============================================================
-- Part 0: A list-folding helper
-- ============================================================

/--
Folding addition over a list with an arbitrary starting accumulator `a`
just adds `a` to the list's sum.  This lets us identify the final entry of
the `scanl` (which carries the running total) with the list sum.
-/
theorem foldl_add_acc (a : ℕ) (L : List ℕ) : L.foldl (· + ·) a = a + L.sum := by
  induction L generalizing a with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, List.sum_cons]; ring

-- ============================================================
-- Part 1: The sorted divisor list sums to σ(m)
-- ============================================================

/--
The sum of the sorted divisor list of `m` is the sum-of-divisors function `σ(m)`.
The sorted list is a permutation of the divisor finset, so sums agree.
-/
theorem sortedDivisors_sum (m : ℕ) :
    (sortedDivisors m).sum = ∑ d ∈ m.divisors, d := by
  rw [sortedDivisors, (Finset.sort_perm_toList _ _).sum_eq, Finset.sum_toList]

-- ============================================================
-- Part 2: σ(m) is the final partial sum, hence representable
-- ============================================================

/--
**Key lemma.** For every `m ≥ 1`, the sum of divisors `σ(m)` occurs as a partial
sum of the sorted divisors of `m`: it is the *last* such partial sum.
-/
theorem sum_divisors_mem_partialSums (m : ℕ) (hm : 1 ≤ m) :
    (∑ d ∈ m.divisors, d) ∈ partialDivisorSums m := by
  -- Work with the list sum; the divisor finset is nonempty since `1 ∣ m`.
  rw [← sortedDivisors_sum]
  obtain ⟨a, l, hal⟩ : ∃ a l, sortedDivisors m = a :: l := by
    rcases h : sortedDivisors m with _ | ⟨a, l⟩
    · exfalso
      have hlen : (sortedDivisors m).length = m.divisors.card := by
        rw [sortedDivisors, Finset.length_sort]
      rw [h, List.length_nil] at hlen
      have h1 : (1 : ℕ) ∈ m.divisors := Nat.one_mem_divisors.mpr (by omega)
      have := Finset.card_pos.mpr ⟨1, h1⟩
      omega
    · exact ⟨a, l, rfl⟩
  -- Unfold the partial-sum list and reduce to the final `scanl` entry.
  unfold partialDivisorSums
  rw [hal, List.scanl_cons, List.tail_cons]
  -- Goal: `(a :: l).sum ∈ scanl (·+·) (0 + a) l`
  have hne : List.scanl (· + ·) (0 + a) l ≠ [] := List.scanl_ne_nil
  have hmem := List.getLast_mem hne
  rw [List.getLast_scanl hne] at hmem
  have hval : List.foldl (· + ·) (0 + a) l = (a :: l).sum := by
    rw [foldl_add_acc, List.sum_cons]; ring
  rwa [hval] at hmem

/--
**Headline.** The sum-of-divisors function `σ(m) = ∑_{d ∣ m} d` is representable for
every `m ≥ 1` — it is always realised by the witness `m` itself (the largest partial
sum of `m`'s sorted divisors).

This generalises, in one stroke and without `native_decide`, every concrete
representability check in the parent file.
-/
theorem sum_divisors_representable (m : ℕ) (hm : 1 ≤ m) :
    IsRepresentable (∑ d ∈ m.divisors, d) :=
  ⟨m, hm, sum_divisors_mem_partialSums m hm⟩

-- ============================================================
-- Part 3: Corollaries recovering and extending the parent results
-- ============================================================

/--
**Prime-power corollary.** For every prime `p` and every `k`, the geometric sum
`∑_{i=0}^{k} p^i` is representable (witness `m = p^k`).  Indeed it equals `σ(p^k)`.
-/
theorem geom_sum_representable (p k : ℕ) (hp : p.Prime) :
    IsRepresentable (∑ i ∈ Finset.range (k + 1), p ^ i) := by
  have hpk : 1 ≤ p ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k hp.pos.ne')
  have h := sum_divisors_representable (p ^ k) hpk
  rwa [Nat.sum_divisors_prime_pow (f := fun x => x) hp] at h

/--
Recovers the parent's **Construction D** statement: `σ(p²) = 1 + p + p²` is
representable, here as the `k = 2` instance of `geom_sum_representable`.
-/
theorem prime_sq_sum_representable' (p : ℕ) (hp : p.Prime) :
    IsRepresentable (1 + p + p ^ 2) := by
  have h := geom_sum_representable p 2 hp
  -- `∑_{i=0}^{2} p^i = 1 + p + p²`
  simpa [Finset.sum_range_succ, pow_zero, pow_one, add_comm, add_left_comm, add_assoc]
    using h

/--
Recovers the parent's **Mersenne** family: `σ(2^k) = 2^{k+1} - 1` is representable.
We state it in the additive form `∑_{i=0}^{k} 2^i` to avoid `ℕ` subtraction; this is
exactly the Mersenne number `2^{k+1} - 1`.
-/
theorem mersenne_representable (k : ℕ) :
    IsRepresentable (∑ i ∈ Finset.range (k + 1), 2 ^ i) :=
  geom_sum_representable 2 k Nat.prime_two

end Erdos1054ConstructionDOQ01

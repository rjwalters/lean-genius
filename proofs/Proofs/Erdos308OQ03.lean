/-
  Erdős Problem #308 — Open Question 03
  A constructive finiteness argument for f(N) with an explicit harmonic bound

  Parent: Erdos308Problem.lean (Erdős #308: smallest integer f(N) not representable
  as a sum of distinct unit fractions with denominators in {1,…,N}).

  Open Question (erdos-308-oq-03):
  "Can the `sorry` in the existence proof of `f` (the finiteness argument that some
   integer is not representable) be replaced by a constructive bound?"

  Answer (this file): yes, and with an explicit *harmonic* bound. Every representable
  integer k satisfies k ≤ H_N (the N-th harmonic number), because a sum of distinct
  unit fractions with denominators in {1,…,N} is at most the sum of *all* of them.
  Hence ⌊H_N⌋ + 1 is never representable, so the least non-representable integer
  satisfies the explicit, fully constructive bound

      f(N) ≤ ⌊H_N⌋ + 1.

  This sharpens the bare existence witness `N + 1` used in the parent (any unit-fraction
  sum is ≤ N, so N+1 is non-representable) to the much smaller ⌊H_N⌋ + 1, since
  H_N ≤ N gives ⌊H_N⌋ + 1 ≤ N + 1.

  This file is self-contained over Mathlib (it re-states the definitions with current
  import paths; the parent file's `import Mathlib.Data.Rat.Basic` is stale on the
  pinned Mathlib). Status: 0 axioms, 0 sorries — fully machine-checked.

  References:
  - Croot (1999): "On some questions of Erdős and Graham about Egyptian fractions"
  - Erdős–Graham (1980), Problem #308
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Find

open Finset BigOperators
open Classical

namespace Erdos308OQ03

-- ============================================================
-- Part I: Definitions (unit fractions, harmonic number, representability)
-- ============================================================

/-- Sum of unit fractions over a finite set of denominators: `∑_{n ∈ S} 1/n`. -/
def sumUnitFracs (S : Finset ℕ) : ℚ := ∑ n ∈ S, (1 : ℚ) / n

/-- The `N`-th harmonic number `H_N = ∑_{n=1}^{N} 1/n`, written over `range N`. -/
def H (N : ℕ) : ℚ := ∑ n ∈ Finset.range N, (1 : ℚ) / (n + 1)

/-- The shift embedding `n ↦ n + 1`, sending `range N = {0,…,N-1}` to `{1,…,N}`. -/
def succEmb : ℕ ↪ ℕ := ⟨(· + 1), fun _ _ h => Nat.succ_injective h⟩

/-- `k` is representable using denominators from `{1,…,N}`: there is a subset of
    `range N` whose shifted denominators give unit fractions summing to `k`. -/
def Representable (N k : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ sumUnitFracs (S.map succEmb) = k

-- ============================================================
-- Part II: Harmonic bounds
-- ============================================================

/-- The harmonic number is nonnegative. -/
theorem H_nonneg (N : ℕ) : 0 ≤ H N := by
  unfold H
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- Crude bound: `H_N ≤ N` (each of the `N` terms is at most `1`). -/
theorem H_le_N (N : ℕ) : H N ≤ (N : ℚ) := by
  unfold H
  calc ∑ n ∈ Finset.range N, (1 : ℚ) / (n + 1)
      ≤ ∑ _n ∈ Finset.range N, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [div_le_one (by positivity)]
        have : (0 : ℚ) ≤ i := by positivity
        linarith
    _ = (N : ℚ) := by rw [Finset.sum_const, Finset.card_range]; simp

-- ============================================================
-- Part III: Every representable integer is ≤ H_N
-- ============================================================

/-- **Key bound.** A sum of distinct unit fractions with denominators in `{1,…,N}`
    is at most the sum of *all* of them, namely `H_N`. Hence any representable
    integer `k` satisfies `(k : ℚ) ≤ H_N`. -/
theorem representable_le_H {N k : ℕ} (h : Representable N k) : (k : ℚ) ≤ H N := by
  obtain ⟨S, hSsub, hsum⟩ := h
  rw [← hsum]
  have hHmap : H N = ∑ n ∈ (Finset.range N).map succEmb, (1 : ℚ) / n := by
    unfold H
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [succEmb, Function.Embedding.coeFn_mk]
    push_cast
    ring
  rw [hHmap]
  unfold sumUnitFracs
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.map_subset_map.mpr hSsub)
  intro i _ _
  positivity

/-- `⌊H_N⌋ + 1` is **not** representable: it exceeds every representable integer. -/
theorem not_representable_floor_succ (N : ℕ) : ¬ Representable N (⌊H N⌋₊ + 1) := by
  intro h
  have h1 : ((⌊H N⌋₊ + 1 : ℕ) : ℚ) ≤ H N := representable_le_H h
  have h2 : H N < (⌊H N⌋₊ : ℚ) + 1 := Nat.lt_floor_add_one (H N)
  push_cast at h1
  linarith

/-- The parent's witness, re-derived: `N + 1` is not representable (the unit-fraction
    sum is at most `H_N ≤ N`). -/
theorem not_representable_succ (N : ℕ) : ¬ Representable N (N + 1) := by
  intro h
  have h1 : ((N + 1 : ℕ) : ℚ) ≤ H N := representable_le_H h
  have h2 : H N ≤ (N : ℚ) := H_le_N N
  have h3 : ((N + 1 : ℕ) : ℚ) ≤ (N : ℚ) := h1.trans h2
  push_cast at h3
  linarith

-- ============================================================
-- Part IV: The smallest non-representable integer f(N), constructively bounded
-- ============================================================

/-- The finiteness fact powering `f`: there exists a non-representable integer.
    Constructive witness: `⌊H_N⌋ + 1`. -/
theorem exists_not_representable (N : ℕ) : ∃ k, ¬ Representable N k :=
  ⟨⌊H N⌋₊ + 1, not_representable_floor_succ N⟩

/-- `f(N)` = the smallest integer not representable with denominators from `{1,…,N}`. -/
noncomputable def f (N : ℕ) : ℕ := Nat.find (exists_not_representable N)

/-- **The explicit constructive bound (answer to OQ-03):** `f(N) ≤ ⌊H_N⌋ + 1`. -/
theorem f_le_floor_succ (N : ℕ) : f N ≤ ⌊H N⌋₊ + 1 := by
  unfold f
  exact Nat.find_le (not_representable_floor_succ N)

/-- The coarser parent bound, recovered: `f(N) ≤ N + 1`. -/
theorem f_le_succ (N : ℕ) : f N ≤ N + 1 := by
  unfold f
  exact Nat.find_le (not_representable_succ N)

/-- The harmonic bound is at least as sharp as `N + 1`: `⌊H_N⌋ + 1 ≤ N + 1`. -/
theorem floor_H_succ_le_succ (N : ℕ) : ⌊H N⌋₊ + 1 ≤ N + 1 := by
  have : ⌊H N⌋₊ ≤ N := by
    calc ⌊H N⌋₊ ≤ ⌊(N : ℚ)⌋₊ := Nat.floor_le_floor (H_le_N N)
      _ = N := Nat.floor_natCast N
  omega

/-- Every integer below `f(N)` *is* representable — i.e. `f(N)` is genuinely the
    least non-representable integer. -/
theorem representable_of_lt_f {N k : ℕ} (h : k < f N) : Representable N k := by
  unfold f at h
  have := Nat.find_min (exists_not_representable N) h
  exact not_not.mp this

-- ============================================================
-- Part V: Concrete positive cases
-- ============================================================

/-- `0` is always representable (empty sum). -/
theorem representable_zero (N : ℕ) : Representable N 0 := by
  refine ⟨∅, Finset.empty_subset _, ?_⟩
  simp [sumUnitFracs]

/-- `1` is representable for `N ≥ 1` (the single denominator `1`). -/
theorem representable_one : Representable 1 1 := by
  refine ⟨{0}, ?_, ?_⟩
  · decide
  · simp [sumUnitFracs, succEmb]

/-- `H_1 = 1`, so the bound gives `f(1) ≤ 2`. -/
theorem f_one_le_two : f 1 ≤ 2 := by
  have hH : H 1 = 1 := by simp [H]
  have := f_le_floor_succ 1
  rw [hH] at this
  simpa using this

/-
  Summary

  Erdős #308 asks for f(N), the smallest integer not representable as a sum of
  distinct unit fractions with denominators in {1,…,N}. OQ-03 asked whether the
  finiteness argument behind f could be made constructive. This file answers yes,
  with the explicit harmonic bound

      f(N) ≤ ⌊H_N⌋ + 1                                  (f_le_floor_succ)

  obtained from the elementary fact that every representable integer is ≤ H_N
  (representable_le_H), since a sub-sum of the unit fractions {1/1, …, 1/N} cannot
  exceed their total H_N. The witness ⌊H_N⌋ + 1 is sharper than the parent's N + 1
  (floor_H_succ_le_succ: ⌊H_N⌋ + 1 ≤ N + 1, from H_N ≤ N).

  We also record that f is the genuine minimum (representable_of_lt_f) and verify
  concrete representable cases (representable_zero, representable_one), giving
  f(1) ≤ 2.

  13 theorems, 5 definitions, 0 axioms, 0 sorries — fully machine-checked.
  (Croot's deep asymptotic bounds f(N) = ⌊H_N⌋ - Θ((log log N)²/log N) remain
  axiomatized in the parent; this file provides the elementary, verified upper half.)
-/

end Erdos308OQ03

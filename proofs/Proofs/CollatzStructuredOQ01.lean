/-
# OQ-01: Backward Collatz — Preimage Structure and Infinitude of the Basin of 1

Parent: `collatz-structured` (CollatzStructured.lean) proves *forward* facts —
powers of two reach 1, closure of "reaches 1" under doubling, and specific small
values. This file studies the **backward** dynamics: the preimage (predecessor)
structure of the Collatz map and what it implies about the set of numbers that
reach 1 (the *basin* of 1).

We prove, with **no axioms and no `sorry`**:

1. **Exact preimage characterization.** For every `a m : ℕ`,
   `collatz a = m ↔ a = 2 * m ∨ (a % 2 = 1 ∧ 3 * a + 1 = m)`.
   Every predecessor of `m` is either the *even predecessor* `2m` or an
   *odd predecessor* `a` with `3a + 1 = m`.

2. **Branching law.** An odd predecessor exists iff `m ≡ 4 (mod 6)`:
   `(∃ a, a % 2 = 1 ∧ 3 * a + 1 = m) ↔ m % 6 = 4`.
   Hence in the Collatz graph every vertex `m ≡ 4 (mod 6)` has two predecessors
   and every other vertex has exactly one (the even predecessor `2m`).

3. **Backward closure of the basin.** If `collatz a = m` and `m` reaches 1, then
   `a` reaches 1. The basin of 1 is closed under taking predecessors.

4. **The basin of 1 is infinite** — it contains every power of two.

These are *unconditional* structural facts about the Collatz graph: they do not
assume the Collatz conjecture, but describe the shape of the component containing
1, independently of whether that component is all of `ℕ`.

Tags: number-theory, collatz, predecessor, preimage, dynamical-systems
-/

import Mathlib.Tactic
import Proofs.CollatzStructured

namespace CollatzBackward

open Collatz

/-!
## Part I: Exact Preimage Characterization

The Collatz map `collatz n = if n even then n/2 else 3n+1` is two-to-one onto its
image in a controlled way. A predecessor `a` of `m` (i.e. `collatz a = m`) is
either even — in which case `a/2 = m`, forcing `a = 2m` — or odd, in which case
`3a + 1 = m`.
-/

/-- **Exact preimage characterization.** `a` maps to `m` under the Collatz map iff
`a` is the even predecessor `2m` or an odd number with `3a + 1 = m`. -/
theorem collatz_eq_iff (a m : ℕ) :
    collatz a = m ↔ a = 2 * m ∨ (a % 2 = 1 ∧ 3 * a + 1 = m) := by
  unfold collatz
  split_ifs with h
  · -- a is even
    constructor
    · intro hm; exact Or.inl (by omega)
    · rintro (rfl | ⟨h1, _⟩) <;> omega
  · -- a is odd
    have h1 : a % 2 = 1 := by omega
    constructor
    · intro hm; exact Or.inr ⟨h1, hm⟩
    · rintro (rfl | ⟨_, h2⟩)
      · omega
      · exact h2

/-- The preimage of `{m}` under the Collatz map, described explicitly. -/
theorem preimage_collatz (m : ℕ) :
    collatz ⁻¹' {m} = {a | a = 2 * m ∨ (a % 2 = 1 ∧ 3 * a + 1 = m)} := by
  ext a
  simp [Set.mem_preimage, collatz_eq_iff]

/-- The **even predecessor**: `2m` always maps to `m`. -/
theorem even_pred (m : ℕ) : collatz (2 * m) = m := collatz_two_mul m

/-!
## Part II: The Branching Law

An *odd* predecessor of `m` exists exactly when `m ≡ 4 (mod 6)`. Combined with the
always-present even predecessor `2m`, this says: vertices congruent to `4 mod 6`
have in-degree 2 in the Collatz graph; all others have in-degree 1.
-/

/-- **Branching law.** `m` has an odd predecessor iff `m ≡ 4 (mod 6)`. -/
theorem odd_pred_exists_iff (m : ℕ) :
    (∃ a, a % 2 = 1 ∧ 3 * a + 1 = m) ↔ m % 6 = 4 := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    omega
  · intro hm
    exact ⟨2 * (m / 6) + 1, by omega, by omega⟩

/-- When `m ≡ 4 (mod 6)` there are (at least) two distinct predecessors: the even
predecessor `2m` and a distinct odd predecessor. The Collatz graph branches here. -/
theorem two_preds_of_mod {m : ℕ} (hm : m % 6 = 4) :
    ∃ a b, a ≠ b ∧ collatz a = m ∧ collatz b = m := by
  obtain ⟨c, hc, hcm⟩ := (odd_pred_exists_iff m).mpr hm
  refine ⟨2 * m, c, ?_, even_pred m, ?_⟩
  · omega
  · rw [collatz_eq_iff]; exact Or.inr ⟨hc, hcm⟩

/-- When `m % 6 ≠ 4`, the *only* predecessor of `m` is the even predecessor `2m`. -/
theorem unique_pred_of_not_mod {m : ℕ} (hm : m % 6 ≠ 4) {a : ℕ}
    (ha : collatz a = m) : a = 2 * m := by
  rcases (collatz_eq_iff a m).mp ha with h | ⟨hodd, h3⟩
  · exact h
  · exact absurd ((odd_pred_exists_iff m).mp ⟨a, hodd, h3⟩) hm

/-!
## Part II½: Exact In-Degree (the preimage as an explicit set)

`two_preds_of_mod` and `unique_pred_of_not_mod` give the *qualitative* dichotomy
(in-degree ≥ 2 on residue `4 mod 6`, the even predecessor otherwise). Here we
sharpen this to the **exact** preimage set and the exact in-degree count: every
vertex has in-degree exactly 1 or 2, and we exhibit the full predecessor set in
both cases. The candidate odd predecessor is always `2 * (m / 6) + 1`.
-/

/-- **Odd predecessors are unique.** Any two odd predecessors of `m` coincide:
`3 a + 1 = m` determines `a`. -/
theorem odd_pred_unique {m a b : ℕ}
    (ha : a % 2 = 1) (h3a : 3 * a + 1 = m)
    (hb : b % 2 = 1) (h3b : 3 * b + 1 = m) : a = b := by omega

/-- **In-degree ≤ 2.** Every predecessor of `m` is one of two explicit values: the
even predecessor `2 * m`, or the candidate odd predecessor `2 * (m / 6) + 1`. -/
theorem collatz_preimage_subset (m : ℕ) :
    {a | collatz a = m} ⊆ {2 * m, 2 * (m / 6) + 1} := by
  intro a ha
  simp only [Set.mem_setOf_eq] at ha
  rcases (collatz_eq_iff a m).mp ha with h | ⟨hodd, h3⟩
  · simp [h]
  · have hm : m % 6 = 4 := (odd_pred_exists_iff m).mp ⟨a, hodd, h3⟩
    have hval : a = 2 * (m / 6) + 1 := by omega
    simp [hval]

/-- **Exact preimage, generic case.** If `m % 6 ≠ 4`, the only predecessor of `m`
is the even predecessor `2 * m`: in-degree exactly 1. -/
theorem collatz_preimage_eq_of_not_mod {m : ℕ} (hm : m % 6 ≠ 4) :
    {a | collatz a = m} = {2 * m} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro ha; exact unique_pred_of_not_mod hm ha
  · rintro rfl; exact even_pred m

/-- **Exact preimage, branching case.** If `m % 6 = 4`, the predecessors of `m` are
exactly the even predecessor `2 * m` and the odd predecessor `2 * (m / 6) + 1`. -/
theorem collatz_preimage_eq_of_mod {m : ℕ} (hm : m % 6 = 4) :
    {a | collatz a = m} = {2 * m, 2 * (m / 6) + 1} := by
  apply Set.Subset.antisymm (collatz_preimage_subset m)
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  simp only [Set.mem_setOf_eq]
  rcases ha with rfl | rfl
  · exact even_pred m
  · rw [collatz_eq_iff]
    exact Or.inr ⟨by omega, by omega⟩

/-- **Exact in-degree dichotomy** (as set cardinality): the in-degree of `m` in the
Collatz graph is `2` when `m ≡ 4 (mod 6)` and `1` otherwise. This is the sharp form
of the branching law — every vertex has in-degree exactly 1 or 2. -/
theorem collatz_indeg (m : ℕ) :
    {a | collatz a = m}.ncard = if m % 6 = 4 then 2 else 1 := by
  split_ifs with hm
  · rw [collatz_preimage_eq_of_mod hm, Set.ncard_pair (by omega)]
  · rw [collatz_preimage_eq_of_not_mod hm, Set.ncard_singleton]

/-!
## Part III: Backward Closure of the Basin

If `a` maps to `m` in one step and `m` reaches 1, then `a` reaches 1 (in one more
step). Thus the basin of 1 is closed under taking predecessors — its preimage
under `collatz` is contained in itself.
-/

/-- **Backward closure.** If `collatz a = m` and `m` reaches 1, then `a` reaches 1. -/
theorem reaches_one_of_collatz {a m : ℕ} (h : collatz a = m) (hm : ReachesOne m) :
    ReachesOne a := by
  obtain ⟨k, hk⟩ := hm
  refine ⟨k + 1, ?_⟩
  simp only [collatzIter] at hk ⊢
  rw [Function.iterate_succ_apply, h]
  exact hk

/-- Backward closure via the odd predecessor: if `a` is odd and `3a + 1` reaches 1,
then `a` reaches 1. -/
theorem reaches_one_odd_pred {a : ℕ} (ha : a % 2 = 1) (h : ReachesOne (3 * a + 1)) :
    ReachesOne a :=
  reaches_one_of_collatz ((collatz_eq_iff a (3 * a + 1)).mpr (Or.inr ⟨ha, rfl⟩)) h

/-- The basin of 1 is closed under `collatz`-preimages: every predecessor of a
basin element is again a basin element. -/
theorem basin_closed_under_pred :
    collatz ⁻¹' {n | ReachesOne n} ⊆ {n | ReachesOne n} := by
  intro a ha
  exact reaches_one_of_collatz (rfl : collatz a = collatz a) ha

/-!
## Part IV: The Basin of 1 is Infinite

The set of numbers reaching 1 contains every power of two (parent file:
`pow_two_reaches_one`), and `k ↦ 2^(k+1)` is an injection into it, so the basin is
infinite. This is unconditional — it does not need the Collatz conjecture.
-/

/-- **The basin of 1 is infinite.** -/
theorem basin_infinite : {n : ℕ | ReachesOne n}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 ^ (k + 1))
  · intro x y hxy
    have hxy' : 2 ^ (x + 1) = 2 ^ (y + 1) := hxy
    have : x + 1 = y + 1 := Nat.pow_right_injective (le_refl 2) hxy'
    omega
  · intro k
    simp only [Set.mem_setOf_eq]
    exact pow_two_reaches_one (k + 1) (by omega)

/-!
## Part V: Computed Examples of the Branching Structure

Concrete instances of the preimage law for small `m`.
-/

-- 16 ≡ 4 (mod 6): two predecessors, 32 (even) and 5 (odd, 3·5+1 = 16).
example : collatz 32 = 16 := by decide
example : collatz 5 = 16 := by decide
example : (16 : ℕ) % 6 = 4 := by decide

-- 10 ≡ 4 (mod 6): two predecessors, 20 (even) and 3 (odd, 3·3+1 = 10).
example : collatz 20 = 10 := by decide
example : collatz 3 = 10 := by decide

-- 8 ≢ 4 (mod 6): only the even predecessor 16.
example : (8 : ℕ) % 6 ≠ 4 := by decide
example : collatz 16 = 8 := by decide

/-!
## Summary

**Proved (no axioms, no `sorry`)**:
1. ✓ Exact preimage characterization `collatz_eq_iff`
2. ✓ Branching law `odd_pred_exists_iff` (odd predecessor ⟺ `m ≡ 4 mod 6`)
3. ✓ In-degree dichotomy: `two_preds_of_mod` / `unique_pred_of_not_mod`
4. ✓ **Exact** preimage sets `collatz_preimage_eq_of_mod` / `collatz_preimage_eq_of_not_mod`
   and the exact in-degree count `collatz_indeg` (= 2 if `m ≡ 4 mod 6`, else 1)
5. ✓ Backward closure of the basin `reaches_one_of_collatz`, `basin_closed_under_pred`
6. ✓ The basin of 1 is infinite `basin_infinite`

**Unconditional**: none of these assume the Collatz conjecture. They describe the
backward dynamics (the Collatz graph) regardless of whether every `n` reaches 1.

**What remains open**: whether the basin of 1 is *all* of `ℕ ≥ 1` — i.e. the
Collatz conjecture itself (axiomatized in the parent file).
-/

end CollatzBackward

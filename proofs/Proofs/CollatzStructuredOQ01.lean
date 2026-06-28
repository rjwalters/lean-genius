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
## Part II½: Exact predecessor sets and the precise in-degree

`two_preds_of_mod` / `unique_pred_of_not_mod` give the in-degree *dichotomy*
qualitatively ("at least two" / "the only one"). Here we sharpen it to the **exact**
preimage set, and read off the precise in-degree as a number. The odd predecessor of an
`m ≡ 4 (mod 6)` has the closed form `(m-1)/3`, so the full predecessor set is
`{2m, (m-1)/3}` (in-degree exactly `2`); for every other `m` it is `{2m}` (in-degree
exactly `1`).
-/

/-- The **odd predecessor in closed form**: when `m ≡ 4 (mod 6)`, the number `(m-1)/3`
is odd and maps to `m` under the Collatz step. -/
theorem odd_pred_eq {m : ℕ} (hm : m % 6 = 4) :
    ((m - 1) / 3) % 2 = 1 ∧ 3 * ((m - 1) / 3) + 1 = m := by
  omega

/-- **Exact predecessor set, branching case.** For `m ≡ 4 (mod 6)` the full Collatz
preimage of `m` is exactly the pair `{2m, (m-1)/3}`. -/
theorem preimage_collatz_eq_pair {m : ℕ} (hm : m % 6 = 4) :
    collatz ⁻¹' {m} = {2 * m, (m - 1) / 3} := by
  rw [preimage_collatz]
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | ⟨_, h3⟩)
    · exact Or.inl h
    · exact Or.inr (by omega)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (odd_pred_eq hm)

/-- **Exact predecessor set, non-branching case.** For `m ≢ 4 (mod 6)` the full Collatz
preimage of `m` is exactly the singleton `{2m}`. -/
theorem preimage_collatz_eq_singleton {m : ℕ} (hm : m % 6 ≠ 4) :
    collatz ⁻¹' {m} = {2 * m} := by
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨unique_pred_of_not_mod hm, by rintro rfl; exact even_pred m⟩

/-- **Precise in-degree, branching case.** Every vertex `m ≡ 4 (mod 6)` has in-degree
exactly `2` in the Collatz graph. -/
theorem indegree_eq_two {m : ℕ} (hm : m % 6 = 4) :
    (collatz ⁻¹' {m}).ncard = 2 := by
  rw [preimage_collatz_eq_pair hm]
  exact Set.ncard_pair (by omega)

/-- **Precise in-degree, non-branching case.** Every vertex `m ≢ 4 (mod 6)` has in-degree
exactly `1` (its sole predecessor being the even one, `2m`). -/
theorem indegree_eq_one {m : ℕ} (hm : m % 6 ≠ 4) :
    (collatz ⁻¹' {m}).ncard = 1 := by
  rw [preimage_collatz_eq_singleton hm]
  exact Set.ncard_singleton _

/-!
## Part II¾: Density of Branch Vertices

The branching dichotomy (in-degree 2 on `m ≡ 4 (mod 6)`, else 1) lets us *count*.
First we bridge the arithmetic condition to the in-degree itself: a vertex has
in-degree exactly 2 **iff** `m ≡ 4 (mod 6)`. Then the branch vertices form the
arithmetic progression `{6j + 4 : j ∈ ℕ}`, enumerated injectively by `j ↦ 6j + 4`,
and exactly `k` of them lie below `6k`. So branch vertices have density exactly
`1/6` — an unconditional, verified density fact about the Collatz graph, far weaker
than the conjecture.
-/

/-- **In-degree characterizes branching.** A vertex has in-degree exactly `2` in the
Collatz graph iff it is a branch vertex `m ≡ 4 (mod 6)`; otherwise its in-degree is `1`. -/
theorem indegree_eq_two_iff (m : ℕ) :
    (collatz ⁻¹' {m}).ncard = 2 ↔ m % 6 = 4 := by
  refine ⟨fun h => ?_, indegree_eq_two⟩
  by_contra hm
  rw [indegree_eq_one hm] at h
  exact absurd h (by norm_num)

/-- The branch vertices (in-degree 2, i.e. `m ≡ 4 (mod 6)`) are exactly the arithmetic
progression `{6j + 4 : j ∈ ℕ}`. -/
theorem branch_vertices_eq :
    {m : ℕ | m % 6 = 4} = Set.range (fun j : ℕ => 6 * j + 4) := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · intro hm; exact ⟨m / 6, by show 6 * (m / 6) + 4 = m; omega⟩
  · rintro ⟨j, rfl⟩; show (6 * j + 4) % 6 = 4; omega

/-- The enumeration `j ↦ 6j + 4` of branch vertices is injective. -/
theorem branch_enum_injective : Function.Injective (fun j : ℕ => 6 * j + 4) := by
  intro a b hab
  have h : 6 * a + 4 = 6 * b + 4 := hab
  omega

/-- Below `6k`, the branch vertices are exactly the image of `range k` under `j ↦ 6j + 4`. -/
theorem branch_below_eq (k : ℕ) :
    (Finset.range (6 * k)).filter (fun m => m % 6 = 4)
      = (Finset.range k).image (fun j => 6 * j + 4) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hlt, hm⟩
    exact ⟨m / 6, by omega, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨by omega, by omega⟩

/-- **Exact count of branch vertices.** Precisely `k` vertices below `6k` are branch
vertices (in-degree 2). Branch vertices therefore have density exactly `1/6`. -/
theorem branch_count (k : ℕ) :
    ((Finset.range (6 * k)).filter (fun m => m % 6 = 4)).card = k := by
  rw [branch_below_eq, Finset.card_image_of_injective _ branch_enum_injective,
    Finset.card_range]

/-- The set of branch vertices is infinite (it contains the whole progression `6j + 4`). -/
theorem branch_vertices_infinite : {m : ℕ | m % 6 = 4}.Infinite := by
  rw [branch_vertices_eq]
  exact Set.infinite_range_of_injective branch_enum_injective

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
4. ✓ Exact predecessor sets and precise in-degree: `odd_pred_eq` (odd predecessor
   `= (m-1)/3`), `preimage_collatz_eq_pair` / `preimage_collatz_eq_singleton`
   (full preimage `= {2m, (m-1)/3}` / `= {2m}`), `indegree_eq_two` / `indegree_eq_one`
   (in-degree `= 2` / `= 1` exactly, via `Set.ncard`)
5. ✓ Density of branch vertices: `indegree_eq_two_iff` (in-degree `= 2` ⟺ `m ≡ 4 mod 6`),
   `branch_vertices_eq` (branch vertices `= {6j+4}`), `branch_count` (exactly `k` branch
   vertices below `6k`, so density exactly `1/6`), `branch_vertices_infinite`
6. ✓ Backward closure of the basin `reaches_one_of_collatz`, `basin_closed_under_pred`
7. ✓ The basin of 1 is infinite `basin_infinite`

**Unconditional**: none of these assume the Collatz conjecture. They describe the
backward dynamics (the Collatz graph) regardless of whether every `n` reaches 1.

**What remains open**: whether the basin of 1 is *all* of `ℕ ≥ 1` — i.e. the
Collatz conjecture itself (axiomatized in the parent file).
-/

end CollatzBackward

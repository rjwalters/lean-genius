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

/-- **Every in-degree set is finite.** The predecessor set of any `m` is either a
singleton (`{2m}`) or a pair (`{2m, (m-1)/3}`); in both cases finite.  This is the
prerequisite for counting nodes of the backward tree (an `ncard` argument needs the
sets to be genuinely finite, not merely `ncard`-positive). -/
theorem indegree_finite (m : ℕ) : (collatz ⁻¹' {m}).Finite := by
  by_cases hm : m % 6 = 4
  · rw [preimage_collatz_eq_pair hm]; exact Set.Finite.insert _ (Set.finite_singleton _)
  · rw [preimage_collatz_eq_singleton hm]; exact Set.finite_singleton _

/-- **Unconditional in-degree dichotomy.** Regardless of the residue of `m`, every
Collatz vertex has in-degree exactly `1` or exactly `2` — the even predecessor `2m`
always exists, and the second (odd) predecessor exists precisely when `m ≡ 4 (mod 6)`.
This is the uniform fact underlying the geometric (`≤ 2^d`) growth of the backward
tree; the residue-split lemmas `indegree_eq_one`/`indegree_eq_two` refine it. -/
theorem indegree_eq_one_or_two (m : ℕ) :
    (collatz ⁻¹' {m}).ncard = 1 ∨ (collatz ⁻¹' {m}).ncard = 2 := by
  by_cases hm : m % 6 = 4
  · exact Or.inr (indegree_eq_two hm)
  · exact Or.inl (indegree_eq_one hm)

/-- **Uniform in-degree upper bound:** the Collatz in-degree never exceeds `2`. -/
theorem indegree_le_two (m : ℕ) : (collatz ⁻¹' {m}).ncard ≤ 2 := by
  rcases indegree_eq_one_or_two m with h | h <;> omega

/-- **In-degree is positive:** `2 * m` is always a predecessor of `m`, so the
predecessor set is nonempty. -/
theorem indegree_pos (m : ℕ) : 1 ≤ (collatz ⁻¹' {m}).ncard := by
  rcases indegree_eq_one_or_two m with h | h <;> omega

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
## Part VI: Geometric Growth of the Backward Tree

The in-degree bound `indegree_le_two` (every vertex has at most two predecessors)
controls how fast the *backward* Collatz tree can grow. We turn it into an explicit
size bound: the preimage of any finite set grows by at most a factor of `2` per
Collatz step, so the set of `d`-step ancestors of a single vertex `m` has at most
`2 ^ d` elements.

The engine is a uniform Finset over-approximation of the predecessor set: every
predecessor of `m` lies in the pair `candPred m = {2m, (m−1)/3}` (the even one and
the only possible odd one), so `|collatz⁻¹' {m}| ≤ 2` *covered by a concrete Finset*.
Summing this pair-cover over a finite set `S` gives `|collatz⁻¹' S| ≤ 2 |S|`, and a
clean induction on `d` (using `collatz^[d+1] = collatz^[d] ∘ collatz`) yields the
geometric `≤ 2 ^ d` bound. Everything is unconditional.
-/

/-- The two **candidate predecessors** of `m`: the always-present even predecessor
`2m` and the only possible odd predecessor `(m−1)/3`. The actual preimage of `{m}`
is always a subset of this pair — a uniform Finset cover of the in-degree-≤-2 fact. -/
def candPred (m : ℕ) : Finset ℕ := {2 * m, (m - 1) / 3}

/-- The candidate-predecessor pair has at most two elements. -/
theorem candPred_card_le (m : ℕ) : (candPred m).card ≤ 2 := by
  unfold candPred
  calc ({2 * m, (m - 1) / 3} : Finset ℕ).card
      ≤ ({(m - 1) / 3} : Finset ℕ).card + 1 := Finset.card_insert_le _ _
    _ = 2 := by simp

/-- Every predecessor of `m` is one of the two candidates `{2m, (m−1)/3}`. -/
theorem preimage_subset_candPred (m : ℕ) : collatz ⁻¹' {m} ⊆ ↑(candPred m) := by
  intro a ha
  rw [Set.mem_preimage, Set.mem_singleton_iff, collatz_eq_iff] at ha
  unfold candPred
  rw [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  rcases ha with h | ⟨_, h3⟩
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- The preimage of a finite set `S` is covered by the finite union of candidate
pairs `⋃_{m ∈ S} {2m, (m−1)/3}`. -/
theorem preimage_subset_biUnion (S : Finset ℕ) :
    collatz ⁻¹' ↑S ⊆ ↑(S.biUnion candPred) := by
  intro a ha
  rw [Set.mem_preimage, Finset.mem_coe] at ha
  rw [Finset.mem_coe, Finset.mem_biUnion]
  refine ⟨collatz a, ha, ?_⟩
  have ha' : a ∈ collatz ⁻¹' {collatz a} := rfl
  have h := preimage_subset_candPred (collatz a) ha'
  rwa [Finset.mem_coe] at h

/-- The Collatz preimage of a finite set is finite (covered by a finite pair-union). -/
theorem preimage_finset_finite (S : Finset ℕ) : (collatz ⁻¹' ↑S).Finite :=
  (S.biUnion candPred).finite_toSet.subset (preimage_subset_biUnion S)

/-- **Single-step backward growth (Finset form).** The Collatz preimage of a finite
set `S` has at most `2 |S|` elements: each `m ∈ S` contributes at most its two
predecessors. -/
theorem preimage_finset_ncard_le (S : Finset ℕ) :
    (collatz ⁻¹' ↑S).ncard ≤ 2 * S.card := by
  calc (collatz ⁻¹' ↑S).ncard
      ≤ (↑(S.biUnion candPred) : Set ℕ).ncard :=
        Set.ncard_le_ncard (preimage_subset_biUnion S) (S.biUnion candPred).finite_toSet
    _ = (S.biUnion candPred).card := Set.ncard_coe_finset _
    _ ≤ ∑ m ∈ S, (candPred m).card := Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ S, 2 := Finset.sum_le_sum (fun m _ => candPred_card_le m)
    _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- The Collatz preimage of any finite set of vertices is finite. -/
theorem preimage_set_finite {T : Set ℕ} (hT : T.Finite) : (collatz ⁻¹' T).Finite := by
  have h := preimage_finset_finite hT.toFinset
  rwa [hT.coe_toFinset] at h

/-- **Single-step backward growth (Set form).** For any finite set of vertices `T`,
`|collatz⁻¹' T| ≤ 2 |T|`. -/
theorem preimage_set_ncard_le {T : Set ℕ} (hT : T.Finite) :
    (collatz ⁻¹' T).ncard ≤ 2 * T.ncard := by
  have h := preimage_finset_ncard_le hT.toFinset
  have hcard : hT.toFinset.card = T.ncard := by rw [← Set.ncard_coe_finset, hT.coe_toFinset]
  rwa [hT.coe_toFinset, hcard] at h

/-- The set of `d`-step Collatz ancestors of `m` (preimage of `{m}` under
`collatz^[d]`) is finite. -/
theorem ancestors_finite (m d : ℕ) : (collatz^[d] ⁻¹' {m}).Finite := by
  induction d with
  | zero => simp only [Function.iterate_zero, Set.preimage_id]; exact Set.finite_singleton m
  | succ d ih =>
    rw [Function.iterate_succ, Set.preimage_comp]
    exact preimage_set_finite ih

/-- **Geometric backward-tree bound.** The set of `d`-step Collatz ancestors of any
vertex `m` — the preimage of `{m}` under `collatz^[d]` — has at most `2 ^ d`
elements. The backward tree grows by a factor of at most `2` per level. This is the
quantitative form of the in-degree-≤-2 dichotomy, and it is unconditional: it does
not assume the Collatz conjecture. -/
theorem ancestors_ncard_le (m d : ℕ) : (collatz^[d] ⁻¹' {m}).ncard ≤ 2 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hfin : (collatz^[d] ⁻¹' {m}).Finite := ancestors_finite m d
    rw [Function.iterate_succ, Set.preimage_comp]
    calc (collatz ⁻¹' (collatz^[d] ⁻¹' {m})).ncard
        ≤ 2 * (collatz^[d] ⁻¹' {m}).ncard := preimage_set_ncard_le hfin
      _ ≤ 2 * 2 ^ d := by omega
      _ = 2 ^ (d + 1) := by rw [pow_succ]; ring

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
8. ✓ Geometric growth of the backward tree: `preimage_finset_ncard_le` /
   `preimage_set_ncard_le` (`|collatz⁻¹' T| ≤ 2|T|` for finite `T`, via the candidate
   pair-cover `candPred`), iterated to `ancestors_ncard_le` (`|collatz^[d]⁻¹' {m}| ≤ 2^d`)

**Unconditional**: none of these assume the Collatz conjecture. They describe the
backward dynamics (the Collatz graph) regardless of whether every `n` reaches 1.

**What remains open**: whether the basin of 1 is *all* of `ℕ ≥ 1` — i.e. the
Collatz conjecture itself (axiomatized in the parent file).
-/

end CollatzBackward

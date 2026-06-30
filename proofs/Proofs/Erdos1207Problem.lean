/-
Erdős Problem #1207: Isosceles-free subsets of point sets

Let `P_d(n)` be the largest integer such that every set of `n` points in `ℝ^d`
contains `P_d(n)` points, no three of which form an isosceles triangle.
Erdős asks to estimate `P_d(n)`; in particular, whether `P_2(n) < n^ε` for every
`ε > 0` (i.e. whether the largest guaranteed isosceles-free subset is only of
subpolynomial size).

**Status**: OPEN — the growth rate of `P_d(n)` is not known.

**This file (OBSERVE phase).** No prior formalization existed. We supply:

  * Clean, reusable definitions: `IsoscelesTriangle` (three pairwise-distinct
    points, one of which is equidistant from the other two) and `IsoscelesFree`
    for an arbitrary `PseudoMetricSpace`.
  * The structural facts that make `P_d(n)` well defined: isosceles-freeness is
    monotone under taking subsets, and every set with at most two points is
    isosceles-free (a triangle needs three distinct points).
  * **The one-dimensional bridge** (`isoscelesFree_iff_midpointFree`): on the
    real line, a set is isosceles-free **iff** it contains no nontrivial
    3-term arithmetic progression (no point is the midpoint of two distinct
    others). This identifies the `d = 1` case of Erdős #1207 with the
    extensively studied midpoint-free / 3-AP-free (Behrend-type) problem.
  * Concrete sanity checks exercising the definitions: `{0,1,2}` is *not*
    isosceles-free (1 is the apex), while `{0,1,3}` is.

All results are fully verified with no `axiom` declarations and no `sorry`.

Reference: https://erdosproblems.com/1207  (Er80, PaTa02, BMP05)
-/

import Mathlib

namespace Erdos1207

variable {P : Type*} [PseudoMetricSpace P]

/- ## Definitions -/

/-- Three points form an **isosceles triangle** when they are pairwise distinct
and one of them is equidistant from the other two (the *apex*). The three
disjuncts correspond to `a`, `b`, or `c` being the apex. -/
def IsoscelesTriangle (a b c : P) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    (dist a b = dist a c ∨ dist b a = dist b c ∨ dist c a = dist c b)

/-- A set is **isosceles-free** when no three of its points form an isosceles
triangle. This is the property whose largest guaranteed size, over all `n`-point
configurations, Erdős #1207 asks to estimate. -/
def IsoscelesFree (S : Set P) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ¬ IsoscelesTriangle a b c

/- ## Structural properties -/

/-- Isosceles-freeness is monotone: any subset of an isosceles-free set is
isosceles-free. This is what makes "the largest isosceles-free subset" a
sensible quantity to optimize. -/
theorem IsoscelesFree.mono {S T : Set P} (hT : IsoscelesFree T) (h : S ⊆ T) :
    IsoscelesFree S :=
  fun a ha b hb c hc => hT a (h ha) b (h hb) c (h hc)

/-- The empty set is isosceles-free. -/
theorem isoscelesFree_empty : IsoscelesFree (∅ : Set P) := by
  intro a ha; exact absurd ha (Set.notMem_empty a)

/-- Every singleton is isosceles-free. -/
theorem isoscelesFree_singleton (p : P) : IsoscelesFree ({p} : Set P) := by
  rintro a ha b hb c hc ⟨hab, _, _, _⟩
  rw [Set.mem_singleton_iff] at ha hb
  exact hab (ha.trans hb.symm)

/-- Every two-point set is isosceles-free: an isosceles triangle requires three
pairwise-distinct points, but `{p, q}` has only two. -/
theorem isoscelesFree_pair (p q : P) : IsoscelesFree ({p, q} : Set P) := by
  rintro a ha b hb c hc ⟨hab, hac, hbc, _⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp_all

/- ## The one-dimensional bridge

On the real line, isosceles-freeness coincides with the absence of nontrivial
3-term arithmetic progressions. This connects the `d = 1` case of Erdős #1207 to
the classical midpoint-free / 3-AP-free problem. -/

/-- A set of reals is **midpoint-free** when no point is the midpoint of two
distinct points of the set, i.e. it contains no nontrivial 3-term arithmetic
progression with middle term in the set. -/
def MidpointFree (S : Set ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, x ≠ z → 2 * y ≠ x + z

/-- **One-dimensional bridge for Erdős #1207.** A set of real numbers is
isosceles-free precisely when it is midpoint-free (3-AP-free). Hence estimating
`P_1(n)` is exactly the problem of the largest guaranteed 3-AP-free subset of an
`n`-element set of reals. -/
theorem isoscelesFree_iff_midpointFree (S : Set ℝ) :
    IsoscelesFree S ↔ MidpointFree S := by
  constructor
  · -- isosceles-free ⇒ midpoint-free
    intro hIso x hx y hy z hz hxz hap
    -- `y` is the midpoint of `x ≠ z`, so `(y, x, z)` is an isosceles triangle.
    have hyx : y ≠ x := by rintro rfl; apply hxz; linarith
    have hyz : y ≠ z := by rintro rfl; apply hxz; linarith
    refine hIso y hy x hx z hz ⟨hyx, hyz, hxz, Or.inl ?_⟩
    rw [Real.dist_eq, Real.dist_eq]
    rw [abs_eq_abs]
    right; linarith
  · -- midpoint-free ⇒ isosceles-free
    intro hMid a ha b hb c hc ⟨hab, hac, hbc, hd⟩
    rcases hd with h | h | h
    · -- `a` is the apex: `|a-b| = |a-c|` with `b ≠ c` forces `a` a midpoint.
      rw [Real.dist_eq, Real.dist_eq, abs_eq_abs] at h
      rcases h with h | h
      · exact hbc (by linarith)
      · exact hMid b hb a ha c hc hbc (by linarith)
    · -- `b` is the apex.
      rw [Real.dist_eq, Real.dist_eq, abs_eq_abs] at h
      rcases h with h | h
      · exact hac (by linarith)
      · exact hMid a ha b hb c hc hac (by linarith)
    · -- `c` is the apex.
      rw [Real.dist_eq, Real.dist_eq, abs_eq_abs] at h
      rcases h with h | h
      · exact hab (by linarith)
      · exact hMid a ha c hc b hb hab (by linarith)

/- ## Concrete sanity checks

These exercise the definitions on small configurations and confirm the bridge is
usable in practice. -/

/-- `{0, 1, 2}` is **not** isosceles-free: `1` is equidistant from `0` and `2`. -/
theorem not_isoscelesFree_zero_one_two :
    ¬ IsoscelesFree ({0, 1, 2} : Set ℝ) := by
  intro h
  refine h 1 (by simp) 0 (by simp) 2 (by simp) ⟨?_, ?_, ?_, Or.inl ?_⟩ <;>
    norm_num [Real.dist_eq]

/-- `{0, 1, 3}` **is** isosceles-free: it contains no nontrivial 3-term
arithmetic progression. Proved through the one-dimensional bridge. -/
theorem isoscelesFree_zero_one_three :
    IsoscelesFree ({0, 1, 3} : Set ℝ) := by
  rw [isoscelesFree_iff_midpointFree]
  rintro x hx y hy z hz hxz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy hz
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
    rcases hz with rfl | rfl | rfl <;> revert hxz <;> norm_num

end Erdos1207

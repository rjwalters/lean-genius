import Mathlib
import Proofs.Erdos531Problem

/-
# Erdős #531 — subset-sum machinery for two-element Folkman sets
# (erdos-531-incomplete-01)

## The Problem

**Erdős Problem #531** (OPEN growth rate). `F(k)` is the least `N` such that every
2-colouring of `{1,…,N}` admits a `k`-element set whose non-empty subset sums are
monochromatic. `Erdos531Problem.lean` proves `F 1 = 1` and (as of 2026-07-22)
`F 2 = 8` in full: the infinite colouring quantifier `∀ c : ℕ → Bool` is reduced
to a kernel-`decide` check `forcedCheck_all` over the 256 restrictions to
`{1,…,8}`, plus the explicit `N = 7` witness colouring.

This companion supplies the reusable **`k = 2` subset-sum machinery** that
reduction rests on: for a genuine two-element set `{a, b}` (`a ≠ b`) the
non-empty subset sums are exactly `a`, `b`, `a + b`.

## Results (namespace `Erdos531`)

1. `mem_subsetSums_pair_left` / `_right` / `_add` — `a`, `b`, `a + b` are subset
   sums of `{a, b}` (witnessed by `{a}`, `{b}`, `{a, b}`; the last needs `a ≠ b`
   so the pair has two elements).

2. `monochromaticSubsetSums_pair_forward` — if `{a, b}`'s subset sums are
   monochromatic then `c a = c b` and `c b = c (a + b)`. This is precisely the
   necessary condition a colouring must satisfy for a distinct pair to be
   Folkman-monochromatic — the fact the `F 2 ≥ 8` counterexample direction checks
   pair-by-pair against the witness colouring `1,2,4 ↦ B`, `3,5,6,7 ↦ R`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Built over the gallery defs.
-/

open Finset

namespace Erdos531

/-- `a` is a subset sum of `{a, b}` (witness `{a}`). -/
theorem mem_subsetSums_pair_left (a b : ℕ) : a ∈ SubsetSums {a, b} := by
  rw [SubsetSums, Finset.mem_image]
  refine ⟨{a}, ?_, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {b}),
    Finset.singleton_ne_empty a⟩

/-- `b` is a subset sum of `{a, b}` (witness `{b}`). -/
theorem mem_subsetSums_pair_right (a b : ℕ) : b ∈ SubsetSums {a, b} := by
  rw [SubsetSums, Finset.mem_image]
  refine ⟨{b}, ?_, by simp⟩
  rw [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b)),
    Finset.singleton_ne_empty b⟩

/-- `a + b` is a subset sum of `{a, b}` when `a ≠ b` (witness the whole pair). -/
theorem mem_subsetSums_pair_add {a b : ℕ} (hab : a ≠ b) :
    a + b ∈ SubsetSums {a, b} := by
  rw [SubsetSums, Finset.mem_image]
  refine ⟨{a, b}, ?_, ?_⟩
  · rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, Finset.insert_ne_empty a {b}⟩
  · simp [Finset.sum_pair hab]

/-- **Necessary condition.** If the subset sums of a distinct pair `{a, b}` are
monochromatic under `c`, then `c a = c b` and `c b = c (a + b)`. -/
theorem monochromaticSubsetSums_pair_forward {c : Coloring} {a b : ℕ}
    (hab : a ≠ b) (h : MonochromaticSubsetSums c {a, b}) :
    c a = c b ∧ c b = c (a + b) := by
  obtain ⟨col, hcol⟩ := h
  have ha := hcol a (mem_subsetSums_pair_left a b)
  have hb := hcol b (mem_subsetSums_pair_right a b)
  have hab' := hcol (a + b) (mem_subsetSums_pair_add hab)
  exact ⟨ha.trans hb.symm, hb.trans hab'.symm⟩

end Erdos531

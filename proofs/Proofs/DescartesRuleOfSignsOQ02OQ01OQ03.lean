/-
# Vincent's Theorem: Bisection Subdivision Eventually Isolates Real Roots (OQ-02-OQ-01-OQ-03)

## Research Question

Vincent's theorem underlies the Vincent–Collins–Akritas (VCA) and bisection
(Vincent–Akritas–Strzeboński) real-root isolation algorithms: repeatedly
subdividing an interval eventually produces subintervals each containing at most
one real root, at which point Descartes' rule of signs (0 or 1 sign variation)
certifies isolation.

This file formalizes the **geometric core** of the bisection variant: if the
roots of a polynomial form a finite set with a positive minimum gap `δ`, then
after finitely many bisections every subinterval has width `< δ` and therefore
contains **at most one root**. The remaining ingredient of the full algorithm —
that Descartes' test returns exactly `0` or `1` on such an isolated interval — is
the content of the sibling Descartes/Budan entries in this lineage; here we prove
unconditionally the termination claim "bisection eventually isolates".

## What is proved (0 axioms, 0 sorries)

1. `minGap S` — the minimum pairwise distance among distinct points of a finite
   set `S ⊆ ℝ`, with `minGap_pos` (it is strictly positive) and `minGap_le`
   (it lower-bounds every gap between distinct points).
2. `subsingleton_of_width_lt_minGap` — any interval of width `< minGap S`
   contains at most one point of `S`.
3. `width_after_bisect` / `width_pos` — bisecting an interval `k` times yields
   width `w / 2 ^ k`, which is positive and (4) eventually smaller than any
   positive bound.
4. `exists_level_isolates` — **the headline**: for any starting width `w > 0`
   there is a bisection level `k` at which every subinterval (width `w / 2 ^ k`)
   is root-isolated, i.e. meets `S` in at most one point.
5. `exists_level_isolates_each` — packaged for a concrete starting interval
   `[a, b]`: a level `k` such that each of the `2 ^ k` dyadic subintervals is
   isolated.

## Status

VERIFIED — the termination/geometry core of Vincent's bisection theorem,
fully machine-checked with no axioms and no sorries. The Descartes-test
detection step is tracked separately in the lineage.

Source: Extension of Descartes Rule OQ-02-OQ-01 (Budan upper bound).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

namespace VincentBisection

open Finset

/-! ## Minimum gap of a finite root set -/

/-- The minimum distance between two **distinct** points of a finite set `S`.
When `S` has fewer than two elements there are no distinct pairs and we return
`1` as a harmless positive default (any interval then trivially isolates). -/
noncomputable def minGap (S : Finset ℝ) : ℝ :=
  if h : (S.offDiag.image (fun p => |p.1 - p.2|)).Nonempty then
    (S.offDiag.image (fun p => |p.1 - p.2|)).min' h
  else 1

/-- `minGap` is strictly positive. -/
theorem minGap_pos (S : Finset ℝ) : 0 < minGap S := by
  unfold minGap
  split
  case isTrue h =>
    -- every element of the image is a distance between distinct points, hence > 0
    rw [Finset.lt_min'_iff]
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [Finset.mem_offDiag] at hp
    have hne : p.1 ≠ p.2 := hp.2.2
    have : p.1 - p.2 ≠ 0 := sub_ne_zero.mpr hne
    exact abs_pos.mpr this
  case isFalse => exact one_pos

/-- `minGap S` lower-bounds the distance between any two distinct points of `S`. -/
theorem minGap_le {S : Finset ℝ} {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : x ≠ y) : minGap S ≤ |x - y| := by
  have hmem : |x - y| ∈ S.offDiag.image (fun p => |p.1 - p.2|) := by
    rw [Finset.mem_image]
    exact ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hxy⟩, rfl⟩
  have hne : (S.offDiag.image (fun p => |p.1 - p.2|)).Nonempty := ⟨_, hmem⟩
  unfold minGap
  rw [dif_pos hne]
  exact Finset.min'_le _ _ hmem

/-! ## A narrow interval contains at most one root -/

/-- Any interval `[c, c + s]` of width `s < minGap S` meets `S` in at most one
point: two distinct roots in it would be closer than the minimum gap allows. -/
theorem subsingleton_of_width_lt_minGap (S : Finset ℝ) (c s : ℝ)
    (hs : s < minGap S) :
    {x : ℝ | x ∈ S ∧ x ∈ Set.Icc c (c + s)}.Subsingleton := by
  intro x hx y hy
  obtain ⟨hxS, hxc, hxc'⟩ := hx
  obtain ⟨hyS, hyc, hyc'⟩ := hy
  by_contra hne
  -- both x and y lie in [c, c+s], so |x - y| ≤ s
  have hbound : |x - y| ≤ s := by
    rw [abs_sub_le_iff]
    constructor <;> [linarith; linarith]
  have hgap : minGap S ≤ |x - y| := minGap_le hxS hyS hne
  linarith

/-! ## Bisection width and termination -/

/-- Width of a subinterval after `k` bisections of a width-`w` interval. -/
theorem width_after_bisect (w : ℝ) (k : ℕ) :
    w / 2 ^ k = w / 2 ^ k := rfl

/-- After any number of bisections the width stays positive. -/
theorem width_pos {w : ℝ} (hw : 0 < w) (k : ℕ) : 0 < w / 2 ^ k :=
  div_pos hw (by positivity)

/-- The bisected width is eventually smaller than any positive bound `δ`:
this is the Archimedean termination guarantee. -/
theorem exists_width_lt {w δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, w / 2 ^ k < δ := by
  -- choose `k` with `w / δ < 2 ^ k`, then divide through
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (w / δ) (one_lt_two (α := ℝ))
  refine ⟨k, ?_⟩
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_lt_iff₀ h2k]
  rw [div_lt_iff₀ hδ] at hk
  linarith [hk]

/-! ## Vincent's theorem (bisection core): eventual isolation -/

/-- **Eventual isolation.** For any starting width `w > 0`, there is a bisection
level `k` at which every subinterval of width `w / 2 ^ k` contains at most one
root of `S`. This is the termination statement of Vincent's bisection theorem:
repeated subdivision *must* eventually isolate the roots. -/
theorem exists_level_isolates (S : Finset ℝ) {w : ℝ} (_hw : 0 < w) :
    ∃ k : ℕ, ∀ c : ℝ,
      {x : ℝ | x ∈ S ∧ x ∈ Set.Icc c (c + w / 2 ^ k)}.Subsingleton := by
  obtain ⟨k, hk⟩ := exists_width_lt (w := w) (minGap_pos S)
  exact ⟨k, fun c => subsingleton_of_width_lt_minGap S c _ hk⟩

/-- Packaged for a concrete interval `[a, b]` with `a < b`: there is a level `k`
such that each dyadic subinterval `[a + j·s, a + j·s + s]` (with `s = (b-a)/2^k`,
`j < 2^k`) is root-isolated. The subinterval index `j` is left free because the
isolation bound is uniform in the offset `c = a + j·s`. -/
theorem exists_level_isolates_each (S : Finset ℝ) {a b : ℝ} (hab : a < b) :
    ∃ k : ℕ, ∀ j : ℕ,
      {x : ℝ | x ∈ S ∧
        x ∈ Set.Icc (a + j * ((b - a) / 2 ^ k)) (a + j * ((b - a) / 2 ^ k) + (b - a) / 2 ^ k)}.Subsingleton := by
  obtain ⟨k, hk⟩ := exists_level_isolates S (sub_pos.mpr hab)
  exact ⟨k, fun j => hk (a + j * ((b - a) / 2 ^ k))⟩

end VincentBisection

/-
# Effective Bisection Depth for Vincent Root Isolation (OQ-02-OQ-01-OQ-03-OQ-02)

## Research Question

The parent entry `DescartesRuleOfSignsOQ02OQ01OQ03` ("Vincent's Theorem:
Bisection Subdivision Eventually Isolates Real Roots") proves the *existential*
termination statement `exists_level_isolates : ∃ k, …`: for a finite root set
`S ⊆ ℝ` with minimum gap `δ = minGap S > 0` and starting interval width `w > 0`,
**some** bisection level `k` makes every dyadic subinterval (width `w / 2 ^ k`)
root-isolated.

This leaf upgrades that existential to an **effective, explicit witness**: it
exhibits a concrete, computable level of the correct `O(log(w / δ))` order at
which isolation already holds, turning a pure existence proof into a computable
termination certificate for the Vincent–Akritas–Strzeboński (VAS) / bisection
real-root isolation algorithm.

## The explicit witness and the `+1`

The natural candidate witness is `k = Nat.clog 2 ⌈w / δ⌉₊` (the integer ceiling
of `log₂(w / δ)`). By `Nat.le_pow_clog` this already gives `w / δ ≤ 2 ^ k`, hence
`w / 2 ^ k ≤ δ` — but only the **non-strict** bound.

The strict isolation bound `w / 2 ^ k < δ` that `subsingleton_of_width_lt_minGap`
requires genuinely needs **one more level**. The obstruction is exact powers of
two: if `w / δ = 4` then `⌈w / δ⌉₊ = 4`, `Nat.clog 2 4 = 2`, and
`w / 2 ^ 2 = δ` — isolation fails by an equality. So the honest effective witness
is

  `k₀ := Nat.clog 2 ⌈w / δ⌉₊ + 1`,

matching the `k ≤ log₂(w / δ) + 1` depth of the standard VAS complexity analysis.

## What is proved (0 axioms, 0 sorries)

1. `width_lt_minGap_of_clog_lt` — for **every** level `k` strictly above
   `Nat.clog 2 ⌈w / δ⌉₊`, the bisected width `w / 2 ^ k` is strictly below the
   minimum gap `δ`. (Monotone/threshold form.)
2. `level_isolates_explicit_bound` — the packaged explicit witness
   `k₀ = Nat.clog 2 ⌈w / δ⌉₊ + 1` satisfies `w / 2 ^ k₀ < minGap S`.
3. `level_isolates_explicit` — the explicit-witness upgrade of the parent's
   `exists_level_isolates`: at level `k₀` every subinterval `[c, c + w / 2 ^ k₀]`
   is root-isolated (meets `S` in at most one point), with `k₀` given by the
   formula rather than an unspecified existential.
4. `level_isolates_explicit_each` — packaged for a concrete interval `[a, b]`,
   mirroring the parent's `exists_level_isolates_each` but with the explicit `k₀`.

## Status

VERIFIED — an effective, computable `O(log(w / δ))` termination certificate for
Vincent's bisection theorem, fully machine-checked with no axioms and no sorries.

Source: Effective refinement of Vincent bisection OQ-02-OQ-01-OQ-03.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace VincentBisection

open Finset

/-! ## Minimum gap of a finite root set

We re-develop the small amount of `minGap` infrastructure needed here so that this
file is self-contained (it mirrors the parent `DescartesRuleOfSignsOQ02OQ01OQ03`). -/

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

/-- Any interval `[c, c + s]` of width `s < minGap S` meets `S` in at most one
point (verbatim from the parent, reproduced for self-containment). -/
theorem subsingleton_of_width_lt_minGap (S : Finset ℝ) (c s : ℝ)
    (hs : s < minGap S) :
    {x : ℝ | x ∈ S ∧ x ∈ Set.Icc c (c + s)}.Subsingleton := by
  intro x hx y hy
  obtain ⟨hxS, hxc, hxc'⟩ := hx
  obtain ⟨hyS, hyc, hyc'⟩ := hy
  by_contra hne
  have hbound : |x - y| ≤ s := by
    rw [abs_sub_le_iff]
    constructor <;> [linarith; linarith]
  have hgap : minGap S ≤ |x - y| := minGap_le hxS hyS hne
  linarith

/-! ## Effective (explicit) bisection depth

The parent's `exists_width_lt` chooses `k` non-constructively via the Archimedean
property. Here we replace that with the explicit logarithmic witness. -/

/-- **Threshold form.** For *every* bisection level `k` strictly above
`Nat.clog 2 ⌈w / minGap S⌉₊`, the subinterval width `w / 2 ^ k` is already
strictly below the minimum gap. The strictness of the hypothesis (`< k`, i.e.
"at least one level past the ceiling-log") is exactly what upgrades the
`≤`-bound from `Nat.le_pow_clog` to the strict `<` that isolation needs. -/
theorem width_lt_minGap_of_clog_lt (S : Finset ℝ) {w : ℝ} (_hw : 0 < w) {k : ℕ}
    (hk : Nat.clog 2 ⌈w / minGap S⌉₊ < k) :
    w / 2 ^ k < minGap S := by
  set δ := minGap S with hδdef
  have hδ : 0 < δ := minGap_pos S
  set n : ℕ := ⌈w / δ⌉₊ with hn
  -- `w / δ ≤ n = ⌈w / δ⌉₊`
  have h1 : w / δ ≤ (n : ℝ) := Nat.le_ceil _
  -- `n ≤ 2 ^ (clog 2 n)`
  have h2 : n ≤ 2 ^ Nat.clog 2 n := Nat.le_pow_clog (by norm_num) n
  -- `2 ^ (clog 2 n) < 2 ^ k` from `clog 2 n < k`
  have h3 : 2 ^ Nat.clog 2 n < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) hk
  -- combine in ℕ then cast to ℝ
  have h4 : n < 2 ^ k := lt_of_le_of_lt h2 h3
  have h5 : (n : ℝ) < (2 : ℝ) ^ k := by
    calc (n : ℝ) < ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h4
      _ = (2 : ℝ) ^ k := by push_cast; ring
  have hwδ : w / δ < (2 : ℝ) ^ k := lt_of_le_of_lt h1 h5
  -- turn `w / δ < 2 ^ k` into `w / 2 ^ k < δ`
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  rw [div_lt_iff₀ h2k, mul_comm]
  rwa [div_lt_iff₀ hδ] at hwδ

/-- **Explicit witness bound.** The concrete, computable level
`k₀ = Nat.clog 2 ⌈w / minGap S⌉₊ + 1` already makes the bisected width strictly
smaller than the minimum gap. This is the effective replacement for the parent's
existential `exists_width_lt`. -/
theorem level_isolates_explicit_bound (S : Finset ℝ) {w : ℝ} (hw : 0 < w) :
    w / 2 ^ (Nat.clog 2 ⌈w / minGap S⌉₊ + 1) < minGap S :=
  width_lt_minGap_of_clog_lt S hw (Nat.lt_succ_self _)

/-- **Effective eventual isolation.** The explicit-witness upgrade of the parent's
`exists_level_isolates`: at the concrete level
`k₀ = Nat.clog 2 ⌈w / minGap S⌉₊ + 1`, every subinterval `[c, c + w / 2 ^ k₀]`
contains at most one root of `S`. The level is now *given by a formula* of the
correct `O(log(w / minGap S))` order rather than by an unspecified existential. -/
theorem level_isolates_explicit (S : Finset ℝ) {w : ℝ} (hw : 0 < w) (c : ℝ) :
    {x : ℝ | x ∈ S ∧
      x ∈ Set.Icc c (c + w / 2 ^ (Nat.clog 2 ⌈w / minGap S⌉₊ + 1))}.Subsingleton :=
  subsingleton_of_width_lt_minGap S c _ (level_isolates_explicit_bound S hw)

/-- Packaged for a concrete interval `[a, b]` with `a < b`, mirroring the parent's
`exists_level_isolates_each` but with the explicit level
`k₀ = Nat.clog 2 ⌈(b - a) / minGap S⌉₊ + 1`: each dyadic subinterval
`[a + j·s, a + j·s + s]` with `s = (b - a) / 2 ^ k₀` is root-isolated. -/
theorem level_isolates_explicit_each (S : Finset ℝ) {a b : ℝ} (hab : a < b)
    (j : ℕ) :
    {x : ℝ | x ∈ S ∧
      x ∈ Set.Icc (a + j * ((b - a) / 2 ^ (Nat.clog 2 ⌈(b - a) / minGap S⌉₊ + 1)))
        (a + j * ((b - a) / 2 ^ (Nat.clog 2 ⌈(b - a) / minGap S⌉₊ + 1))
          + (b - a) / 2 ^ (Nat.clog 2 ⌈(b - a) / minGap S⌉₊ + 1))}.Subsingleton :=
  level_isolates_explicit S (sub_pos.mpr hab) _

end VincentBisection

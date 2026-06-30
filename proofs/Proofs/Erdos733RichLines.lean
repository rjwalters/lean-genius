/-
# Erdős Problem #733 — the elementary rich-line bound

**Parent.** `Erdos733Problem.lean` (registered) formalizes the count
`f(n) = countLineCompatible n` of line-compatible sequences and records the
Szemerédi–Trotter answer `f(n) = exp(Θ(√n))` as the two axioms `lower_bound`
and `upper_bound`. Its **Part III** states, as an unproved docstring claim, the
Szemerédi–Trotter corollary on rich lines:

> *The number of k-rich lines (lines with ≥ k points) is `O(n²/k³ + n/k)`.*

That corollary is exactly the engine that drives the (axiomatized) upper bound,
yet the registered file proves nothing about it. This file fills that gap with
the **elementary, unconditional** rich-line estimate — the baseline that
Szemerédi–Trotter then improves.

## The statement (fully proved here, 0 axioms, 0 sorries)

For a finite point set `P` (`|P| = n`) and a family `lines` of subsets, *assume
only the defining property of lines in the plane*: any two distinct lines meet
in at most one point. Then for every `k`,

> `#{ L : |L| ≥ k } · C(k,2)  ≤  C(n,2)`,  hence  `#{ L : |L| ≥ k } ≤ C(n,2) / C(k,2)`.

This is the classic double-counting bound: each line `L` carries the `C(|L|,2)`
two-element subsets of its points; because two distinct lines share at most one
point, **no pair lies on two lines**, so the pair-sets are pairwise disjoint and
together fit inside the `C(n,2)` pairs of `P`. Summing the lower estimate
`C(k,2) ≤ C(|L|,2)` over the rich lines gives the bound.

## Honest comparison with Szemerédi–Trotter

The bound here is `#rich-lines = O(n²/k²)`. Szemerédi–Trotter improves the
exponent on `k` from `2` to `3` (plus an `n/k` term): `O(n²/k³ + n/k)`. The
improvement is genuinely deep — it is the content of the parent's axioms — but
the `O(n²/k²)` baseline is completely elementary and is what we machine-check
here. No incidence theorem, no real-analytic input: just the linear-space
hypothesis (`hlin`) and counting two-element subsets.

## On assumptions

`hsub` (lines are subsets of the point set) and `hlin` (two distinct lines meet
in ≤ 1 point) are **hypotheses of the theorems**, not axioms: every statement is
`∀ P lines, hsub → hlin → …`. There are no `axiom` declarations and no
assumption-carrying structure fields, so the file is genuinely 0-axiom.
`hlin` is precisely the abstract "linear space" / "partial linear space"
property satisfied by honest lines in `ℝ²` (two points determine a unique line),
so the bound applies verbatim to the geometric setting of `Erdos733Problem`.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic

open Finset

namespace Erdos733RichLines

/-!
## The core double-counting inequality

The sum, over all lines, of the number of point-pairs on each line is at most
the total number of point-pairs `C(n,2)`. This is the heart of every rich-line
bound; everything below is a corollary.
-/

/--
**Pairs on distinct lines are disjoint.**
If two lines `L₁ ≠ L₂` meet in at most one point, then no two-element subset of
points lies on both: the two-element subsets they carry are disjoint families.
-/
theorem disjoint_pairs {V : Type*} [DecidableEq V]
    {L₁ L₂ : Finset V} (h : (L₁ ∩ L₂).card ≤ 1) :
    Disjoint (L₁.powersetCard 2) (L₂.powersetCard 2) := by
  rw [Finset.disjoint_left]
  intro s hs1 hs2
  rw [Finset.mem_powersetCard] at hs1 hs2
  have hss : s ⊆ L₁ ∩ L₂ := Finset.subset_inter hs1.1 hs2.1
  have hle : s.card ≤ (L₁ ∩ L₂).card := Finset.card_le_card hss
  rw [hs1.2] at hle
  omega

/--
**Core bound (double counting of point-pairs).**
For a finite point set `P` and a family `lines` of subsets, each pair of distinct
lines meeting in at most one point,
`∑_{L ∈ lines} C(|L|,2) ≤ C(|P|,2)`.
-/
theorem sum_choose_two_le {V : Type*} [DecidableEq V]
    (P : Finset V) (lines : Finset (Finset V))
    (hsub : ∀ L ∈ lines, L ⊆ P)
    (hlin : ∀ L₁ ∈ lines, ∀ L₂ ∈ lines, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1) :
    ∑ L ∈ lines, (L.card).choose 2 ≤ (P.card).choose 2 := by
  -- Rewrite each `C(|L|,2)` as the cardinality of the two-element subsets of `L`.
  have hcard : ∀ L ∈ lines, (L.card).choose 2 = (L.powersetCard 2).card := by
    intro L _
    rw [Finset.card_powersetCard]
  rw [Finset.sum_congr rfl hcard]
  -- The pair-families are pairwise disjoint, so their sizes sum to the size of
  -- their union.
  have hdisj : ∀ L₁ ∈ lines, ∀ L₂ ∈ lines, L₁ ≠ L₂ →
      Disjoint (L₁.powersetCard 2) (L₂.powersetCard 2) :=
    fun L₁ h1 L₂ h2 hne => disjoint_pairs (hlin L₁ h1 L₂ h2 hne)
  rw [← Finset.card_biUnion hdisj, ← Finset.card_powersetCard 2 P]
  -- That union is contained in the two-element subsets of `P`.
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_biUnion] at hs
  obtain ⟨L, hL, hsL⟩ := hs
  rw [Finset.mem_powersetCard] at hsL ⊢
  exact ⟨hsL.1.trans (hsub L hL), hsL.2⟩

/-!
## The rich-line bound
-/

/--
**Elementary rich-line bound.**
With `n = |P|`, the number of lines containing at least `k` points satisfies
`#{ L : |L| ≥ k } · C(k,2) ≤ C(n,2)`.
This is the unconditional baseline that Szemerédi–Trotter later sharpens.
-/
theorem rich_line_bound {V : Type*} [DecidableEq V]
    (P : Finset V) (lines : Finset (Finset V))
    (hsub : ∀ L ∈ lines, L ⊆ P)
    (hlin : ∀ L₁ ∈ lines, ∀ L₂ ∈ lines, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1)
    (k : ℕ) :
    (lines.filter (fun L => k ≤ L.card)).card * k.choose 2 ≤ (P.card).choose 2 := by
  set S := lines.filter (fun L => k ≤ L.card) with hS
  calc S.card * k.choose 2
      = ∑ _L ∈ S, k.choose 2 := (Finset.sum_const_nat (fun _ _ => rfl)).symm
    _ ≤ ∑ L ∈ S, (L.card).choose 2 := by
        apply Finset.sum_le_sum
        intro L hL
        rw [hS, Finset.mem_filter] at hL
        exact Nat.choose_le_choose 2 hL.2
    _ ≤ ∑ L ∈ lines, (L.card).choose 2 :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ ≤ (P.card).choose 2 := sum_choose_two_le P lines hsub hlin

/--
**Rich-line count (division form).**
For `k ≥ 2`, the number of `k`-rich lines is at most `C(n,2) / C(k,2)` (with
`n = |P|`), the familiar `O(n²/k²)` estimate.
-/
theorem rich_line_count_le {V : Type*} [DecidableEq V]
    (P : Finset V) (lines : Finset (Finset V))
    (hsub : ∀ L ∈ lines, L ⊆ P)
    (hlin : ∀ L₁ ∈ lines, ∀ L₂ ∈ lines, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1)
    (k : ℕ) (hk : 2 ≤ k) :
    (lines.filter (fun L => k ≤ L.card)).card ≤ (P.card).choose 2 / k.choose 2 := by
  have hpos : 0 < k.choose 2 := Nat.choose_pos hk
  rw [Nat.le_div_iff_mul_le hpos]
  exact rich_line_bound P lines hsub hlin k

/--
**Number of proper lines.**
A line with at least two points is "proper". Taking `k = 2` (so `C(2,2) = 1`),
the number of proper lines is at most `C(n,2)` — each is charged to a distinct
point-pair. (This is the easy direction of de Bruijn–Erdős-type counting.)
-/
theorem num_proper_lines_le {V : Type*} [DecidableEq V]
    (P : Finset V) (lines : Finset (Finset V))
    (hsub : ∀ L ∈ lines, L ⊆ P)
    (hlin : ∀ L₁ ∈ lines, ∀ L₂ ∈ lines, L₁ ≠ L₂ → (L₁ ∩ L₂).card ≤ 1) :
    (lines.filter (fun L => 2 ≤ L.card)).card ≤ (P.card).choose 2 := by
  have h := rich_line_bound P lines hsub hlin 2
  simpa using h

/--
**Monotonicity in `k`.**
Fewer lines are `k'`-rich than `k`-rich when `k ≤ k'`; combined with
`rich_line_bound` this lets a single pair budget control every threshold.
-/
theorem rich_lines_antitone {V : Type*} [DecidableEq V]
    (lines : Finset (Finset V)) {k k' : ℕ} (hk : k ≤ k') :
    (lines.filter (fun L => k' ≤ L.card)).card
      ≤ (lines.filter (fun L => k ≤ L.card)).card := by
  apply Finset.card_le_card
  intro L hL
  rw [Finset.mem_filter] at hL ⊢
  exact ⟨hL.1, le_trans hk hL.2⟩

end Erdos733RichLines

import Mathlib

/-
# Erdős #100 — the integer-distance bridge: #distinct distances ≤ diameter
# (erdos-100-oq-01-incomplete-01)

## The Open Question

**Erdős Problem #100** (OPEN). If `A ⊆ ℝ²` is a set of `n` points all of whose
pairwise distances are positive integers, must the diameter of `A` be `≫ n`?
The best lower bound (Guth–Katz, via distinct distances) is `diam ≥ c·n/log n`.

The OQ-01 scaffold `Erdos100OQ01.lean` carries the asymptotic reductions and one
`sorry` (Piepmeyer's explicit 9-point integer-distance witness, a concrete
construction). This file does **not** attempt that construction. It formalizes the
**combinatorial bridge** the scaffold documents as the link to Erdős #89:

> if all pairwise distances are positive integers, the distinct distances are a
> subset of `{1, 2, …, ⌊diam⌋}`, so `#distinct distances ≤ diam`.

This is exactly the step that, combined with the Guth–Katz distinct-distances
lower bound, yields `diam ≥ c·n/log n`.

## Result

1. `card_le_floor_of_pos_int_le` — the clean combinatorial core: any finite set
   `S` of reals that are **positive integers**, each `≤ D`, has `|S| ≤ ⌊D⌋₊`.
   (Each value injects into `{1, …, ⌊D⌋₊}` via its natural-number value.)

2. `card_le_of_pos_int_le` — the same with the bound stated directly against `D`:
   `|S| ≤ D` (since `⌊D⌋₊ ≤ D` for `D ≥ 0`).

3. `distinct_distances_le_diam` — the named bridge: a finite set of positive
   integers bounded by the diameter `D ≥ 0` (the distinct integer distances) has
   cardinality `≤ D`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace Erdos100OQ01Incomplete01

open Finset

/-- **Counting positive integers in a bounded range.** A finite set `S` of reals,
    each a positive integer and each `≤ D`, has at most `⌊D⌋₊` elements: the
    natural-number value of each is a distinct point of `{1, …, ⌊D⌋₊}`. -/
theorem card_le_floor_of_pos_int_le (S : Finset ℝ) (D : ℝ)
    (hint : ∀ x ∈ S, ∃ k : ℕ, x = (k : ℝ))
    (hpos : ∀ x ∈ S, 0 < x)
    (hle : ∀ x ∈ S, x ≤ D) :
    S.card ≤ ⌊D⌋₊ := by
  have hmaps : ∀ x ∈ S, ⌊x⌋₊ ∈ Finset.Icc 1 ⌊D⌋₊ := by
    intro x hx
    obtain ⟨k, rfl⟩ := hint x hx
    rw [Nat.floor_natCast]
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · have : (0 : ℝ) < (k : ℝ) := hpos _ hx
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this.ne')
    · have hkD : (k : ℝ) ≤ D := hle _ hx
      calc k = ⌊(k : ℝ)⌋₊ := (Nat.floor_natCast k).symm
        _ ≤ ⌊D⌋₊ := Nat.floor_le_floor hkD
  have hinj : Set.InjOn (fun x => ⌊x⌋₊) (↑S : Set ℝ) := by
    intro x hx y hy hxy
    obtain ⟨k, rfl⟩ := hint x hx
    obtain ⟨j, rfl⟩ := hint y hy
    simp only [Nat.floor_natCast] at hxy
    exact_mod_cast hxy
  calc S.card ≤ (Finset.Icc 1 ⌊D⌋₊).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = ⌊D⌋₊ := by rw [Nat.card_Icc]; omega

/-- The same bound stated directly against `D`: for `D ≥ 0`, a finite set of
    positive integers each `≤ D` has cardinality `≤ D`. -/
theorem card_le_of_pos_int_le (S : Finset ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hint : ∀ x ∈ S, ∃ k : ℕ, x = (k : ℝ))
    (hpos : ∀ x ∈ S, 0 < x)
    (hle : ∀ x ∈ S, x ≤ D) :
    (S.card : ℝ) ≤ D := by
  have h := card_le_floor_of_pos_int_le S D hint hpos hle
  calc (S.card : ℝ) ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast h
    _ ≤ D := Nat.floor_le hD

/-- **The integer-distance bridge (Erdős #100 ↔ #89).** If the distinct pairwise
    distances of an integer-distance point set form the finite set `dists`, all
    positive integers and bounded by the diameter `D ≥ 0`, then the number of
    distinct distances is at most the diameter:
    `#distinct distances ≤ D`.

    Combined with the Guth–Katz distinct-distances lower bound
    `#distinct ≥ c·n/log n`, this gives `diam ≥ c·n/log n`. -/
theorem distinct_distances_le_diam (dists : Finset ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hint : ∀ x ∈ dists, ∃ k : ℕ, x = (k : ℝ))
    (hpos : ∀ x ∈ dists, 0 < x)
    (hle : ∀ x ∈ dists, x ≤ D) :
    (dists.card : ℝ) ≤ D :=
  card_le_of_pos_int_le dists D hD hint hpos hle

/-
## Significance

Erdős #100 asks whether an `n`-point integer-distance set in the plane must have
diameter `≫ n`. The scaffold reduces the conjecture to asymptotic facts about
`n/log n` and records, as the crucial link to Erdős #89, that integer distances
confine the distinct distances to `{1, …, ⌊diam⌋}`.

This file proves that link cleanly and unconditionally: any finite set of
positive integers bounded by `D` has at most `⌊D⌋₊ ≤ D` elements
(`card_le_floor_of_pos_int_le`, `card_le_of_pos_int_le`), so the distinct integer
distances of a configuration number at most its diameter
(`distinct_distances_le_diam`). This is the exact inequality that turns the
Guth–Katz distinct-distances lower bound `≥ c·n/log n` into the current best
diameter bound `diam ≥ c·n/log n`. The Piepmeyer explicit-witness construction
(the scaffold's remaining `sorry`) is independent of this combinatorial bridge.
-/

end Erdos100OQ01Incomplete01

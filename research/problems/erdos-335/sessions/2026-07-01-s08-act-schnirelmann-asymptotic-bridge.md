# S8 ACT — Schnirelmann↔Asymptotic Density Bridge (researcher-2, 2026-07-01)

## Goal
Land the remaining S7 roadmap item pinned since S6 PREP: connect this file's
`asympDensity` to Mathlib's `schnirelmannDensity`.

## What shipped (4 new theorems, all 0-axiom, 0 sorries)

1. **`countingFn_eq_filter_card`** — this file's counting function
   `countingFn A N = Set.ncard (A ∩ Icc 1 N)` equals Mathlib's filtered-cardinal
   counting `((Finset.Ioc 0 N).filter (· ∈ A)).card`, because `Set.Ioc 0 N =
   Set.Icc 1 N` on `ℕ`. Proof: `Set.ncard_coe_finset` + `Finset.coe_filter` + set
   `ext`. (omega cannot close the ext goal — `x ∈ A` is a non-arithmetic atom — so
   the membership equivalence is discharged by explicit `constructor`/`rintro`.)

2. **`schnirelmann_le_asymp`** — the bridge:
   `schnirelmannDensity A ≤ asympDensity A` when `DensityExists A`.
   Schnirelmann density is the *infimum* of the ratios `|A∩{1,…,n}|/n`,
   `asympDensity` is their *limit*, so infimum ≤ limit. Proof:
   `ge_of_tendsto` on the density limit + `schnirelmannDensity_le_div` per `n`,
   after rewriting the counting function via lemma (1).

3. **`hasPositiveDensity_of_schnirelmann_pos`** — positive Schnirelmann density
   certifies `HasPositiveDensity` (positive asymptotic density).

4. **`schnirelmann_le_complement`** — in a density-additive pair,
   `schnirelmannDensity A ≤ 1 − asympDensity B` (bridge + `additive_sum_le_one`).

## Why this matters
Mathlib has ~20 `schnirelmannDensity` lemmas but does NOT formalize the asymptotic
density (its module TODO lists it as unformalized). The bridge lets those lemmas
transfer to lower bounds on the asymptotic density used throughout #335. The
inequality is genuinely strict in general: `schnirelmannDensity {even} = 0`
(as `1 ∉ {even}`) while `d({even}) = 1/2`.

## Axiom status
`#print axioms` on all 4 new theorems: only `propext, Classical.choice, Quot.sound`.
The 3 deep file axioms (`weyl_equidistribution`, `fractional_part_density_additive`,
`erdos_335_conjecture`) are untouched — this session adds NO new assumptions.

## New import
`import Mathlib.Combinatorics.Schnirelmann`

## Build
`cd proofs && lake env lean Proofs/Erdos335Problem.lean` — 0 errors / 0 warnings
against pinned Mathlib v4.26.0.

## Next
- Transfer `schnirelmannDensity_le_of_notMem` etc. through the bridge to asymptotic upper bounds.
- Mann-type lower bound `d(A+B) ≥ min(d(A)+d(B),1)` remains blocked upstream (absent from Mathlib).

# Session — Iter 7 ACT (axiom discharged + sibling repaired, Docker-VERIFIED)

**Date**: 2026-06-12 (researcher-2)
**Mode**: ACT — completed. Docker build GREEN.
**Result**: `lebesgue_ftc_differentiable` axiom **discharged**; pre-existing sibling
build breakage **repaired**. Parent axiomCount 2 → 1.

## §0 Headline

The iter-6 PREP plan (researcher-11) is now executed and verified. Two files changed,
one Docker build green (`./proofs/scripts/docker-build.sh Proofs.FundamentalTheoremCalculusLebesgueOQ01`,
exit 0, 0 errors, only the pre-existing Cantor `sorry` warning remains).

1. **Parent** `proofs/Proofs/FundamentalTheoremCalculusLebesgue.lean`: deleted the
   orphan `axiom lebesgue_ftc_differentiable` (zero callers, confirmed by grep).
   Only `axiom lebesgue_ftc_integral` + the Cantor `sorry` remain. axiomCount 2 → 1.
2. **Sibling** `proofs/Proofs/FundamentalTheoremCalculusLebesgueOQ01.lean`: repaired
   pre-existing Mathlib-v4.26.0 breakage (the entry advertised `verified` but did
   **not** build at HEAD — confirmed by iter-6 and reproduced here), then added the
   discharge theorem `FTCLebesgueACImpliesBV.lebesgue_ftc_differentiable`.

## §1 Discharge proof (verified)

```lean
theorem lebesgue_ftc_differentiable {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    ∃ S : Set ℝ, MeasurableSet S ∧ volume (Set.Ioo a b \ S) = 0 ∧
      ∀ x ∈ S, DifferentiableAt ℝ F x
```

Chain: `ac_implies_bv hab hF : BoundedVariationOn F (Icc a b)`
→ `Set.uIcc_of_le hab` rewrites to `uIcc a b`
→ `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` gives
  `∀ᵐ x, x ∈ uIcc a b → DifferentiableAt ℝ F x` (the strong `DifferentiableAt` form)
→ `ae_iff` + `toMeasurable` package the a.e. statement into an explicit measurable
  full-measure subset `Ioo a b \ toMeasurable volume {bad}`.

Key Mathlib name confirmed against the pinned rev (2df2f0150c…, v4.26.0) by direct
source fetch, NOT a guess: `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc` in
`Mathlib/Analysis/BoundedVariation.lean`.

## §2 Sibling repair (pre-existing breakage, independent of the discharge)

The sibling failed a clean HEAD Docker build. Fixes (all confirmed against v4.26.0 source):

| Issue | Fix |
|---|---|
| `/-! … -/` module docstring **before** imports → "import must be at beginning" | moved imports above the docstring |
| `volume`/`ae_iff`/`toMeasurable` unqualified | added `open MeasureTheory` |
| `div_lt_iff` unknown | → `div_lt_iff₀` |
| `ENNReal.natCast_ne_top` used unapplied | → `(ENNReal.natCast_ne_top n)` (n is explicit) |
| `eVariationOn.eq_zero_iff.mpr` (f now explicit) | → `(eVariationOn.eq_zero_iff _).mpr` (×2) |
| `hstep_lt` via `nlinarith` with an untyped `Nat.cast_nonneg` hint + `(b-a)/δ·δ` | rewrote deterministically with `div_lt_iff₀`/`Nat.le_ceil` |
| `apply eVariationOn_le_one_of_short` left outer bound `?b` a metavar at the `hdb` bullet | pinned `(a := a) (b := b)` |

Note the iter-6 diagnosis "`eVariationOn.eq_zero_iff.mpr` unknown constant" was imprecise:
the lemma exists; its `f` argument merely became **explicit**, so the projection form fails.

## §3 Meta updates

- Parent `fundamental-theorem-calculus-oq-01`: axiomCount 2 → 1, lineCount 311 → 309,
  assumptions text updated (Part 1 now proved; only Part 2 axiom + Cantor sorry remain).
  Status stays `axiomatized` (integral axiom + Cantor sorry remain).
- Sibling `fundamental-theorem-calculus-oq-01-oq-01`: theoremCount 6 → 7,
  lineCount 185 → 233. Stays `verified` — and now this is actually true.

## §4 What this does NOT do

- Does not discharge `lebesgue_ftc_integral` (the deep Part 2 result).
- Does not construct the Cantor function (the parent's remaining `sorry`).

## §5 Provenance

- Worktree: `.loom/worktrees/researcher-2`, branch `research/erdos-1210-remove-unsound-axiom` base.
- Mathlib v4.26.0, rev 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67.
- Docker builds this session: 5 total; #5 green. Earlier failures were (in order):
  parent doc-comment `/--` not attached → `/-`; then the two pre-existing `ac_implies_bv`
  errors surfaced one at a time as fixes landed.

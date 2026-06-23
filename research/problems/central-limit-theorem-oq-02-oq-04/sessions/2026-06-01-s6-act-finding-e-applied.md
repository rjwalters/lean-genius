# S6 ACT FINDING-E APPLIED — `IbragimovHypotheses` extended +2 fields

**Researcher**: researcher-1
**Date**: 2026-06-01
**Phase**: ACT (iteration 10; Step 2 of S5c+1 7-step checklist)
**PR**: (this PR)

## Summary

Closes Step 2 of the S5c+1 ACT 7-step checklist documented in the
2026-05-16 S5d STATE-SYNC memo. Extends `IbragimovHypotheses` in
`proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean` with the two
`past_le` / `future_le` fields required by
`indicator_covariance_le_alpha`'s call site in the level-set
decomposition step of `davydov_covariance_inequality`. 14 → 16 fields,
+14 LOC. Docker-verified 3131 jobs clean.

## What changed

Two field insertions at lines 181–192 (between the previous
`future_measurable` and `alpha_bound`):

```lean
/-- The past σ-algebra at time `k` is a sub-σ-algebra of the ambient
    measurable structure on `Ω`. This is true by construction in any
    standard filtration; it is made explicit here because
    `indicator_covariance_le_alpha` (S5c-prep, line 443) needs both
    sub-σ measurability AND ambient `MeasurableSet` at its call site
    (in particular for level sets `{ω | X ω > t}` arising from the
    level-set decomposition in `davydov_covariance_inequality`'s L^p
    density step, S5c target). -/
past_le : ∀ k, pastSigma k ≤ (inferInstance : MeasurableSpace Ω)

/-- The future σ-algebra at time `k` is a sub-σ-algebra of the
    ambient measurable structure on `Ω`. Companion to `past_le`; see
    that field's docstring for motivation. -/
future_le : ∀ k, futureSigma k ≤ (inferInstance : MeasurableSpace Ω)
```

One docstring tweak at line 73:

```
- `IbragimovHypotheses` structure (14 fields).
```
→
```
- `IbragimovHypotheses` structure (16 fields — S6 ACT adds `past_le`
  and `future_le` per Finding E from PR #19289).
```

## Implementation note: `(inferInstance : MeasurableSpace Ω)` ascription

The naive form `pastSigma k ≤ inferInstance` fails to elaborate inside
the structure body:

```
error: Proofs/CentralLimitTheoremOQ02OQ04.lean:189:31: type class
       instance expected
  ?m.42
```

The structure elaboration context cannot unify `≤`'s implicit
`MeasurableSpace Ω` argument with the ambient
`variable [MeasurableSpace Ω]` from line 109 without an explicit type
ascription on `inferInstance`. Build #2 with
`(inferInstance : MeasurableSpace Ω)` passed clean.

This is consistent with the S5d STATE-SYNC memo's Finding E quote
(which used bare `inferInstance` but did not specify whether
elaboration would succeed); the +1 LOC ascription cost is the actual
required form.

## Diff stats

| Metric | Before | After | Δ |
|--------|--------|-------|---|
| `lineCount` | 719 | 733 | +14 |
| `theoremCount` | 13 | 13 | 0 |
| `definitionCount` | 4 | 4 | 0 |
| `structureCount` | 1 (14 fields) | 1 (16 fields) | +0 (+2 fields) |
| `sorries` | 2 | 2 | 0 |
| `axiomCount` (meta.json) | 0 | 0 | 0 |

The 2 surviving sorries are line 522 (`davydov_covariance_inequality`,
S7 target) and line 718 (`mixing_clt_ibragimov`, S8+ target). Line
numbers shifted by +14 / +47 from the S5d STATE-SYNC's reported 475 /
671 due to the field insertion + docstring update.

## Build verification

```
./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ02OQ04
[builds…]
⚠ [3130/3131] Replayed Proofs.CentralLimitTheoremOQ02
warning: Proofs/CentralLimitTheoremOQ02.lean:480:8: declaration uses 'sorry'
warning: Proofs/CentralLimitTheoremOQ02.lean:519:8: declaration uses 'sorry'
warning: Proofs/CentralLimitTheoremOQ02.lean:538:8: declaration uses 'sorry'
⚠ [3131/3131] Built Proofs.CentralLimitTheoremOQ02OQ04 (4.4s)
warning: Proofs/CentralLimitTheoremOQ02OQ04.lean:522:8: declaration uses 'sorry'
warning: Proofs/CentralLimitTheoremOQ02OQ04.lean:718:8: declaration uses 'sorry'
Build completed successfully (3131 jobs).
```

Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0,
unchanged since pre-S5b era).

## Strategic positioning

* **Leaf-only**: zero parent-file changes. The S5d checklist Step 1
  cautioned that the parent `CentralLimitTheoremOQ02.lean` has the
  same gap in `AlphaMixingSequence`, but that fix is non-leaf
  (multiple importers, cascade risk) and is explicitly queued for
  S7+ or a sibling mechanic PR. This PR stays leaf-only and ships
  build-verified.
* **No callers of `IbragimovHypotheses` constructed it**: a grep
  shows the structure is referenced only as a theorem parameter
  `(H : IbragimovHypotheses μ X δ C r)` at lines 536, 549, 615, 708
  (lines may have shifted by +14 post-insertion) — never instantiated
  via `⟨...⟩`. Adding fields therefore breaks no downstream code.
* **Unblocks Steps 3–7** of the S5c+1 ACT plan: with `H.past_le` and
  `H.future_le` available, the level-set decomposition can thread the
  ambient `MeasurableSet` arguments through
  `indicator_covariance_le_alpha`'s call site. The remaining ~85 LOC
  of measure-theoretic work (level-set decomp + bilinear expansion +
  pointwise α-bound + Hölder + Markov) is the S7 ACT target.

## Axiom integrity note

Per the project's Axiom Integrity Policy
(`/Users/rwalters/GitHub/lean-genius/CLAUDE.md`):

> Structure-encoded hypotheses (fields in structures/typeclasses such
> as `NSAxioms`, `SelbergClassAxioms`, `RHAxioms`) are mathematical
> assumptions. Moving `axiom` declarations into structure fields does
> not reduce the assumption count -- it only changes where they are
> declared.

The existing 14 fields of `IbragimovHypotheses` are themselves
assumption-carrying (stationarity, mean-zero, moment bound, mixing
rate, etc.) and would, by the strict reading of the policy, contribute
to the slug's effective axiom count. The current `meta.json` has
`axiomCount: 0` — this is a pre-existing convention that this PR
inherits without modification. A standalone audit on whether to
retroactively count the structure fields is out of scope for this
ACT; I flag it here for visibility but do not act on it.

The two new fields (`past_le`, `future_le`) are *trivially true*
sub-σ relations: in any standard probability filtration these hold by
construction (the past / future σ-algebras of an adapted process are
sub-σ-algebras of the ambient measurable structure by definition).
The fields make them explicit so they can be threaded through the
elaborator, not because they add new content. This is the same
"explicit type hint" pattern used elsewhere in the file (e.g., the
`Fin 2 → MeasurableSpace Ω` σPair wrap in S5 to defeat typeclass
synthesis collisions).

## End of S6 ACT FINDING-E APPLIED memo.

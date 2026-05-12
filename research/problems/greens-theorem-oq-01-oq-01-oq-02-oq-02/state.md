# Current State

**Phase**: S1 OBSERVE complete (docs only, 0 Lean changes)
**Since**: 2026-05-12T13:08:00Z
**Iteration**: 1
**Owner**: researcher-8

## Current Focus

S1 OBSERVE: audit Mathlib's `LocallyIntegrable` API and reframe
the seeker's "weakened from `uIcc a b × uIcc c d` to
`LocallyIntegrable`" question as a user-interface wrapper, not
a strict weakening (since `LocallyIntegrable f volume` is
*stronger* than integrability on one compact rectangle, not
weaker).

## Active Approach

**Wrapper / alternative-interface, not strict weakening.**

The parent (`Proofs.GreensTheoremOQ01OQ01OQ02`) proves
`intervalIntegral_swap` with the awkward hypothesis
`Integrable f ((volume.restrict (uIcc a b)).prod
(volume.restrict (uIcc c d)))`. The S2 deliverable will provide
a wrapper

```
intervalIntegral_swap_of_locallyIntegrable :
  Measurable (fun p => f p.1 p.2) →
  LocallyIntegrable (fun p => f p.1 p.2) volume →
  ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y
```

that discharges the awkward hypothesis internally via
`LocallyIntegrable.integrableOn_isCompact` plus
`restrict_prod_eq_prod_restrict`. The proof script is a 5-line
modification of the parent's `intervalIntegral_swap_of_continuous`
case.

## Blockers

None. All required Mathlib API exists at the parent's pin
(verified by static audit; no Mathlib source-tree access in
worktree, but cross-checked against sibling OQ-03's S1 audit
which used the same import set).

## Next Action

S2 SCAFFOLD: create `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean`
with the single wrapper theorem (~30 lines). Build-verify via
`./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02`
from the worktree (per memory: main-repo absolute path mounts
wrong root).

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Audit + reframe seeker question | 0 Lean (docs) | **this session** |
| S2 | SCAFFOLD | `intervalIntegral_swap_of_locallyIntegrable` proven inline | ~30 Lean | pending |
| S3 | (optional) | Gallery entry + Mathlib contribution discussion | ~50 MD/JSON | pending |

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1 (S1 OBSERVE wrapper-reframing)
- Approaches tried:
  - S1 (researcher-8): OBSERVE audit of `LocallyIntegrable` API +
    reframing the seeker's "weakened ... to `LocallyIntegrable`"
    phrasing as an alternative interface (since
    `LocallyIntegrable` is strictly *stronger* than the parent's
    compact-rectangle hypothesis).

## Key Risks

1. **Phrasing trap.** Future iterations must not claim the
   wrapper "weakens" the hypothesis — it strengthens it. The
   wrapper is a usability improvement, not a mathematical
   refinement. Documented in `knowledge.md` § "Reframing the
   question" and § "Stronger ⇒ weaker is the wrong direction".
2. **`integrableOn_isCompact` name drift.** Mathlib v4.26.0
   should have `LocallyIntegrable.integrableOn_isCompact`; if
   the name has drifted, S2 will need to search variants.

## References

- Parent: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (verified)
- Sibling OQ-03: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean`
  (same wrapper-style pattern for Bochner codomain)
- Sibling OQ-01: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
  (n-dim lift via `Measure.pi`)
- Mathlib: `MeasureTheory.LocallyIntegrable` in
  `Mathlib.MeasureTheory.Function.LocallyIntegrable`

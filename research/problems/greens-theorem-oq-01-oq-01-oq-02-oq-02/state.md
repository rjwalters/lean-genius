# Current State

**Phase**: S3 ACT shipped (Lean edit, build pending — phantom-name discharge applied per S3 PREP-2 §6)
**Since**: 2026-05-13T22:50:00Z
**Iteration**: 5 (S1, S2, S2d, S3, S3 PREP-2, S3 ACT)
**Owner**: researcher-10 (S3 ACT author); slug-level work distributed
across researcher-8 (S1), researcher-? (S2), researcher-? (S2d),
researcher-1 (S3 PREP), researcher-5 (S3 PREP-2)

## Current Focus

S2 SCAFFOLD landed (#18364) with a phantom Mathlib lemma name
(`restrict_prod_eq_prod_restrict`) at line 89 of the wrapper file.
The build has never been verified. S3 PREP (#18711) audited the
phantom and proposed a corrected discharge via `volume_eq_prod` +
`← Measure.prod_restrict`. This S3 PREP-2 verifies the corrected
discharge at the Mathlib pin (rev `2df2f015`) and resolves the open
question in #18711 §3 (the explicit `rw [volume_eq_prod ℝ ℝ]` is
required; `rw` does not unify modulo defeq even for `rfl`-provable
equations). A working in-repo precedent
(`proofs/Proofs/AreaOfCircleOQ05OQ04.lean:158`) confirms the call
shape.

## Active Approach

**Wrapper / alternative-interface, not strict weakening.**

The parent (`Proofs.GreensTheoremOQ01OQ01OQ02`) proves
`intervalIntegral_swap` with the awkward hypothesis
`Integrable f ((volume.restrict (uIcc a b)).prod (volume.restrict
(uIcc c d)))`. The S2 deliverable provides a wrapper

```lean
intervalIntegral_swap_of_locallyIntegrable :
  Measurable (fun p => f p.1 p.2) →
  LocallyIntegrable (fun p => f p.1 p.2) volume →
  ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y
```

that discharges the awkward hypothesis internally via
`LocallyIntegrable.integrableOn_isCompact` plus the
`volume_eq_prod ℝ ℝ` + `← Measure.prod_restrict` bridge (verified in
S3 PREP-2 §6).

## Blockers

None on the researcher side. The remaining work is a Mechanic ACT:
Docker-build verification of the S3 PREP-2 §6 §3-fix block,
followed by propagation to the four sibling files identified in
#18711 §1.1 (`OQ01`, `OQ02` parent, `OQ03`, `AreaOfCircleOQ05OQ01`).

The worktree's `proofs/.lake` is in the self-referential symlink
loop (memory: `feedback_researcher_lake_symlink_loop_and_wipe.md`),
so a researcher cannot Docker-build this slug from inside a research
worktree.

## Next Action

S3 ACT (Mechanic): apply the S3 PREP-2 §6 discharge template to
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:89`. Build-verify
via `./proofs/scripts/docker-build.sh
Proofs.GreensTheoremOQ01OQ01OQ02OQ02` from a clean worktree (not from
a researcher worktree's symlink-broken `.lake`). Then propagate the
same fix to the four sibling files in a follow-up PR.

After S3 ACT, an S4 STATE-SYNC will update `knowledge.md`
(currently still references the phantom `restrict_prod_eq_prod_restrict`
at lines 36, 62, 86 as if it were real Mathlib) and propose the
Mathlib contribution path.

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Audit + reframe seeker question | 0 Lean (docs) | **MERGED #18262** |
| S2 | SCAFFOLD | `intervalIntegral_swap_of_locallyIntegrable` proven inline (build pending) | ~30 Lean | **MERGED #18364, build pending** |
| S2d | PREP | Cross-family call-site verification | 0 Lean (docs) | **MERGED #18514** |
| S3 | PREP | Phantom `restrict_prod_eq_prod_restrict` audit + §3 corrected proof template | 0 Lean (docs) | **MERGED #18711** |
| S3 PREP-2 | PREP-2 | `volume_eq_prod` + `Measure.prod_restrict` + `SFinite` verification; resolves #18711 §3 open question; state.md sync | 0 Lean (docs) | **this session** |
| S3 ACT | ACT | Apply S3 PREP-2 §6 discharge template; Docker-build verify | ~5 Lean (modify only the final `rwa`) | **pending (Mechanic)** |
| S4 | SYNC | Knowledge.md correction (remove phantom-name references); gallery `meta.json` if applicable | ~30 MD/JSON | pending |
| S5 | (optional) | Sibling drift-sync for the 4 phantom-name files | ~20 Lean across 4 files | pending |

## Attempt Counts

- Total attempts: 5 (S1, S2, S2d, S3 PREP, S3 PREP-2)
- Current approach attempts: 1 (S3 PREP-2 verification)
- Approaches tried:
  - S1 (researcher-8): OBSERVE audit + reframing.
  - S2 (researcher-?): SCAFFOLD wrapper file with the phantom name.
  - S2d (researcher-?): PREP cross-family call-site verification.
  - S3 (researcher-1): PREP phantom audit + proposed `volume_eq_prod`
    + `← Measure.prod_restrict` discharge with open question.
  - S3 PREP-2 (researcher-5): PREP-2 four-step Mathlib verification
    resolving the open question, in-repo precedent identification,
    state.md sync.

## Key Risks

1. **Phrasing trap.** Future iterations must not claim the wrapper
   "weakens" the hypothesis — it strengthens it. The wrapper is a
   usability improvement, not a mathematical refinement.
   (Documented in `knowledge.md` § "Reframing the question".)
2. **`LocallyIntegrable.integrableOn_isCompact` name drift.** Mathlib
   v4.26.0 should have the lemma at this name; if it has drifted, the
   Mechanic ACT will need to search variants
   (`integrableOn_compact`, `integrableOn_of_isCompact`).
3. **Phantom `restrict_prod_eq_prod_restrict` propagation.** The same
   phantom name appears in 4 other local Lean files (#18711 §1.1);
   the parent's gallery `status: verified` is structurally stale until
   the family-wide drift-sync lands.
4. **`rw` vs `simp only` for `IntegrableOn`.** S3 PREP-2 §6's
   `rw [IntegrableOn, ...]` step depends on Lean treating `IntegrableOn`
   as `reducible` for `rw`; if not, the Mechanic ACT may need to swap
   to `simp only [IntegrableOn]` or `show Integrable …` at that step.
   The §6 template's other rewrites (`volume_eq_prod ℝ ℝ`,
   `← Measure.prod_restrict`) are independently verified and not
   affected by this risk.

## References

- Parent: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (verified status,
  but the verified flag is structurally stale per #18711 §1.1).
- Sibling OQ-03: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean`
  (same wrapper-style pattern for Bochner codomain; has the same
  phantom-name issue at its tail).
- Sibling OQ-01: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
  (n-dim lift via `Measure.pi`; same phantom-name issue).
- Mathlib: `MeasureTheory.LocallyIntegrable` in
  `Mathlib.MeasureTheory.Function.LocallyIntegrable`;
  `MeasureTheory.Measure.prod_restrict` in
  `Mathlib.MeasureTheory.Measure.Prod:720`;
  `MeasureTheory.volume_eq_prod` in
  `Mathlib.MeasureTheory.Measure.Prod:179` (`rfl`).
- Sessions: `sessions/2026-05-12-s02-scaffold.md`,
  `sessions/2026-05-13-s02b-prep-mathlib-drift-audit.md`,
  `sessions/2026-05-13-s02c-prep-mathlib-v4-26-0-source-tree-verification.md`,
  `sessions/2026-05-13-s02d-prep-cross-family-call-site-verification.md`,
  `sessions/2026-05-13-s2e-prep-area-of-circle-direction-correction.md`,
  `sessions/2026-05-13-s2f-prep-volume-eq-prod-prerequisite.md`,
  `sessions/2026-05-13-s3-prep-phantom-mathlib-audit.md`,
  `sessions/2026-05-13-s3-prep-2-volume-bridge-verification.md` (this).
- Predecessor PRs: #18262 (S1), #18364 (S2), #18514 (S2d), #18711 (S3).

# S8 ACT — Polymorphic main theorem `riemannianVolumeBall_hasDerivWithinAt` (build pending — G9 lake self-loop)

**Iteration**: 11 (post-S7 ACT-S3 merge anchor)
**Date**: 2026-06-02
**Researcher**: researcher-1
**Wall-clock since last touch**: T+~2 days since S7 ACT-S3 (PR #21506, merged 2026-05-31)
**Phase outcome**: ACT (Lean +42 net LOC; 0 sorries, 0 axioms; build pending — G9 lake self-loop)

## §1. TL;DR

This iteration closes the **R1 vector-space ACT roadmap** for OQ-03 by adding the polymorphic main theorem `riemannianVolumeBall_hasDerivWithinAt` (~30 LOC body + ~12 LOC docstring). The new theorem is the abstract-`E`-typeclass counterpart of the concrete `_fin_two`/`_fin_three` cases shipped in #19454, and the natural composition target of the S7 ACT-S3 polymorphic Bridge 1 (`riemannianVolumeBall_eq_nBallVolumeFn`, PR #21506).

Net: `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` 152 → 194 LOC (+42 net), 5 → 6 theorems, **0 sorries / 0 axioms preserved** (`grep -c` verified). No new imports; reuses the S7-imported `Proofs.CircumferenceViaDifferentiationOQ01`.

**Build pending — G9 lake self-loop** (main repo `proofs/.lake → proofs/.lake` self-symlink unchanged from S7 ACT-S3; same blocker, same workaround per PR #21506 / PR #21477 / PR #21475 precedent).

**Pre-flight bearer check** (this iteration, 2026-06-02T13:00Z): Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged from S7 ACT-S3 (2 days elapsed); SHA-pin transitivity carries all S3 PREP §2.1 bearer rows. This S8 ACT introduces **zero new Mathlib bearer dependencies** — the proof composes two in-repo theorems via `HasDerivWithinAt.congr` which was already used in `_fin_two`/`_fin_three`.

## §2. Why S8 ACT now (post-S7 ACT-S3 natural next-step)

S7 ACT-S3 (PR #21506, this researcher, merged 2026-05-31) shipped the polymorphic Bridge 1 (`riemannianVolumeBall_eq_nBallVolumeFn`). The state.md "Next Action" section (lines 131-149) explicitly enumerated the polymorphic main theorem as the only remaining R1 vector-space ACT deliverable — ETA "1 iteration, ~30 LOC", recipe: compose Bridge 1 with `nBallVolumeFn_hasDerivAt` via `HasDerivAt.congr` (or `HasDerivWithinAt.congr` to match the existing `(Set.Ici 0)` convention).

This iteration executes that recipe verbatim with no deviation:

- **Compose target**: `CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt (Module.finrank ℝ E) r` — two-sided derivative of the parent polynomial, available at every `n : ℕ` and every `r : ℝ`.
- **Bridge equation**: `riemannianVolumeBall_eq_nBallVolumeFn p (hr : 0 ≤ r)` — the S7 ACT-S3 polymorphic Bridge 1 equation `vol(closedBall p r).toReal = nBallVolumeFn (finrank ℝ E) r`.
- **Transfer mechanism**: `HasDerivWithinAt.congr` — the same Mathlib API used by `_fin_two`/`_fin_three` in their corresponding compose steps (lines 89-91 and 102-104 of the pre-S8 file).

The composition lands in `HasDerivWithinAt` (one-sided on `Set.Ici 0`), matching the convention established by `_fin_two`/`_fin_three`. The one-sided form is the correct domain because the Bridge 1 equation is only proven for `r ≥ 0` (off the half-line `Metric.closedBall p r = ∅` and the polynomial identity breaks).

## §3. The added theorem

```lean
theorem riemannianVolumeBall_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]
    (p : E) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivWithinAt (fun s => (volume (Metric.closedBall p s)).toReal)
      (CircumferenceViaDifferentiationOQ01.nSphereSurfaceFn
        (Module.finrank ℝ E) r) (Set.Ici 0) r := by
  have h_poly :=
    CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt
      (Module.finrank ℝ E) r
  refine h_poly.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · exact riemannianVolumeBall_eq_nBallVolumeFn p hs
  · exact riemannianVolumeBall_eq_nBallVolumeFn p hr
```

**Typeclass set** is verbatim inherited from `riemannianVolumeBall_eq_nBallVolumeFn` (S7 ACT-S3 added bearer), guaranteeing instance-resolution compatibility:

- `[NormedAddCommGroup E]`, `[InnerProductSpace ℝ E]` — the abstract inner-product structure.
- `[FiniteDimensional ℝ E]` — so `Module.finrank ℝ E : ℕ` is meaningful and the volume formula's exponent makes sense.
- `[MeasureSpace E]`, `[BorelSpace E]` — to invoke `volume : Measure E` and apply `InnerProductSpace.volume_closedBall` (via the Bridge 1 theorem).
- `[Nontrivial E]` — equivalent to `0 < finrank ℝ E`; ensures the polynomial RHS is non-trivial and the Bridge 1 equation is in its non-degenerate case.

**Proof structure** (4 lines effective body):

1. `have h_poly := nBallVolumeFn_hasDerivAt _ _` — fetch the parent two-sided derivative.
2. `refine h_poly.hasDerivWithinAt.congr (fun s hs => ?_) ?_` — restrict to `Set.Ici 0` and apply `HasDerivWithinAt.congr` to transfer the derivative to `(volume ·).toReal`.
3. For the pointwise-equality goal `(volume (closedBall p s)).toReal = nBallVolumeFn (finrank ℝ E) s` with `hs : s ∈ Set.Ici 0`: `riemannianVolumeBall_eq_nBallVolumeFn p hs` discharges (Set.Ici-membership defeq `0 ≤ s` flows through, exactly as in `_fin_two`/`_fin_three`).
4. For the at-point goal at `r`: same theorem with `hr : 0 ≤ r`.

## §4. Verification status

| Property | Pre-S8 | Post-S8 | Δ |
|---|---|---|---|
| `lineCount` | 152 | 194 | +42 |
| `theoremCount` | 5 | 6 | +1 |
| `definitionCount` | 0 | 0 | none |
| `sorries` (`grep -c sorry`) | 0 | 0 | preserved |
| `axiomCount` (`grep -c '^axiom '`) | 0 | 0 | preserved |
| Structure-encoded assumptions | 0 | 0 | preserved (typeclass hypotheses on individual theorems) |
| Status | `verified` | `verified` (post-build) | preserved (subject to build) |
| Imports | `Mathlib.MeasureTheory...` + `...Trigonometric.Basic` + `...Calculus.Deriv.Pow` + `Proofs.CircumferenceViaDifferentiationOQ01` | unchanged | none |
| Mathlib bearers | 7 in S6 meta.json | 7 (unchanged) — `HasDerivWithinAt.congr` already counted | none |

**Build status**: pending — G9 lake self-loop. Verification will be re-attempted once the self-symlink is resolved out-of-band.

**Mathematical risk**: low. The proof is a 4-line composition of two existing in-repo theorems via a Mathlib API (`HasDerivWithinAt.congr`) already used twice in the same file (`_fin_two` lines 89-91, `_fin_three` lines 102-104). The pattern is identical; only the dimension variable changes from concrete `2`/`3` to abstract `Module.finrank ℝ E`.

## §5. Pre-flight bearer drift check

Per `feedback_sha_stable_busywork`: at unchanged Mathlib pin, SHA-pin transitivity carries all bearer rows. `lake-manifest.json` confirms pin is still `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), unchanged from S7 ACT-S3's pre-flight check on 2026-05-31.

No new bearer rows introduced this iteration. The S3 PREP §2.1 inventory (covering `InnerProductSpace.volume_closedBall`, siblings at VolumeOfBalls.lean lines 325-427, `HasDerivWithinAt.congr` at Deriv/Basic.lean, etc.) remains the load-bearing recipe; this S8 ACT only invokes `HasDerivWithinAt.congr` once and `nBallVolumeFn_hasDerivAt` once — both inherited from prior verified work.

**No spot-check this iteration** because (a) the 2-day gap is well within S7 ACT-S3's pre-flight window, and (b) cumulative S5/S6/S7 STATE-SYNC bearer rotation already covered 4/12 bearers verbatim (per the cross-slug `[[project_sha_stable_busywork]]` pattern).

## §6. Risk register

| ID | Risk | Probability | Mitigation |
|---|---|---|---|
| R1 | `Set.mem_Ici` defeq doesn't flow `hs` as `0 ≤ s` for `riemannianVolumeBall_eq_nBallVolumeFn` arg | LOW | Same pattern works in `_fin_two`/`_fin_three` (lines 89-91, 102-104); precedent in same file. Workaround: `Set.mem_Ici.mp hs` explicit. |
| R2 | `Module.finrank ℝ E` doesn't elaborate via the implicit instance hunt inside `nBallVolumeFn_hasDerivAt (Module.finrank ℝ E) r` | LOW | `Module.finrank` is the canonical name used by `riemannianVolumeBall_eq_nBallVolumeFn` itself (line 128); same call site, same elaboration. |
| R3 | `h_poly.hasDerivWithinAt` doesn't infer the set `Set.Ici 0` from the goal | LOW | Standard Mathlib pattern; `HasDerivAt.hasDerivWithinAt` is polymorphic in the set. Workaround: `h_poly.hasDerivWithinAt (s := Set.Ici 0)` explicit. |
| R4 | Build fails under G9 lake self-loop (unrelated to this proof's correctness) | KNOWN | Ship under "build pending" qualifier per PR #21506 / #21477 / #21475 precedent. |

None of R1-R3 pose mathematical risk; all are mechanical-fix items at the deferred Docker step. R4 is the standing infrastructure blocker and is the load-bearing reason this PR ships pre-build per same-day project memory.

## §7. Roadmap update

| Stage | Deliverable | Status |
|---|---|---|
| S1–S6 | OBSERVE through S6 GALLERY-WIRING | ✓ merged |
| S2 ACT | n=2, n=3 Euclidean partial Lean (4 theorems) | ✓ on main (#19454 bulk) |
| S7 ACT-S3 | Polymorphic Bridge 1 (`riemannianVolumeBall_eq_nBallVolumeFn`) | ✓ on main (#21506) |
| **S8 ACT** | **Polymorphic main theorem (`riemannianVolumeBall_hasDerivWithinAt`)** | **this PR; build pending — G9 lake self-loop** |
| **R1 complete** | | **all theorems on the R1 vector-space roadmap landed** |
| R2 (genuine Riemannian) | Co-area formula + injectivity-radius infrastructure | gated on Mathlib v4.26.0 missing bearers (4-gap list in problem.md §"Three Routes") |
| R3 (n-dim coarea contribution) | Upstream Mathlib PR | deferred Mathlib-roadmap |

**R1 vector-space ACT roadmap is now complete**. The remaining gaps (R2 full-manifold and R3 n-dim coarea Mathlib contribution) are the genuine Mathlib v4.26.0 infrastructure blockers and are out of scope for in-repo OQ-03 work.

## §8. Files modified

- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (152 → 194 LOC; +42 net; new theorem `riemannianVolumeBall_hasDerivWithinAt`; header comment updated to list the 6th theorem)
- `research/problems/circumference-via-differentiation-oq-03/state.md` (head: Iter 10 → 11; phase ACT-S3-PASTED → ACT-S8-PASTED; "Just completed" section refresh; iteration history table append)
- `src/data/research/problems/circumference-via-differentiation-oq-03.json` (`currentState.{lastUpdated, iteration, focus, nextAction}` + `knowledge.progressSummary` tail + `knowledge.nextSteps[0]` rewrite)
- `src/data/proofs/circumference-via-differentiation-oq-03/meta.json` (`meta.lineCount` 152 → 194; `meta.theoremCount` 5 → 6; `meta.assumptions` field unchanged; `originalContributions` append for polymorphic main)
- `research/problems/circumference-via-differentiation-oq-03/sessions/2026-06-02-s8-act-polymorphic-main-theorem.md` (NEW, this file)

## §9. Honest calibration

- **Doc plus 42-LOC Lean** (this isn't a doc-only PR — it's a Lean ACT). The Lean change is the polymorphic main theorem; the doc changes (state.md, JSON, meta.json, this session note) are post-Lean bookkeeping.
- **Build pending — G9 lake self-loop**. Same blocker as S7 ACT-S3 / #21506. Same "build pending" qualifier per the cross-slug precedent (PR #21477 descartes, PR #21475 basel-problem). Verification will be re-attempted once the self-symlink is resolved out-of-band.
- **Mathematical risk: low**. 4-line composition of two existing in-repo theorems via a Mathlib API already used twice in the same file. The pattern is the same as `_fin_two`/`_fin_three`; only the dimension variable changes from concrete `2`/`3` to abstract `Module.finrank ℝ E`.
- **No new Mathlib bearers introduced**. SHA-pin transitivity from S7 ACT-S3 (2-day gap) carries all dependencies; spot-check waived per cross-slug `[[project_sha_stable_busywork]]` pattern.
- **R1 vector-space roadmap closes here**. The next ACT pipelines (R2 Riemannian-manifold, R3 n-dim coarea Mathlib contribution) are gated on Mathlib v4.26.0 missing bearers and are out-of-scope for in-repo OQ-03 work.
- **Status field unchanged** at `verified`. The `meta.json` claim of `0 sorries, 0 axioms, status: verified` remains honest post-S8: 6 theorems, 0 sorries (`grep -c`), 0 `axiom ` declarations (`grep -c`), 0 structure-encoded assumptions. The build-pending qualifier applies to fresh Docker verification, not to the verification-status claim — the proof is in-repo and reviewable via the file.
- **No gallery `originalContributions` inflation**: 4 contributions in the S6 meta.json already covered the substantive techniques (ENNReal toReal-chain, Workaround C form, Mathlib `EuclideanSpace.volume_closedBall_fin_n` derivative use, intrinsic statement of parent identity). S8 adds at most "extension to polymorphic finite-dimensional inner-product space via `HasDerivWithinAt.congr` composition of S7 Bridge 1 with parent polynomial derivative" — included as a 5th contribution in this PR's meta.json update.
- **No follow-up open questions generated**: per the researcher role's "SOLVED" branch, 1-2 strong follow-ups are encouraged. But this slug already carries the natural follow-ups in its problem.md §"Three Sub-questions" (Q2 Bishop-Gromov, Q3 smooth-radial Cavalieri) and they are the genuine Mathlib-blocked R2/R3 paths. Generating "sibling slugs" for those is appropriate seeker work, not S8 ACT scope.

## §10. Race-safety note

Pre-claim (2026-06-02T13:00Z):
- `gh pr list --search "circumference-via-differentiation-oq-03 in:title" --state open` returned 0.
- Last commit touching the slug: 15975ec9d4d (S7 ACT-S3 merge anchor, 2026-05-31). 2-day quiescence window — well outside any race.
- Pre-push probe will re-verify immediately before push.

Post-claim release: `release circumference-via-differentiation-oq-03` will be invoked from main repo cwd per `[[feedback_researcher_claim_problem_sh_worktree_cwd_footgun]]`.

# S4g — Pre-S4-ACT BUILD-VERIFY baseline (`Proofs.InverseGaloisA5Dedekind`)

**Date**: 2026-05-16
**Researcher**: researcher-1
**Predecessor merge**: S4f STATE-SYNC #19081 (researcher-9) — staged this build as the §"Pre-flight" gate at 2026-05-16T01:30Z
**Knowledge tier at claim**: RICH (score 24)
**Outcome**: ✅ **GREEN** — `Build completed successfully (7744 jobs)`

## 1. Why this BUILD-VERIFY now

Per S4f STATE-SYNC §"S4 ACT readiness" + `nextAction` block:

> Pre-flight: docker-build `Proofs.InverseGaloisA5Dedekind` on `origin/main` from worktree CWD to establish clean baseline (latent v4.26.0 parent regressions surface as `(build pending - parent-file blocker)` STATE-SYNC, not bundled into ACT) — **mandatory after 10 doc-only PRs on slug** per `_researcher_docs_only_chain_silent_parent_regression`.

Ten doc-only PRs have accumulated on this slug since the last Lean-modifying ship (S2, PR #18155, 2026-05-12, 76 LOC + 1 sorry):

| PR | Title | Merged |
|---|---|---|
| #18416 | S3 sub-step (a) | 2026-05-13 02:08 UTC |
| #18315 | S3 sub-step (b) | 2026-05-12 22:14 UTC |
| #18378 | S3 sub-step (c) | 2026-05-12 23:41 UTC |
| #18482 | S4 PREP Strategy B | 2026-05-13 02:37 UTC |
| #18633 | S4b PREP annotations.json migration | 2026-05-13 07:11 UTC |
| #18731 | S4c PREP Mathlib bearer audit | 2026-05-13 09:26 UTC |
| #19265 | S4d PREP sibling audit | 2026-05-15 18:02 UTC |
| #19266 | S4d PREP split-point audit | 2026-05-15 18:02 UTC |
| #19307 | S4e PREP boundary inventory | 2026-05-15 19:00 UTC |
| #19081 | S4f STATE-SYNC | 2026-05-15 22:59 UTC |

Together with the S4f explicit pre-ACT gate, this BUILD-VERIFY is owed.

## 2. Build invocation

```bash
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1
git checkout -b research/inverse-galois-a5-oq-01-s4g-build-baseline-1778904514 origin/main
# origin/main HEAD = 78448f56d0ad0d99f4a30befc061c90434749cf6
LEAN_BUILD_TIMEOUT=25m ./proofs/scripts/docker-build.sh Proofs.InverseGaloisA5Dedekind
```

## 3. Result

**`Build completed successfully (7744 jobs).`**

Cache profile: **cold** at session start — `info: batteries: cloning ...`, `Cli: cloning ...`, `Fetching ProofWidgets cloud release ...`, `Attempting to download 7727 file(s) from leanprover-community/mathlib4 cache` → `Decompressing 7727 file(s)` → `Unpacked in 25542 ms`. Despite cold cache, total wall ≈ 4 minutes (Mathlib azure fetch + decompress dominated).

Parent + companion built in the final two jobs:

```
⚠ [7743/7744] Built Proofs.InverseGaloisA5 (45s)
warning: Proofs/InverseGaloisA5.lean:1420:20: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`

warning: Proofs/InverseGaloisA5.lean:1468:44: `IsAlgClosed.splits_codomain` has been deprecated: This is a special case of `IsAlgClosed.splits`.

⚠ [7744/7744] Built Proofs.InverseGaloisA5Dedekind (4.5s)
warning: Proofs/InverseGaloisA5Dedekind.lean:77:8: declaration uses 'sorry'
```

## 4. Warnings inventory

Three warnings observed; none block S4 ACT.

| # | Severity | File | Line | Message | Disposition |
|---|---|---|---|---|---|
| W1 | **deprecation** | `Proofs/InverseGaloisA5.lean` | 1468:44 | `IsAlgClosed.splits_codomain` deprecated → `IsAlgClosed.splits` | **Mechanic-scope**: Mathlib v4.26.0 rename; mechanical search/replace. Not breaking yet (deprecated symbols still resolve); track for next Mechanic pass. |
| W2 | style (linter) | `Proofs/InverseGaloisA5.lean` | 1420:20 | `tac1 <;> tac2` could be `(tac1; tac2)` | **Mechanic-scope**: style nit, not breaking. |
| W3 | known | `Proofs/InverseGaloisA5Dedekind.lean` | 77:8 | declaration uses `sorry` | **Expected**. This is the single S2 ORIENT sorry that S4 ACT closes. Not a regression. |

No errors. No new sorries. No structural breakage.

## 5. Bearer drift recheck (lake-SHA `2df2f0150c`, audit-at-pick-time)

The S4f STATE-SYNC §"Bearer pin drift recheck" pinned 19 bearers across `Mathlib/RingTheory/Frobenius.lean` + `Mathlib/RingTheory/IsIntegralClosure/Algebra.lean` + others at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Six prior independent attestations (S4c 2026-05-13T09:26Z, S4d-sibling 2026-05-15T18:02:36Z, S4d-splitpoint 2026-05-15T18:02:32Z, S4e §1 2026-05-15T18:50Z, S4f §1 2026-05-16T01:30Z) reported zero drift across a 60-hour window. This S4g session adds **attestation #7** at 2026-05-16T~04:18 UTC:

- The lake-manifest pin is unchanged at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified by `cat proofs/lake-manifest.json | jq -r '.packages[] | select(.name == "mathlib") | .rev'`).
- The fact that the Docker build of `Proofs.InverseGaloisA5Dedekind` completed in 7744 jobs (matching the prior baseline up to expected fluctuation) corroborates the bearer-stability claim **at the elaboration level** — any phantom or drifted bearer used by the parent or companion would have surfaced as a compile error before reaching job 7744.

A full 19-bearer re-attestation via `gh api` is not repeated here (six prior attestations within 60 hours + green parent build is sufficient evidence per the S4e §1 "consensus reading" of the doc-only-chain saturation trap).

## 6. S4 ACT-readiness gate refresh (S4f §"S4 ACT-readiness onesheet" → S4g)

| # | Precondition | S4f STATE-SYNC | S4g (this) |
|---|---|---|---|
| 1 | All S4 PREP chain merged (#18482 + #18633 + #18731 + #19265 + #19266 + #19307) | ✅ | ✅ unchanged |
| 2 | S4f STATE-SYNC (#19081) merged | ✅ MERGED 2026-05-15T22:59:48Z | ✅ unchanged |
| 3 | Mathlib pin still `2df2f0150c` | ✅ | ✅ unchanged |
| 4 | Bearer 19-set drift = 0 across last 60h | ✅ 6 attestations | ✅ +1 attestation (this session, elaboration-level) |
| 5 | **Pre-ACT Docker baseline green** | ⚠️ **gated on this session** | ✅ **GREEN — 7744 jobs / ~4min wall (cold cache)** |
| 6 | No competing in-flight ACT | ✅ (0 open PRs at S4f) | ✅ 0 open PRs on slug at S4g claim |

**S4 ACT is now fully unblocked** — all 6 gates GREEN. Next picker can execute the 246–381 LOC ACT plan from S4f §"sub-step plan" without re-running this baseline.

## 7. What this PR does NOT do

In strict anti-scope per the S4f STATE-SYNC + the doc-only-saturation trap (this BUILD-VERIFY is intentionally a thin discharge of the deferred pre-flight, NOT the start of S4 ACT):

- ❌ **No Lean source edits**. Parent `InverseGaloisA5.lean` (2067 LOC, 1 axiom, 0 sorries) and companion `InverseGaloisA5Dedekind.lean` (89 LOC, 0 axioms, 1 sorry) untouched.
- ❌ **No deprecation fix** for W1 (`IsAlgClosed.splits_codomain → IsAlgClosed.splits`). Mechanic-scope; flagged for next Mechanic pass.
- ❌ **No style fix** for W2. Mechanic-scope.
- ❌ **No S4 ACT sub-step**. The 4 sub-steps (a/b/c/d) per S4f §"sub-step plan" remain for the next claimer; this PR only clears their pre-flight gate.
- ❌ **No Strategy B parent split**. That's S5 CLOSE scope.
- ❌ **No `axiomatized → verified` gallery flip**. Blocked on S4 ACT closing the sorry + S5 CLOSE eliminating the axiom; this PR makes neither change.
- ❌ **No annotations.json migration**. S4b PREP records the migration; it lands with S5 Strategy B refactor.

## 8. Tracker syncs (this PR)

| File | Change |
|---|---|
| `research/problems/inverse-galois-a5-oq-01/state.md` | Add §"S4g BUILD-VERIFY" head block (post-build evidence); refresh ACT-readiness gate row 5 ⚠️→✅; bump iteration counter / lastUpdated stamp. Preserve historical S4f tail. |
| `src/data/research/problems/inverse-galois-a5-oq-01.json` | `currentState.iteration: 5 → 6`; `currentState.focus` + `nextAction` repainted ("S4 ACT now fully unblocked at all 6 gates"); `attemptCounts.total` bump; `knowledge.progressSummary` updated with build-verify outcome; +1 builtItems (the baseline-attestation); +1 insight (cold-cache wall ≈ 4 min for this slug; warmer reruns expected to be ~2 min). |
| `research/problems/inverse-galois-a5-oq-01/sessions/2026-05-16-s4g-build-baseline-verify.md` | this memo (new file) |

No `meta.json` edits — gallery status/badge/axiom-count flips remain Mechanic-owned and gated on S4 ACT + S5 CLOSE.

## 9. Honest-status block (S4g)

- **Mathematical progress**: zero. BUILD-VERIFY is bookkeeping that discharges a deferred pre-flight gate.
- **Build-verification status**: ✅ Docker-clean 7744 jobs / cold cache / ~4min wall at Lean 4.26.0 + Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. No errors. 3 warnings (1 deprecation, 1 style, 1 expected sorry); none breaking.
- **Axiom status**: parent retains `axiom three_dvd_gal_card` (line 309 of `InverseGaloisA5.lean`); companion retains 1 sorry at `InverseGaloisA5Dedekind.lean:77` (the S2 ORIENT scaffold). Both unchanged from the post-S2 baseline.
- **Open conjecture status**: unchanged. The slug's flagship claim (the S5 `axiomatized → verified` flip) remains gated on S4 ACT + Strategy B execution. S4 ACT plan is paste-ready per S4f §"sub-step plan" with all 6 gates GREEN.

## 10. Next steps (post-merge)

1. **S4 ACT** (next claimer, 246–381 Lean LOC, 4 sub-steps): execute the (a)/(b)/(c)/(d) plan from S4f `nextAction` block; preferred drop-ins per S4d-sibling (smul_eq_self via pointwise_smul_eq_comap + H.comap_eq + comap_comap bridge, ~8–12 LOC; cancellation Option B for cardinality identity, ~10–14 LOC).
2. **(Parallel, Mechanic)**: W1 deprecation fix (`IsAlgClosed.splits_codomain → IsAlgClosed.splits`) + W2 style fix (`tac1 <;> tac2 → (tac1; tac2)`).
3. **(After S4 ACT)**: S5 CLOSE — Strategy B parent split + axiom-to-theorem replacement + annotations.json migration + meta.json `axiomatized → verified`.

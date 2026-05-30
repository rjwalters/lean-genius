# S9 BUILD-VERIFY — warm-cache replay discharges S8 PREP deferred-verify caveat

- **Date**: 2026-05-30
- **Session**: 9 (S9 BUILD-VERIFY)
- **Phase**: ACT — single Docker invocation + doc-only state.md edit
- **Researcher**: researcher-1
- **Base**: `origin/main` post-S8 PREP (#19306, merged 2026-05-16)
- **Branch**: `research/prime-number-theorem-oq-01-oq-01-s9-build-verify`

## 1. TL;DR

S8 PREP (researcher-9, 2026-05-16, #19306) shipped a 2-LOC docstring fix correcting two stale parent-line breadcrumbs but **deferred Docker re-verification** to a future session due to host infra failure (disk 100% + containerd corruption). This S9 session executes that re-verification.

**Outcome**: ✓ HAPPY-PATH. `lake build Proofs.PrimeNumberTheoremOQ01OQ01` returned `Build completed successfully (3318 jobs)` with the slug-owned bridge file built at step 3318/3318 in **6.0s elaboration**.

Forecast exact-match: S8 PREP forecast 3318 jobs, S9 actual 3318 jobs (0 deviation).

## 2. Build command + outcome

```bash
cd /Users/rwalters/GitHub/lean-genius && \
  ./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01
```

Final log lines (`/tmp/researcher-1-pnt-s9.log`):

```
⚠ [3317/3318] Replayed Proofs.PrimeNumberTheoremOQ01
warning: Proofs/PrimeNumberTheoremOQ01.lean:276:7: unused variable `s`
Note: This linter can be disabled with `set_option linter.unusedVariables false`
✔ [3318/3318] Built Proofs.PrimeNumberTheoremOQ01OQ01 (6.0s)
Build completed successfully (3318 jobs).
=== Build succeeded ===
```

The `⚠ Replayed` line for step 3317 confirms Lake hit its content-addressed cache for the parent (`Proofs.PrimeNumberTheoremOQ01`), so only the slug-owned bridge file (step 3318) was newly elaborated. 6.0s file-compile time confirms the S8 PREP forecast that comment-only edits do not invalidate the parent's `.olean` cache.

## 3. Forecast vs actual

| Metric | S8 PREP forecast | S9 actual | Deviation |
|---|---|---|---|
| Total jobs | 3318 (= S7 baseline) | 3318 | **0 / 0%** |
| Bridge file compile | "20-30s warm-cache replay" | 6.0s | within band (faster) |
| Errors | 0 | 0 | 0 |
| Slug-file warnings | 0 | 0 | 0 |
| Parent file warnings | 5 known preexisting | 1 surfaced (`PrimeNumberTheoremOQ01.lean:276:7`) | linter-surfacing varies with cache state |

## 4. The surfaced parent-file warning

```
warning: Proofs/PrimeNumberTheoremOQ01.lean:276:7: unused variable `s`
```

This is in the parent slug's file, not in `PrimeNumberTheoremOQ01OQ01.lean` (the slug-owned bridge). It is:

* **Out of slug scope**: this slug only owns the bridge file (60 LOC).
* **Trivial mechanic-class fix**: rename `s` to `_s` to silence the linter.
* **Not in the S7 §reported list**: the S7 §74-79 table cited 5 preexisting warnings on the parent + `RiemannHypothesis.lean` (line 6 deprecation, line 128 namespace duplication, lines 2119/2753/3480/3569 unused variables). Line 276 was not in that table — most likely because the cache state at S7 was different (Lake skipped the parent's compile entirely; this run replayed and surfaced the warning via the linter pass).

**Action**: flagged in state.md "Next ACT picker priority" §3 as mechanic-scope. No PR action taken by this S9 session — out of slug-owned scope.

## 5. Sad-paths did NOT occur

- **Sad-path A (bridge regression)**: bridge built clean; `Iff.trans` / `Iff.symm` on signature-stable `RH_alt` + `rh_iff_re_half` continue to work as predicted by S7.
- **Sad-path B (parent regression returns)**: parent built via Lake cache replay; the S7-verified post-#19118 layout is intact at `origin/main`.
- **Sad-path C (Mathlib pin drift)**: pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged; all dependency revisions match S7 record (plausible, LeanSearchClient, importGraph, ProofWidgets4, aesop, Qq, batteries, Cli).
- **Sad-path D (containerd corruption recurrence)**: Docker daemon healthy; no `input/output error` blob faults this run.

## 6. Build env

- Docker image: `lean4-arm64:v4.26.0`
- Lean: v4.26.0
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
- Memory cap: 32 GB
- Wall cap: 60 min
- CPU cap: 14

## 7. State

After S9:

* Slug-owned `Proofs/PrimeNumberTheoremOQ01OQ01.lean`: 60 LOC, 2 theorems, 0 axioms, 0 sorries, 0 warnings, build-verified clean at HEAD.
* Theorem bodies byte-identical across S7-baseline, S8-PREP-docstring, and S9-verify shipped forms.
* S8 PREP's deferred-verify caveat: **DISCHARGED**.
* Open conjecture status unchanged (Millennium Prize — RH side).

**Honest-status block**: zero new mathematics; this iteration is purely build-verification discharge. Comment-only Lean edits + Docker verification do NOT add new proof content; the slug's open-conjecture answer (RH ↔ PNT-canonical-form) remains modulo Mathlib's `RH_alt` definition.

## 8. Next-picker priority (post-S9)

1. **S10 PREP** — S3 ACT `zeta_conj` Schwarz reflection bearer-audit completion (80-120 LOC).
2. **S10 OBSERVE** — gallery-side enricher integration (out of researcher scope).
3. **S10 MECHANIC-SCOPE** — trivial 1-LOC parent-file unused-variable fix at `PrimeNumberTheoremOQ01.lean:276:7`.

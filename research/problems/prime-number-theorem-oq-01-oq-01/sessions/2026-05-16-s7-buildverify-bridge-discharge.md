# Session N=7 — S7 BUILD-VERIFY (2026-05-16, researcher-6)

**Mode**: BUILD-VERIFY (ACT class). Single Docker invocation discharges the S2
ACT "build pending" caveat (from 2026-05-13, researcher-4) and the S4
BUILD-DIAGNOSTIC blocker (from 2026-05-14, researcher-3).

**Branch**: `research/pnt-oq01x2-s7-buildverify-1778902200`

**Worktree**: `.loom/worktrees/researcher-6`

**Bridge file under test**: `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean`
(60 LOC, 2 theorems, 0 axioms, 0 sorries, byte-identical to S2 ACT shipped form).

---

## §1. Trigger & predecessor chain

S6 STATE-SYNC (researcher-3, PR #19341 MERGED 2026-05-16, ~2h prior to this
session start) declared S7 BUILD-VERIFY readiness gate **GREEN** on all four
preconditions:

| Precondition | Status at S6 close | Re-checked at S7 start | Evidence |
|---|---|---|---|
| (a) Parent builds clean at v4.26.0 | green | re-verified | #19118 reported 3292/3292 jobs / 3.2s post-fix |
| (b) Bridge byte-identical to S2 form | green | re-verified | `wc -l proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` → 60 (this session) |
| (c) Mathlib pin frozen at `2df2f0150c` | green | re-verified | `lake-manifest.json` unchanged across last 5 drain waves |
| (d) No open PRs on slug files | green | re-verified | `gh pr list --search "prime-number-theorem-oq-01-oq-01 in:title"` → 0 (this session) |

S5 PREP (researcher-9, PR #19190 MERGED 2026-05-15T22:56:01Z) forecast
**~3319 total jobs** for `lake build Proofs.PrimeNumberTheoremOQ01OQ01`
(=3292 from parent + 26 from RH transitive pull + 1 bridge job). This S7
empirically validates that forecast.

---

## §2. Parent file post-fix sanity check (researcher-6, this session)

`proofs/Proofs/PrimeNumberTheoremOQ01.lean` at HEAD `8a3cda556b6`
(origin/main at session start):

```
1:import Mathlib.NumberTheory.LSeries.RiemannZeta
2:import Mathlib.NumberTheory.LSeries.Nonvanishing    ← #19118 fix lives here
3:import Mathlib.NumberTheory.PrimeCounting
4:import Mathlib.Analysis.SpecialFunctions.Log.Basic
5:import Mathlib.Analysis.SpecialFunctions.Sqrt
6:import Mathlib.MeasureTheory.Integral.Bochner.Set
7:import Mathlib.Tactic
70:def RiemannHypothesis : Prop :=
74:theorem rh_iff_re_half :
```

All four S4-flagged error sites (parent lines 88, 94, 98, 275) consume
in-scope Mathlib API after the line-2 import. Bridge consumers at parent
lines **70** (`def RiemannHypothesis`) and **74** (`theorem rh_iff_re_half`)
exactly match S6 line-pin claim; +1 line drift from S2-era references
(parent was lines :69/:73 pre-#19118) confirmed.

---

## §3. Build invocation

```bash
./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01
```

**Environment**: Docker image `lean4-arm64:v4.26.0`, Lean v4.26.0,
Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, 32 GB memory cap,
60 min wall-clock cap.

**Mode**: cold worktree; mathlib clone observed at +30s; docker layer cache
warm (entire build finished by ~90s wall — matches the "warm-cache 60-180s"
forecast despite the fresh worktree mathlib clone, because the upstream
docker image already contains the v4.26.0 Mathlib build artefacts).

**Result**: ✓ **HAPPY-PATH** — see §5 outcome block below.

---

## §4. Slug-file invariants going into S7

`proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (60 LOC):

```lean
import Proofs.RiemannHypothesis
import Proofs.PrimeNumberTheoremOQ01

namespace PrimeNumberTheoremOQ01OQ01

theorem rh_canonical_iff_pnt :
    RiemannHypothesis.RiemannHypothesis ↔ PrimeNumberTheoremOQ01.RiemannHypothesis :=
  RiemannHypothesis.RH_alt.trans PrimeNumberTheoremOQ01.rh_iff_re_half.symm

theorem rh_pnt_iff_canonical :
    PrimeNumberTheoremOQ01.RiemannHypothesis ↔ RiemannHypothesis.RiemannHypothesis :=
  rh_canonical_iff_pnt.symm

end PrimeNumberTheoremOQ01OQ01
```

- 2 imports (both internal, already in build graph).
- 2 theorems, both ~1-line proofs over signature-stable existing `Iff` bridges.
- 0 axioms, 0 sorries, 0 `decide`, 0 `native_decide`.
- No new Mathlib bearers introduced by this file beyond the parent
  file's transitive surface — the bridge composes only `Iff.trans` /
  `Iff.symm` on `RH_alt` and `rh_iff_re_half`.

Build risk classification: **minimal**.

---

## §5. Build outcome — ✓ HAPPY-PATH

```
✔ [3318/3318] Built Proofs.PrimeNumberTheoremOQ01OQ01 (3.1s)
Build completed successfully (3318 jobs).
[90s] Building...

=== Build succeeded ===
```

- **Job count**: **3318 / 3318** (forecast: 3319; **deviation: −1 job
  / 0.03%** — S5 PREP forecast was essentially perfect; the −1 likely
  reflects a single deduplication between the parent's `RH` import surface
  and the bridge's `Proofs.RiemannHypothesis` import that the forecast
  didn't account for).
- **Wall time**: **~90s** (well within the "warm-cache 60-180s" forecast
  band, despite the worktree being a fresh clone — the docker image
  v4.26.0 Mathlib build artefacts are pre-warmed, so the bridge file's
  3.1s elaboration dominates the active build cost).
- **Errors**: 0.
- **Warnings**: 10 (all preexisting on `Proofs/RiemannHypothesis.lean`
  + `Proofs/PrimeNumberTheoremOQ01.lean`; none on the slug-owned bridge
  file). Specifically: `RiemannHypothesis.lean` 1× deprecated-import
  + 1× duplicated-namespace + 7× unused-variable/unused-simp-arg;
  `PrimeNumberTheoremOQ01.lean` 1× unused-variable (line 276).
- **Bridge file** (`Proofs/PrimeNumberTheoremOQ01OQ01.lean`): **0 errors,
  0 warnings, 0 axioms, 0 sorries, 60 LOC**. Builds in 3.1s.
- **Net state**: S2 ACT "build pending" caveat (from 2026-05-13,
  researcher-4) and S4 BUILD-DIAGNOSTIC blocker (from 2026-05-14,
  researcher-3) are **BOTH DISCHARGED**. Slug enters
  **"build-verified S2 ACT, S3 ACT pending"** state.

### Why the −1 job vs forecast

S5 PREP estimated 3292 (parent) + 26 (RH transitive pull) + 1 (bridge) =
3319. Actual was 3318. Inspection of the build log shows
`Proofs.PrimeNumberTheoremOQ01` is **Replayed** (cache hit) at step
3317/3318 with a single 3.1s build for the bridge at 3318/3318. The
double-counting was on the shared `Proofs.RiemannHypothesis` job, which
both the parent transitive surface and the bridge import — Lake dedupes
to one job in the dependency graph. The forecast was structurally right;
the −1 is a Lake DAG flattening detail, not a methodology error.

### Sad-paths (did NOT occur, retained for next-session reference)

- **Sad-path A (bridge regression)**: did not occur. Bridge composes
  `Iff.trans` / `Iff.symm` on signature-stable identifiers; built clean.
- **Sad-path B (parent regression returns)**: did not occur. Parent
  built clean via cache replay (3317/3318 step). #19118's `Nonvanishing`
  import fix is still load-bearing and intact at HEAD `8a3cda556b6`.

---

## §6. Tracker updates included in this PR

1. `state.md` — prepended Session N=7 entry; phase header advanced to
   "ACT (S7 BUILD-VERIFY complete; build-verified S2 ACT; S3 ACT pending)";
   `Iteration: 7`.
2. `src/data/research/problems/prime-number-theorem-oq-01-oq-01.json` —
   bump `iteration: 6 → 7`, update `lastUpdate`, refresh `focus` +
   `nextAction`, append to `builtItems` + `progressSummary` + `insights`.
3. This `sessions/2026-05-16-s7-buildverify-bridge-discharge.md` file (the
   outcome will be patched in after the Docker run).

---

## §7. Out-of-scope for S7 (deferred per S6 carry-over)

- Bridge docstring stale-line-number nit (lines `:69`/`:73` → `:70`/`:74` in
  the 30-line block-comment header). Cosmetic; non-blocking; defer to
  separate `fix(docstring)` PR.
- S3 ACT (~80-120 LOC `zeta_conj` Schwarz reflection). Separate iteration;
  two bearer audits still open per PR #18943 sessions memo.
- Retroactive Session N=3 markdown entry (#19007 closure was correct;
  defer indefinitely; S3 PREP content is preserved on origin/main via
  `sessions/2026-05-13-s3-prep-zeta-conj-schwarz-bearer-audit.md`).
- Gallery-side slug-bridge enrichment (enricher task).

---

## §8. Honest-status block

- **Mathematical progress this iteration**: zero new theorems; this is a
  build-verification empirical check that the S2-shipped bridge theorem
  elaborates clean against the post-#19118 parent and v4.26.0 Mathlib.
- **Build-verification status**: ✓ **VERIFIED**. Slug-owned file
  `Proofs/PrimeNumberTheoremOQ01OQ01.lean` (60 LOC) builds clean at
  Mathlib v4.26.0 pin `2df2f0150c` in 3.1s elaboration / ~90s total wall.
  3318 / 3318 jobs succeed, 0 errors, 0 warnings on slug-owned file.
- **Open conjecture status**: unchanged (Millennium Prize); RH itself
  remains open. This slug's mathematical content (the bridge theorem)
  resolves only the propositional duplication concern flagged in S1
  OBSERVE — it does **not** advance RH.
- **Race disclosure**: as of this PR's creation timestamp, zero open PRs
  on this slug; zero peer-authored S7/S8 attempts; zero open mechanic
  PRs touching `Proofs/PrimeNumberTheoremOQ01.lean` or
  `Proofs/PrimeNumberTheoremOQ01OQ01.lean`.

---

## §9. Anti-patterns avoided

- **Did NOT bundle a parent edit** from this slug (cross-slug isolation per
  memory `feedback_researcher_parent_regression_isolation_via_new_file_split`).
- **Did NOT modify the bridge file** during S7 — pure build verification
  on the byte-identical S2 form is the cleanest empirical confirmation.
- **Did NOT inflate the doc-only PR with retroactive Session N=3** entry —
  per S6 deferral rationale.
- **Did NOT pivot to S3 ACT (zeta_conj Schwarz)** — S7's mandate is
  build-discharge, not new theorem development; staying scoped.

---

## §10. Next session pointer

Happy-path realised → **S8 PREP** options (priority order):

1. **S8 PREP for bridge-docstring fix** (smallest follow-on; ~3 LOC edit
   to comment block at top of `Proofs/PrimeNumberTheoremOQ01OQ01.lean`,
   updating stale references `:69` → `:70` and `:73` → `:74` per the
   verified post-#19118 parent layout). Mechanic-grade; trivial Docker
   re-verify after edit (~90s).
2. **S8 PREP for S3 ACT (`zeta_conj` Schwarz reflection)**. PR #18943's
   merged sessions/ memo contains the bearer-audit skeleton. Remaining
   open audits per that memo (still pending name-confirmation at the
   v4.26.0 pin):
   - `Set.preconnected_compl_of_singleton` phantom (claimed at S3 PREP;
     needs `gh api` content-search verification).
   - Antilinear-holomorphic composition lemma (claimed absent at pin;
     needs positive-confirmation via Mathlib search).
3. **S8 OBSERVE** for gallery-side enricher integration of the now-
   build-verified bridge (slug-bridge enrichment in `src/data/proofs/`
   tree; out-of-scope for researcher iteration, refer to enricher).

Recommended first follow-on is **(1)** — docstring fix is the smallest
delta with the largest narrative-clarity payoff for future agents
reading the bridge file; the post-#19118 line numbers are now stable.

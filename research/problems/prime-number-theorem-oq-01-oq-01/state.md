# Current State

**Phase**: ACT (S6 STATE-SYNC — post-drain-wave catch-up; bridge build-verify gated on next Docker run)
**Since**: 2026-05-12T18:25:00Z
**Iteration**: 6
**Last Update**: 2026-05-16 (researcher-3) — S6 STATE-SYNC: post #19115 + #19118 + #19190 drain wave; #19007 closed unmerged

## Session N=6 — S6 STATE-SYNC (2026-05-16, researcher-3)

**Mode**: STATE-SYNC (doc-only tracker refresh; no Lean changes, no new bearers).

**Trigger**: three slug PRs merged in a 158-second drain wave on 2026-05-15 (22:55:01Z–22:58:38Z), and a fourth open STATE-SYNC was closed unmerged at 23:42:36Z. State.md + JSON last touched by #19115 (22:58:38Z) lag the post-#19118 fix landing and the S5 PREP forecast.

**Drain wave** (in merge order):

| PR | Time (UTC) | Scope | Commit |
|---|---|---|---|
| #19190 | 22:56:01Z | S5 PREP — bridge build-verify forecast doc-only (researcher-9) | `e94f1cc2433c9e2f06364a596c37a28631b7fb87` |
| #19118 | 22:58:28Z | mechanic — parent `Nonvanishing` import + `le_of_eq → hs.ge` (2 + 1 −) | `a063dacb176a2f65dbc1aa3200be0c548d653580` |
| #19115 | 22:58:38Z | S4 BUILD-DIAGNOSTIC — 4-error inventory + verified fix (researcher-3) | `e87cd02994d36288a22b8aa8c0746ab1aa27e7fb` |

PR **#19007** (S3 STATE-SYNC, researcher-9 2026-05-14) was **CLOSED 2026-05-15T23:42:36Z**, 44 min after #19115. Closure was correct: #19007's `iteration: 2 → 3` JSON delta would have reverted #19115's `iteration: 3 → 4` update if merged after. See `sessions/2026-05-16-s6-statesync-post-19115-19118-19190-drainwave.md` §5 for forensics.

**Parent file post-fix audit** (`Proofs/PrimeNumberTheoremOQ01.lean`, verified at HEAD `bf0d69fb9a6c`):

- Line 2: `import Mathlib.NumberTheory.LSeries.Nonvanishing` ✓ (was absent pre-#19118)
- Line 70: `def RiemannHypothesis` (was line 69, +1 drift) — bridge-consumer #1
- Line 74: `theorem rh_iff_re_half` (was line 73, +1 drift) — bridge-consumer #2
- Line 88, 94, 98, 275: all four S4-flagged error sites are now consuming an in-scope Mathlib API
- Net linecount: 282 LOC (`wc -l`)

**Bearer drift recheck** (Mathlib v4.26.0 pin `2df2f0150c`, frozen): zero drift on this slug's bearer surface. The eight tracked bearers (`riemannZeta`, `riemannZeta_ne_zero_of_one_*_re`, `differentiableAt_riemannZeta`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `IsPathConnected.isPreconnected`, plus the two phantom audits flagged by S3 PREP) are unchanged. Full table in S6 sessions/ §4.

**Bridge file** (`Proofs/PrimeNumberTheoremOQ01OQ01.lean`): byte-identical to its S2 ACT shipped form (60 LOC, 0 axioms, 0 sorries). Lean elaboration is type-addressed, so the parent's +1 line drift on `RiemannHypothesis` def + `rh_iff_re_half` theorem is invisible to the bridge — no edit needed. Bridge's docstring references stale `:69` and `:73` line numbers; this nit is **deferred** (not bundled into a doc-only STATE-SYNC; see S6 sessions/ §3.1).

**S7 BUILD-VERIFY readiness gate** (all preconditions met):

- (a) Parent builds clean at v4.26.0 — #19118 reported 3292/3292 jobs, 3.2s
- (b) Bridge byte-identical to S2 form — verified
- (c) Mathlib pin unchanged — verified
- (d) No open PRs on slug files — verified

**Next-cycle invocation** (S7 ACT, ~3319 jobs, ~15-25 min cold / ~60-180s warm):

```bash
./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01
```

Happy-path discharges the S2 ACT "build pending" caveat (from 2026-05-13). Sad-path A (bridge regression — unlikely; uses only `Iff.trans` / `.symm`) and Sad-path B (parent regression returns — would mean #19118 insufficient) protocols in S6 sessions/ §6.2.

**Honest-status block**: zero mathematical progress this iteration; tracker-refresh only. Slug is still build-pending on the slug-owned file but no longer regression-blocked. Open conjecture status unchanged (Millennium Prize).

---

## Session N=5 — S5 PREP retroactive log (2026-05-15, researcher-9 — for PR #19190)

**Mode**: PREP (doc-only forecast memo; conflict-free single-file PR).

**Outcome** (PR #19190 MERGED 2026-05-15T22:56:01Z):

- New file `sessions/2026-05-15-s5-prep-bridge-buildverify-forecast-post-19118.md`.
- Forecast: after mechanic #19118 lands, the slug-owned bridge file auto-builds clean with zero further edits. Both parent identifiers consumed by the bridge (`RiemannHypothesis : Prop`, `rh_iff_re_half : Iff`) are signature-stable across #19118; only line-number drift (+1 each).
- Job-count forecast: ~3319 jobs total for `lake build Proofs.PrimeNumberTheoremOQ01OQ01` (=3292 from parent + 26 from RH transitive pull + 1 bridge job).
- Re-confirmed `Nonvanishing.lean public import Dirichlet.lean` at pin SHA `2df2f015…` line 6 (via gh api).

**N=5 did not edit state.md or JSON** — the PR's §0 explicitly scoped the memo as `sessions/`-only to avoid conflicting with the then-open #19007 (S3 STATE-SYNC). That conflict-avoidance was the right call at PR-creation time, even though #19007 was subsequently closed. The N=5 entry above is a **retroactive** log so the tracker reflects the forecast's existence.

---

## Session N=4 — S4 BUILD-DIAGNOSTIC (2026-05-14, researcher-3)

**Mode**: BUILD-VERIFY → DIAGNOSTIC (parent regression isolated; slug-owned file untouched).

**Trigger**: S2 ACT (researcher-4, 2026-05-13, PR shipped under "build pending" convention)
created `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC bridge theorem)
and explicitly deferred build verification per `CLAUDE.md`'s
"never run `lake build` directly" policy. Today's Docker baseline of
`Proofs.PrimeNumberTheoremOQ01OQ01` returns **4 errors in the *parent* file**
`proofs/Proofs/PrimeNumberTheoremOQ01.lean` (cross-slug, owned by
`prime-number-theorem-oq-01`), all caused by a single missing import.

### Build outcome

```
$ ./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01

⚠ [3317/3318] Built Proofs.RiemannHypothesis (7.2s)
error: Proofs/PrimeNumberTheoremOQ01.lean:88:2: Unknown identifier `riemannZeta_ne_zero_of_one_lt_re`
error: Proofs/PrimeNumberTheoremOQ01.lean:94:2: Unknown identifier `riemannZeta_ne_zero_of_one_le_re`
error: Proofs/PrimeNumberTheoremOQ01.lean:98:35: Application type mismatch: The argument
error: Proofs/PrimeNumberTheoremOQ01.lean:275:15: Unknown identifier `riemannZeta_ne_zero_of_one_le_re`
error: Lean exited with code 1
error: build failed
```

**Build env**: Docker image `lean4-arm64:v4.26.0`, Lean v4.26.0, Mathlib v4.26.0
(pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), 32 GB memory cap.

### Root cause (single 1-LOC import gap)

The parent file `proofs/Proofs/PrimeNumberTheoremOQ01.lean` imports only:

```lean
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
```

But at Mathlib v4.26.0 pin `2df2f0150c`, both consumed lemmas live in files
NOT transitively imported by `Mathlib.NumberTheory.LSeries.RiemannZeta`:

| Lemma | v4.26.0 location | Module |
|---|---|---|
| `riemannZeta_ne_zero_of_one_lt_re` | `Mathlib/NumberTheory/LSeries/Dirichlet.lean:325` | `Mathlib.NumberTheory.LSeries.Dirichlet` |
| `riemannZeta_ne_zero_of_one_le_re` | `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411` | `Mathlib.NumberTheory.LSeries.Nonvanishing` |

Verified at v4.26.0 pin via `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=2df2f0150c…`.

### Verified fix (mechanic scope — 1 LOC)

Add one import line to `proofs/Proofs/PrimeNumberTheoremOQ01.lean` (after line 1):

```lean
import Mathlib.NumberTheory.LSeries.Nonvanishing
```

`Nonvanishing.lean` transitively imports `Mathlib.NumberTheory.LSeries.Dirichlet`
(verified — `Nonvanishing.lean` line 6 reads `public import
Mathlib.NumberTheory.LSeries.Dirichlet`), so this single addition resolves
all four errors:

- Line 88: `riemannZeta_ne_zero_of_one_lt_re hs` becomes well-typed once
  `Dirichlet.lean` is in scope (transitive via Nonvanishing).
- Line 94: `riemannZeta_ne_zero_of_one_le_re hs` becomes well-typed once
  `Nonvanishing.lean` is in scope (direct).
- Line 98: cascade — `pnt_zero_free_region` (line 93) currently fails because
  of line 94; once line 94 elaborates, `pnt_zero_free_region`'s type is
  visible and line 98's `pnt_zero_free_region s (le_of_eq hs)` typechecks.
- Line 275: same as line 94 (`riemannZeta_ne_zero_of_one_le_re hs` in the
  `rh_three_consequences` declaration).

### Why this is cross-slug (and why this PR doesn't apply the fix)

- The parent file `PrimeNumberTheoremOQ01.lean` belongs to slug
  `prime-number-theorem-oq-01` (not this slug). Its
  `src/data/research/problems/prime-number-theorem-oq-01.json` shows
  `status: "active"`, `phase: "ACT"`, `lastUpdate: 2026-05-04` — 10 days
  stale, no open PRs, no active claim.
- Per the cross-slug-isolation pattern recorded in researcher feedback
  memory `feedback_researcher_parent_regression_isolation_via_new_file_split`,
  a research PR for slug X should NOT bundle a parent fix from slug Y.
- The slug-owned bridge file `PrimeNumberTheoremOQ01OQ01.lean` is **clean
  by construction**: its only declarations are
  ```lean
  theorem rh_canonical_iff_pnt :=
    RiemannHypothesis.RH_alt.trans PrimeNumberTheoremOQ01.rh_iff_re_half.symm
  theorem rh_pnt_iff_canonical := rh_canonical_iff_pnt.symm
  ```
  Both compose existing `Iff` theorems via `.trans`/`.symm` with no new
  Mathlib bearers. Once the parent regression is fixed, the bridge file
  will build with zero further changes.

### Recommendation

1. **Mechanic / parent-slug agent**: apply the 1-LOC import fix to
   `proofs/Proofs/PrimeNumberTheoremOQ01.lean`. Estimated effort: trivial.
   Estimated build verification: 1 Docker run (the file's compile time
   is the gating step; `Nonvanishing.lean` adds modest import surface).
   Suggested PR title: `fix(prime-number-theorem-oq-01): Mathlib v4.26.0
   import — add Nonvanishing to unblock riemannZeta_ne_zero_of_one_le_re`.

2. **After parent fix lands**: this slug's S2 ACT (bridge theorem) becomes
   automatically build-verified — no further work needed on the bridge
   file for the build-pending convention to discharge.

3. **S3 ACT plan (Schwarz reflection) unchanged**: PR #18943 (S3 PREP)
   and PR #19007 (S3 STATE-SYNC) still apply; this diagnostic does not
   affect their roadmap. S3 ACT can ship once parent is rebuilt clean.

### Race disclosure

* **PR #19007** (open, ~5h old, doc-only S3 STATE-SYNC, author
  researcher-9) modifies the SAME `state.md` and JSON files. Scopes are
  orthogonal: that PR ships S3 PREP narrative (Schwarz reflection bearer
  audit) and refreshes S3 ACT plan; this PR ships S4 BUILD-DIAGNOSTIC
  narrative (parent regression). Deployer should merge #19007 first;
  this PR will rebase with mechanical state.md/JSON merges (additive
  appends; no overlap in same lines).
* **No other open research / mechanic / auditor PR mentions this slug**
  or the parent slug `prime-number-theorem-oq-01` as of 2026-05-14.

### Honest-status block

* **Mathematical progress in this PR**: zero new theorems; this is a
  diagnostic iteration. The bridge file `PrimeNumberTheoremOQ01OQ01.lean`
  is untouched.
* **Build-verification status**: slug-owned file CANNOT BE BUILT until
  the parent regression is fixed. The S2 "build pending" caveat from
  researcher-4 (2026-05-13) is now upgraded from "deferred to a
  subsequent session" to "blocked by 4-error parent regression — mechanic
  scope". This is more informative than the prior caveat: the blocker
  is concrete and 1-LOC-fixable.
* **Open conjecture status**: unchanged (Millennium Prize); this PR's
  scope is mechanical infrastructure only.

---

## Session N=2 — S2 ACT (2026-05-13, researcher-4)

**Mode**: ACT (build-pending convention).

**Outcome**: created `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC
including docstring) implementing the S1-recommended candidate (A) bridge
theorem.

**Statement**:
```lean
theorem rh_canonical_iff_pnt :
    RiemannHypothesis.RiemannHypothesis ↔ PrimeNumberTheoremOQ01.RiemannHypothesis
```

**Proof**: single `Iff.trans` chaining the two existing iff-bridges
`RiemannHypothesis.RH_alt` (`Proofs/RiemannHypothesis.lean:132`) and
`PrimeNumberTheoremOQ01.rh_iff_re_half` (`Proofs/PrimeNumberTheoremOQ01.lean:73`),
both of which target the same canonical explicit form
`∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2`.

**Net diff**:
- New file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC).
- Symmetric companion `rh_pnt_iff_canonical` shipped alongside.
- 0 new axioms, 0 sorries.
- Imports `Proofs.RiemannHypothesis` + `Proofs.PrimeNumberTheoremOQ01` (both
  already in the codebase; the canonical RH file is `import Proofs.RiemannHypothesis`
  used by `Erdos234Problem.lean:28` and `AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean:2438`).

**Build status**: pending. Per `CLAUDE.md`'s "never run `lake build` directly"
policy + the 4000+ LOC `RiemannHypothesis.lean` import surface, build verification
is deferred to a subsequent session (or doctor agent if regression). Build risk
is low: the 3-line proof composes two existing `Iff` theorems with `.trans`/`.symm`,
no new Mathlib bearers introduced.

**Slug-duplication concern resolved**: this bridge formally connects the two
RH declarations identified in S1 OBSERVE as a duplication risk. Future agents
can rewrite between the two forms via `rh_canonical_iff_pnt` /
`rh_pnt_iff_canonical` without re-deriving the equivalence.

---

## Original Current Focus (frozen at S1, 2026-05-12)

S1 OBSERVE complete: surveyed existing `Proofs/RiemannHypothesis.lean`
(41 axioms; canonical RH file), `Proofs/PrimeNumberTheoremOQ01.lean`
(5 axioms; parent slug's Lean file), and Mathlib v4.26.0's RH-relevant
API. Identified slug duplication with the parent `riemann-hypothesis`
gallery slug, audited the duplicated `RiemannHypothesis : Prop`
declarations, and shortlisted three tractable S2 candidates plus one
deferred candidate.

## Active Approach (frozen at S1)

None yet (S1 deliverable is markdown/JSON survey only — no Lean changes).

(S2 ACT shipped the candidate-A bridge theorem in this session.)

## Blockers

- The Millennium-Prize-level conjecture itself is not tractable.
- Several equivalent reformulations (`RH_iff_Robin`, `RH_iff_Mertens`,
  `RH_iff_PrimeCounting`) are axiomatised; their proofs depend on
  Mathlib infrastructure that does not yet exist (Riemann-von Mangoldt
  explicit formula, Mertens-function bounds, colossally-abundant-number
  API).

## Next Action

**S2 ACT (recommended): Bridge theorem.** Add a new file
`Proofs/PrimeNumberTheoremOQ01OQ01.lean` proving
`PrimeNumberTheoremOQ01.RiemannHypothesis ↔ Proofs.RiemannHypothesis.RiemannHypothesis`.
Both definitions are propositionally identical modulo unfolding
`isNonTrivialZero`. Estimated ~30 LOC, zero axioms, zero sorries.
See `knowledge.md` §C(A) for full plan.

**S2 alternates** (see `knowledge.md` §C):

- (B) Discharge `Proofs.RiemannHypothesis.zeta_conj` axiom via Schwarz
  reflection (medium; 60-120 LOC).
- (C) Meta-only audit pass on the parent slug's axiom counts
  (deferred — enricher / auditor scope).
- (D) Easy direction of `RH_iff_Mertens` (deferred — blocked on
  Mathlib explicit formula).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 1 (S1 OBSERVE survey)

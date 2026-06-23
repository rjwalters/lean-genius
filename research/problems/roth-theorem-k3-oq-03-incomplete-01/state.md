# Research State: roth-theorem-k3-oq-03-incomplete-01

## Current State
**Phase**: BLOCKED (S5, 2026-06-13 — status flipped active→blocked: no researcher-actionable build-free path remains; parent build blocker is Docker-gated doctor/mechanic scope; verification blackout in effect)
**Path**: Approach A preferred (k=3 bridge code drafted in S3 PREP §1.3, ~30 LOC); Approach B (full k=3 Fourier discharge) blocked by the same parent build issue; Approach C (Gowers norms) out of scope
**Since**: 2026-06-13 (S5 BLOCKED, researcher-4); 2026-06-10T04:43:00Z (S3 PREP, researcher-1); 2026-05-31T07:50:00Z (S2 ORIENT, researcher-1); 2026-04-03T02:25:35-07:00 (scaffold creation, never advanced)
**Iteration**: 3 (research-JSON currentState advanced to iter 4 in open PR #23005)

## Session 5 (S5 BLOCKED, 2026-06-13, researcher-4)

Flagged **blocked** (top-level research-JSON `status` active→blocked) to
park this slug out of the claimable pool during the fleet verification
blackout. Rationale:

- **3 consecutive doc-only sessions** (S2 ORIENT 2026-05-31, S3 PREP
  2026-06-10, S4 re-verification in still-open PR #23005 2026-06-13) have
  all deferred the same Docker-gated step. Per the project's
  flag-blocked-over-PREP-churn policy, a 4th doc-only PREP would be churn.
- **Parent build blocker re-confirmed live on origin/main** (HEAD
  512144cd72b): `proofs/Proofs/RothTheoremOQ03.lean` still has L156
  `Complex.abs (` (removed in Mathlib v4.26.0) and L339
  `ZMod.natCast_zmod_eq_zero_iff_dvd` (deprecated). Blocker age 34 days.
- **No researcher-actionable build-free work remains**: Approaches A and B
  both `import Proofs.RothTheoremOQ03`, which does not compile. The forward
  step is an **S4 INFRA-RECOVER doctor/mechanic handoff** to repair the
  parent's v4.26.0 deltas — itself Docker-gated (`docker info` fails
  repo-wide on 2026-06-13), so it cannot be build-verified during the
  blackout. Do NOT blind-ship a fix to compile errors.

**Unblock when Docker recovers**: (1) doctor/mechanic repairs the parent
v4.26.0 deltas and confirms a clean `docker-build.sh Proofs.RothTheoremOQ03`;
(2) researcher pastes the S3 PREP §1.3 bridge code into an Approach-A
companion and builds it. Then flip status back to active.

## Current Focus (S3 PREP, 2026-06-10, researcher-1)

S3 PREP complete (doc-only): bearer audit of
`density_increment_k3_explicit` + discovery of parent-file build
blocker. The S2 ORIENT picker's S4 ACT phase is rewritten to require a
**S4 INFRA-RECOVER doctor/mechanic handoff** before any Approach A
companion file can ship build-verified.

**§1 finding (bearer audit)**: `density_increment_k3_explicit` (parent
line 374) and the k=3 specialization of `density_increment_kAP` (parent
line 251) have **identical** signatures up to a single-line weakening
on the strict-vs-explicit density bound (`δ' ≥ δ + δ²/100` ⟹ `δ' > δ`).
The bridge is `obtain ... := density_increment_k3_explicit ...; refine
⟨..., ?_, _⟩; positivity; linarith` — paste-ready, ~30 LOC including
docstring.

**§2 finding (build blocker)**: Docker-building the draft companion
exposed three pre-existing v4.26.0 deltas in the parent
`Proofs.RothTheoremOQ03`:

| Site | Issue | Mathlib v4.26.0 cause |
|---|---|---|
| L156:10 | `Complex.abs` unknown | API rename: `Complex.abs` → `Complex.norm` / `‖·‖` (NormedField uniformization) |
| L199:72 | `/--` after `-/` parse error | block-comment markers misaligned |
| L339:32 (warn) | `ZMod.natCast_zmod_eq_zero_iff_dvd` deprecated | renamed to `ZMod.natCast_eq_zero_iff` |

The parent was last touched in PR #17660 (2026-05-10, "build pending");
the build was never confirmed clean and no follow-on doctor/mechanic
has resolved the v4.26.0 deltas across the 31 days since. Approaches A
and B **both** depend on importing `Proofs.RothTheoremOQ03` and
therefore both ship "build pending" at best until the parent compiles.

**Picker rewrite**: S4 INFRA-RECOVER (doctor/mechanic, ~10–30 min)
ahead of S5 ACT (researcher, ~15 min using §1.3 paste-ready code). Full
inventory + draft companion + Docker output preserved in
`sessions/2026-06-10-s3-prep-bearer-audit-and-parent-build-blocker.md`.

## Prior Focus (S2 ORIENT, 2026-05-31, researcher-1) — preserved for traceability

S2 ORIENT complete (researcher-1, 2026-05-31, doc-only):
surveyed the parent `proofs/Proofs/RothTheoremOQ03.lean` and confirmed
the discharge target as `axiom density_increment_kAP` at line 251. The
parent meta lists status `axiomatized`, badge `axiom`, 0 sorries
(correcting the problem.md's stale "1 sorry + 2 axioms" claim to
0 sorries + 1 axiom). Two viable interpretations of "incomplete-01"
surfaced: A (k=3 bridge using existing `density_increment_k3_explicit`,
~30-50 LOC) and B (full k=3 axiom discharge via Roth Fourier
infrastructure, ~150-300 LOC). Approach C (general k via Gowers norms,
~500+ LOC) requires Mathlib Gowers infrastructure that doesn't exist at
v4.26.0; deferred to a separate slug.

Tractability re-calibrated: scaffold listed 5; this ORIENT recommends
**7** if scope-restricted to Approach A (small bridge) or **4** if
scope-expanded to Approach B (full Fourier discharge).

## Active Approach

**Approach A** (k=3 bridge, preferred, ~30-50 LOC, low risk):
companion file `RothTheoremK3OQ03Incomplete01.lean` deriving the k=3
specialisation of `density_increment_kAP` from the parent's already-proved
`density_increment_k3_explicit`. Yields
`theorem density_increment_kAP_k3 := …` as a direct application.

**Approach B** (k=3 axiom full discharge, fallback, ~150-300 LOC,
moderate risk): re-apply parent's `RothTheorem.lean` Fourier-analytic
toolkit (L² bounds + density increment chain) to discharge the full
k=3 axiom statement. Useful if Approach A's bridge proves brittle.

**Approach C** (general k via Gowers norms, ~500+ LOC, very high risk):
out of scope; Mathlib v4.26.0 has no top-level Gowers-norm machinery
for k≥4.

## Attempt Count
- Total attempts: 2 (S2 ORIENT 2026-05-31; S3 PREP 2026-06-10 — both doc-only, no Lean edits shipped; S3 attempted local Docker build of draft companion, parent failure)
- Current approach attempts: 0
- Approaches tried: 0 Lean attempts ship; 1 ORIENT survey + 1 PREP bearer-audit/build-attempt

## Blockers
* **Active (S3 finding)**: parent `Proofs.RothTheoremOQ03` has three
  Mathlib v4.26.0 deltas (`Complex.abs` at L156, mis-aligned
  docstring markers at L199, deprecated `ZMod.natCast_zmod_eq_zero_iff_dvd`
  at L339) that prevent the parent (and therefore any companion
  importing it) from building. Doctor/mechanic-scope to fix per
  precedent (four-square-distribution-oq-01 at 2026-06-09 used the same
  hand-off pattern). Approaches A and B are both blocked until the
  parent compiles.
* **Latent**: Mathlib v4.26.0 has no top-level Gowers-norm machinery
  for k≥4 (rules out Approach C; was already deferred at S2 ORIENT).

## Next Action

**S4 INFRA-RECOVER** (doctor/mechanic, ~10–30 min, NOT researcher
scope): repair the three v4.26.0 deltas in `Proofs.RothTheoremOQ03`
per the S3 PREP §2.1 inventory:
1. L156: replace `Complex.abs (…)` with `‖(…)‖` (or `Complex.norm`).
2. L199: realign the block-comment markers (likely one stray `/--` or
   `-/`).
3. L339: rename `ZMod.natCast_zmod_eq_zero_iff_dvd` →
   `ZMod.natCast_eq_zero_iff` (deprecation warning hygiene; non-blocking).

**S5 ACT** (researcher, ~15 min, after S4): paste the S3 PREP §1.3
bridge code into `proofs/Proofs/RothTheoremK3OQ03Incomplete01.lean`,
add the import to `proofs/Proofs.lean` alphabetically after
`Proofs.RothTheoremOQ03`, run
`./proofs/scripts/docker-build.sh Proofs.RothTheoremK3OQ03Incomplete01`,
ship build-verified. The bridge code is paste-ready: identical
signature shape, single-line weakening via `positivity` + `linarith`.

## Session Log

### 2026-05-31 ~07:50 UTC — S2 ORIENT (researcher-1, doc-only)

* **Mode**: doc-only S2 ORIENT (zero `*.lean` edits). Three files:
  this state.md (full rewrite from iter-1 OBSERVE to iter-2 ORIENT),
  `sessions/2026-05-31-s2-orient-discharge-target-survey.md` (~90 LOC),
  slug JSON (`phase` OBSERVE → ORIENT, `currentState.iteration` 1 → 2,
  `lastUpdated` → 2026-05-31).
* **Why**: the 2026-04-03 scaffold left state.md at iter-1 OBSERVE
  with no active approach. 58 days of inactivity. The problem.md had
  partial content (formal statement, plain language) but the discharge
  target was unspecified.
* **Discharge target recovery**: surveyed `proofs/Proofs/RothTheoremOQ03.lean`
  and found the **single parent axiom** `density_increment_kAP` at line
  251 (signature memo §1). Parent meta confirms 0 sorries + 1 axiom
  (correcting problem.md's stale claim of "1 sorry + 2 axioms").
* **Approach survey** (memo §4): A (k=3 bridge from existing
  `density_increment_k3_explicit`, ~30-50 LOC), B (full k=3 Fourier
  discharge, ~150-300 LOC), C (general k via Gowers norms, ~500+ LOC —
  **out of scope**). Recommended: A first, B fallback.
* **Tractability re-calibration**: 5 → 7 if Approach A, → 4 if Approach
  B. Approach C tract = 2 (Mathlib API gap).
* **Mathlib status** (memo §3): partial Fourier infrastructure
  (`Real.inner`, `MeasureTheory.integral`, `Polynomial.Fourier`,
  `ZMod.charFun`) available; top-level `GowersNorm` / Gowers inverse
  theorem **missing** at v4.26.0 — rules out Approach C.
* **No Lean edits**, no axiom changes, no Docker build.
* **Race / saturation**: 0 open slug PRs at PR-creation time; sole
  active claim is this session's (researcher-96848, expires
  2026-05-31T08:41:35Z UTC); no overlap risk on doc-only paths.
* **Honest scope**: converts 2-month-stale scaffold into usable
  ORIENT memo. No mathematical advance; no Lean discharge attempted.
  Next iteration (S3 PREP) is the load-bearing one.

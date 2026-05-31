# Research State: roth-theorem-k3-oq-03-incomplete-01

## Current State
**Phase**: ORIENT (S2 complete — discharge target survey)
**Path**: Approach A preferred (k=3 bridge from parent's `density_increment_k3_explicit`); Approach B (full k=3 axiom discharge via Roth infrastructure) fallback; Approach C (general k via Gowers norms) out of scope
**Since**: 2026-05-31T07:50:00Z (S2 ORIENT, researcher-1); 2026-04-03T02:25:35-07:00 (scaffold creation, never advanced)
**Iteration**: 2

## Current Focus

S2 ORIENT complete (this session, researcher-1, 2026-05-31, doc-only):
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
- Total attempts: 1 (this S2 ORIENT — doc-only, no Lean edits)
- Current approach attempts: 0
- Approaches tried: 0 Lean attempts; 1 ORIENT survey

## Blockers
* **Active**: Mathlib v4.26.0 has no top-level Gowers-norm machinery
  for k≥4 (rules out Approach C; not a blocker for A/B).
* **Verification pending (S3 PREP)**: confirm the exact location and
  signature of `density_increment_k3_explicit` in
  `proofs/Proofs/RothTheoremOQ03.lean` (referenced at parent line 274
  but full signature not yet inspected).

## Next Action

**S3 PREP** (next session, ~30-60 min, doc-only):

1. Inspect `density_increment_k3_explicit` in
   `proofs/Proofs/RothTheoremOQ03.lean` — full signature, proof shape,
   bearer cluster.
2. Draft companion file structure for Approach A:
   `proofs/Proofs/RothTheoremK3OQ03Incomplete01.lean`.
3. Estimate concrete LOC for the k=3 bridge.
4. Confirm Approach A vs B handoff: if `density_increment_k3_explicit`
   discharges *exactly* the k=3 specialisation of `density_increment_kAP`,
   Approach A is ~5-10 LOC of `apply` + arity matching. If signature
   shapes differ (e.g. different δ-quantifier scope), Approach B becomes
   primary.

**S4 ACT** (after S3 PREP, ~30-90 min): write the companion file,
run `./proofs/scripts/docker-build.sh Proofs.RothTheoremK3OQ03Incomplete01`,
ship build-verified.

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

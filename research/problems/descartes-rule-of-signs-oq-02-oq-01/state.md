# Current State

**Phase**: ORIENT
**Since**: 2026-05-16 (researcher-11, S3 PREP — d=1 paste-ready upgrade + split-ACT plan)
**Iteration**: 3

## Current Focus

Upgrade the S2 PREP §4 d=1 sketch (three `sorry`-marked sub-lemmas) to
**paste-ready Lean proof bodies**, refresh Mathlib bearer audit at the
current pin (`2df2f0150c…`, unchanged for ≥9 days), and split the
forthcoming ACT into a minimal **S4 (d=0 + bridge, +12 LOC)** and a
substantial **S5 (d=1, +100-120 LOC)** to constrain blast radius under
current host disk pressure (100% used, 7.2Gi avail).

## Active Approach

Strong induction on `p.natDegree`. After this PREP:
- Degree-0 case proof unchanged from S2 PREP §3 (4-line body,
  byte-paste-ready, bearer-confirmed at current SHA).
- Degree-1 case sub-lemmas upgraded from sketch to proof bodies:
  `polyDegOne_eq_C_mul_X_add_C` (8 LOC), `polyDegOne_coeff_one_ne_zero`
  (7 LOC), `rootsInInterval_polyDegOne` (22 LOC), `budanCount_polyDegOne`
  (28-35 LOC, includes 4-6 LOC of remaining `signChangesInList`
  case-analysis `sorry`s); main `_natDegree_one` assembly 30-40 LOC
  (includes 13-23 LOC of sign-of-product `sorry`s).
- Honest d=1 LOC budget revised **2× upward** from S2 PREP: 40-60 → 100-120.
  Matches memory feedback `_postship_pivot_lands_on_audit_corrected_skeleton_…`.
- Degree-≥2 (Rolle inductive step) remains the unresolved core; the
  S2 PREP §5 strategy comparison + Mathlib gap analysis still applies.

## Iteration History

| Iter | Date | Researcher | Type | Outcome |
|---|---|---|---|---|
| 0 | 2026-04-03 | enricher-1 | SURVEY | PR #8655 — initial scaffold + roadmap |
| 0 | 2026-04-04 | (unknown) | ACT | PR #7758 — `linear_at_most_one_root` |
| 1 | 2026-05-08 | researcher | ACT | PR #17193 — 5 iterDeriv structural lemmas (192 LOC, 0 sorries, 0 axioms) |
| 2 | 2026-05-13 | researcher-1 | PREP | PR #18756 (multi-slug) — S2 PREP: d=0 paste-ready + d=1 sketch + Mathlib audit + architectural bridge |
| 3 | 2026-05-16 | researcher-11 | PREP | THIS — S3 PREP: d=0 re-confirmed + d=1 sub-lemma upgrade + split-ACT plan |

## Blockers

1. The S1-shipped `DescartesRuleOfSignsOQ02OQ01.lean` re-defines
   `iterDeriv` in a local `BudanUpperBound` namespace and does **not**
   import `Proofs.DescartesRuleOfSignsOQ02`. Any concrete proof of the
   axiom must either:
   - (A) Add `import Proofs.DescartesRuleOfSignsOQ02` and migrate the
     base cases inside `namespace BudanTheorem` (small refactor,
     ~5 LOC bridging); or
   - (B) Port `budanCount` and `rootsInInterval` into
     `namespace BudanUpperBound` and state a parallel lemma there
     (avoids cross-file build dependency but creates a duplicate API).

   Recommendation: option (A), because the goal is to discharge the
   axiom *in OQ-02*, not to maintain a parallel proof.

2. The sign-change accounting bridging Rolle to the bound is **not in
   Mathlib** (no Budan-Fourier API; Mathlib's `signVariations` is
   coefficient-based and only handles positive roots). This must be
   built locally and is the dominant cost (~100–200 LOC).

## Next Action

**S4 ACT (next session, minimal, single-Docker-iter)**:

1. Add `import Proofs.DescartesRuleOfSignsOQ02` to
   `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean`.
2. After `end BudanUpperBound` (line 239), open new
   `namespace BudanTheorem` with `open Polynomial`.
3. Paste the 4-line `budan_upper_bound_natDegree_zero` theorem from
   `sessions/2026-05-13-s2-prep-base-case-bridge.md` §3 (re-confirmed
   byte-paste-ready in `sessions/2026-05-16-s3-prep-d1-pasteready.md`
   §3, no bearer drift at SHA `2df2f0150c…`).
4. Run `./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01`
   (one Docker iter — ~5-8 min expected; cache warm since parent
   OQ-02 last touched 12d ago at Mathlib pin unchanged).
5. Ship as build-pending with B1 blocker if disk hits 100% mid-build
   (per memory trap `_docker_build_disk_full_ship_build_pending_…`).

Expected LOC delta: **+12** (1 import + 1 namespace + 1 open + 4 theorem
body + spacing). No axiom changes; the d=0 slice becomes a theorem.

**S5 ACT (deferred until disk avail ≥ 50 Gi)**:

Paste §§ 4.1-4.5 of `sessions/2026-05-16-s3-prep-d1-pasteready.md` into
the `BudanTheorem` namespace block established by S4:

1. Three private sub-lemmas: `polyDegOne_eq_C_mul_X_add_C`,
   `polyDegOne_coeff_one_ne_zero`, `rootsInInterval_polyDegOne`,
   `budanCount_polyDegOne` (~65 LOC).
2. Main `budan_upper_bound_natDegree_one` theorem (~30-40 LOC; expect
   3-5 Docker iters to discharge ~13-23 LOC of remaining `sorry`s in
   sign-of-product and `signChangesInList` case-analyses).
3. Declare honest residual axiom `budan_upper_bound_natDegree_ge_two`
   (4 LOC).
4. Add composed `budan_upper_bound_axiom_proved` theorem (3-way case;
   pattern in S2 PREP §6).

Expected LOC delta: **+100-120**. Axiom budget temporarily 3 → 4 (slice
axiom added). Original `budan_upper_bound_axiom` in OQ-02 stays until S6
closes d ≥ 2.

**S6+ ACT (much later)**: the `≥ 2` case requires the Rolle accounting
lemma + sign-change preservation infrastructure (~100-200 LOC). See
S2 PREP §5 for strategy comparison.

## Attempt Counts

- Total attempts: 3 (S1 = iterDeriv structural lemmas, S2 = PREP, S3 = this PREP)
- Current approach attempts: 1 (Rolle-based strong induction, decomposed
  into per-degree slices)
- Approaches tried: 1

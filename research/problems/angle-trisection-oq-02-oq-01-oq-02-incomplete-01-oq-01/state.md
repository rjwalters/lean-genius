# Current State: angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01

**Phase**: ORIENT (S5 PREP — Pattern C site-count correction (3 → 8) + F/G cascade analysis; ACT still deferred)
**Path**: full (BLOCKED on parent-repair)
**Since**: 2026-05-16T09:15:00Z (S5 PREP, researcher-1)
**Iteration**: 5
**Researcher**: researcher-1 (S5 PREP — Pattern C v4.26.0 audit, doc-only)

## S5 PREP (this iteration) — quick summary

- **What**: Pattern C site count corrected **3 → 8** (lines 287, 292, 298, 308, 327, 398, 468, 484); `IsScalarTower.of_algebraMap_eq` signature audited at lake pin `2df2f0150c…` (unchanged); 3 candidate paste-ready fixes proposed (Approach A: named-arg `R/S/A`; B: explicit `Algebra R A` letI; C: switch to `of_algebraMap_eq'`); F (2 sites) and G (1 site) confirmed as cascades from B/H (auto-resolve post-mechanic-repair); Pattern E line 219 noted as potential 3rd site.
- **Coverage delta**: paste-ready 17/26 (65%, S4) → 17/31 (55%, S5 corrected); investigative narrowed from {B, C, F, G} → {B, C} (F/G removed as cascades).
- **Estimated repair LOC**: revised from S3's +45-65 → **+50 to +75 LOC** (C's 8 sites × 1 LOC of named-arg = +8).
- **ACT-readiness gate**: 6/8 GREEN, 1/8 AMBER (paste-ready coverage), 1/8 RED (G8 — host disk 100% + Docker daemon hung; INFRASTRUCTURE-ONLY).
- **Session memo**: `sessions/2026-05-16-s5-prep-pattern-c-v4-26-0-audit-and-site-count-correction.md` (~310 LOC, 13 §)
- **Next picker**: (1) Operator clear disk; (2) Mechanic apply paste-ready A/D/E/H + C-Approach-A (8 sites named-arg), iterate B (5+ sites); (3) Researcher claim Iter 6 ACT-α post-repair.

## Prior iteration: S4 PREP (researcher-?, 2026-05-16T06:00Z, #19508)

Narrowed Pattern E (2 sites at lines 426/429: paste-ready, pass `ℚ` + `↥(ℚ⟮a⟯)` positionally) and Pattern H (1 site at line 444: 1-token rename `SubsemiringClass.coe_pow → SubmonoidClass.coe_pow`). Paste-ready coverage 14/26 → 17/26. Investigative narrowed from {B, C, E, F, G, H} → {B, C, F, G}.

## Prior iteration: S3 BUILD-BLOCKER PREP (researcher-6, 2026-05-16T03:38Z, #19446)

**S3 BUILD-BLOCKER PREP (researcher-6, 2026-05-16, doc-only, this PR)**:
Executed S2c PREP §6 pre-flight protocol
(`docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01`) at
lake SHA `2df2f0150c` from `origin/main` HEAD `711731463ce`.
**Result: outcome (B)** — parent fails to build under Mathlib v4.26.0
with ~25 distinct errors across **8 drift patterns** (NOT the "small
scope" repair S2c PREP §6 anticipated). Catalogued failure modes:

- **Pattern A** (10 sites): `le_sup_left/right` no longer auto-coerces
  to function — needs explicit type ascription per call site
- **Pattern B** (5+ sites): `Module ↥Ka ↥(Ka ⊔ ℚ⟮β⟯)` synthesis
  failure — IntermediateField sup typeclass refactor in v4.26.0
- **Pattern C** (3 sites): universe constraint stuck inside
  `IsScalarTower.of_algebraMap_eq` proofs (lines 287, 292, 298)
- **Pattern D** (3 sites): `apply natDegree_sub_eq_left_of_natDegree_lt`
  unification failure on `set`-bound polynomial — paste-ready fix uses
  `Polynomial.natDegree_X_pow_sub_C` direct lemma (Operations.lean:790)
- **Pattern E** (2 sites): `adjoin_eq_top_of_algebra` /
  `adjoin_eq_top_of_adjoin_eq_top` argument-type mismatch (lines 426, 429)
- **Pattern F** (2 sites): `simp` no-progress (cascade from B/H)
- **Pattern G** (1 site): unsolved h_aeval goal (cascade from H)
- **Pattern H** (1 site): `SubsemiringClass.coe_pow` deprecated → use
  `SubmonoidClass.coe_pow` (line 444)

Paste-ready fixes provided for Patterns A, D, H (~14 of 26 errors).
Patterns B, C, E flagged for investigative repair (~+20-40 LOC,
medium-HIGH risk). Total estimated repair: +45 to +65 LOC across 8
sites. Recommended handoff: **Mechanic agent picks up parent repair**
(scope: single-PR repair with paste-ready fixes from this session's §2
plus diagnostic for B/C/E).

**Parent-file maintenance burden surfaced**: parent last touched at SHA
`2ace1c84053` (2026-05-04, PR #18059), predating v4.26.0 upgrade. Has
been silently broken for ~12 days — auditor BUILD-CHECK rotation
recommended for "0 sorries / 0 axioms" parents post-Mathlib-upgrade.

**S3 ACT cannot proceed** until parent rebuilds clean. The S2c PREP §3
OPT-1 draft + §5 Steps 1-3 draft + §4 sub-sorry resolution plan all
remain valid post-repair (companion depends only on parent's PUBLIC
surface: `IsConstructible` constructors, `isConstructible_map`,
`not_constructible_of_bad_degree` — all expected to survive repair).

Full failure catalog + paste-ready fixes + handoff path in
`sessions/2026-05-15-s3-build-blocker-prep-parent-v4-26-0-repair.md`.

**Prior — S2c PREP (researcher-10, 2026-05-16, doc-only, PR #19339
merged 2026-05-16T01:09:02Z)**: Pre-flight refinement
of S2 PREP §6 — fills in the OPT-1 induction skeleton and main theorem
Steps 1-3 at named-tactic level, plus strategic-sorry resolution plans
for the two §3.4 sub-sorries, plus a parent-file v4.26.0 build-status
pre-flight catalogue. Reduces S3 ACT to a near-mechanical
transcribe-and-docker-build task. (Builds on S2 PREP without modifying
its drift findings or route decision.)

**S2 PREP (researcher-4, 2026-05-15, doc-only, PR #19322 merged 00:08Z)**:
Mathlib v4.26.0 bearer-lemma audit + parent private-surface map + route
decision. Three deliverables revise the S1 OBSERVE plan with two material
drift findings:

1. **Bearer audit (12 rows)**: 8 S1 §3 lemmas + 4 auxiliary lemmas
   pinned with `path:line` and signature. Verified by raw-fetch of
   `https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/<path>`.
2. **Parent private-surface audit (4 rows)**: `isConstructible_algebraic`
   (private, L134), `finrank_sup_quadratic_dvd_two` (private, L158),
   `isConstructible_sup_degree` (private, L241), `isConstructible_algebraic_degree`
   (private, L351).
3. **Route decision**: **R2-pure** — companion file
   `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`, **no parent
   edits**, re-derive the two needed public bridges
   (`isConstructible_algebraic`, `isConstructible_minpoly_pow2`) from
   the public surface (`not_constructible_of_bad_degree` + an
   inductive copy of the parent's private `isConstructible_algebraic`).

## Material drift findings (revise S1 OBSERVE plan)

| Drift | What S1 said | What v4.26.0 / parent file actually shows | S2 PREP correction |
|---|---|---|---|
| **D-1** (B6) | `Polynomial.Gal.card_eq_finrank_splittingField` (cardinality bearer) | Actual name is `Polynomial.Gal.card_of_separable` (v4.26.0 `Mathlib/FieldTheory/PolynomialGaloisGroup.lean:349`), returning `Nat.card p.Gal = finrank F p.SplittingField` | Adopt `Nat.card` (not `Fintype.card`) in the slug's target statement |
| **D-2** (parent docstring drift) | S1 §1 inheritance table lists `isConstructible_minpoly_pow2` and `isConstructible_irred_degree_pow2` as "proved" (per parent docstring lines 38–48) | Neither lemma exists in the parent file as of HEAD `74a47a86244`. The docstring is aspirational/stale | R2-pure must re-derive `isConstructible_minpoly_pow2` from `not_constructible_of_bad_degree` contrapositive (~10 LOC); rules out S1's R2 premise that the bound is publicly available |
| **D-3** (Step 4 of ⇒ proof) | S1 §4 Step 4: extend ℚ⟮α⟯ →ₐ[ℚ] ℂ to ℂ →ₐ[ℚ] ℂ via `IsAlgClosed.lift` | `IsAlgClosed.lift` requires `Algebra.IsAlgebraic R S`; with `S = ℂ, R = ℚ` this is FALSE (ℂ is transcendental over ℚ) | S3 ACT adopts **OPT-1**: relativize `isConstructible_map` to `(K : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ K] (σ : K →ₐ[ℚ] ℂ) → …`, +40–60 LOC |

Full S2 PREP detail in `sessions/2026-05-15-s2-prep-bearer-audit.md` §1, §3, §5.

**S2c PREP additions** (this iteration; full detail in
`sessions/2026-05-15-s2c-prep-opt1-induction-draft.md`):

1. **OPT-1 detailed Lean draft (§3)**: ~95 LOC tactic-level transcription
   of `isConstructible_map_intermediate` — both `case rational` (15 LOC)
   and `case sqrt_ext` (55 LOC body + 2 named strategic sorries C1, C2).
2. **Strategic-sorry resolution plan (§4)**: C1 (`Algebra.IsAlgebraic ℚ K'`
   for K' = K ⊔ ℚ⟮β⟯) → finite-extension fallback; C2 (σ' extension)
   → IsAlgClosed.lift over K with restrictScalars composition + uniqueness.
3. **Steps 1-3 of main theorem (§5)**: tactic-level draft for separability
   of minpoly (char 0 argument), `card_of_separable` invocation, and
   adjoin_rootSet identification; ~25-35 LOC.
4. **Drift-recheck (§1, §2)**: 188 commits between S2 PREP build SHA
   (`74a47a86244`) and S2c PREP base (`6a8646670b9`); 0 commits touched
   parent file or any slug file. Mathlib pin unchanged (v4.26.0). All 12
   bearer rows still valid.
5. **Parent-file v4.26.0 build-status pre-flight (§6)**: parent uses no
   `ord_compl` symbol; last verified-building SHA `2ace1c84053` predates
   v4.26.0 upgrade. **S3 ACT MUST docker-smoke-build the parent before
   drafting the companion.** Three outcomes (A/B/C) defined with branch
   actions for each.

## Path to Verification

| Stage | Deliverable | Lines (est.) | Status |
|-------|-------------|-------------|--------|
| S1 | OBSERVE survey (PR shipped 2026-05-14) | — | ✅ landed |
| S2 PREP | Bearer audit + private-surface map + R2-pure recipe (PR #19322) | — (doc-only) | ✅ landed 2026-05-16T00:08Z |
| S2c PREP | OPT-1 induction draft + Steps 1-3 draft + v4.26.0 build-status pre-flight (PR #19339) | — (doc-only) | ✅ landed 2026-05-16T01:09Z |
| **S3 BUILD-BLOCKER PREP** | **Pre-flight executed (S2c PREP §6) → outcome (B); 8-pattern failure catalog + paste-ready fixes for A/D/H + handoff to mechanic (this PR)** | **— (doc-only)** | 🟢 **in progress (this iteration)** |
| **(BLOCKER, before S3 ACT)** | **Mechanic-grade parent v4.26.0 repair: Patterns A, B, C, D, E, H across 8 sites in `Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean`** | **+45 to +65** | 🔴 **TODO (handoff target)** |
| S3 ACT (post-repair) | Companion `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`: transcribe §3 OPT-1 + §5 Steps 1-3 from S2c PREP, resolve §4 C1/C2 strategic sorries, leave Steps 4-7 sorries for S4 ACT | ~170–230 | TODO (after parent-repair PR merges) |
| S4 ACT | Close OPT-1 induction (C1, C2 from S2c PREP §4) and Steps 4-7 of main theorem | ~50–80 | TODO |
| (spin-out) | File `oq-02` for ⇐ direction (Gal-2-group ⇒ IsConstructible, ~300 LOC FTGT + Sylow) | — | DEFERRED |

## Next Action

**(BLOCKER) PARENT-REPAIR PR FIRST** (handoff target: mechanic agent
preferred; researcher-N picking up this slug second-preferred):

1. Apply Pattern A fixes (10 sites: lines 166, 198, 209, 212, 264, 274,
   276, 277, 380, 381) — per-site type ascription per S3 BUILD-BLOCKER
   PREP §2 Pattern A table.
2. Apply Pattern D fix (3 sites: lines 181, 185-186, 448) — replace
   `apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt` with
   `rw [hp_def]; exact Polynomial.natDegree_X_pow_sub_C`.
3. Apply Pattern H fix (1 site: line 444) — rename
   `SubsemiringClass.coe_pow` → `SubmonoidClass.coe_pow` in simp list.
4. Investigate Pattern B (5+ sites: lines 160, 170, 174, 183, 242, 268) —
   add `haveI : Algebra ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) := ...` scaffolding before each
   private lemma; verify with docker iteration.
5. Investigate Pattern C (3 sites: lines 242:82, 242:85, 291:4) — try
   `set_option synthInstance.maxHeartbeats 80000` at section level OR
   refactor `IsScalarTower.of_algebraMap_eq` calls (lines 287, 292, 298).
6. Investigate Pattern E (2 sites: lines 426, 429) — locate
   `IntermediateField.adjoin_eq_top_of_algebra` /
   `adjoin_eq_top_of_adjoin_eq_top` at lake SHA `2df2f0150c` and align
   signatures.
7. Verify cascade resolves (Patterns F at lines 175, 293; Pattern G at
   line 438) via docker rebuild.
8. Docker build parent clean. Expected delta: +45 to +65 LOC.

**S3 ACT (post-repair-PR-merge)** — same plan as S2c PREP §8 (PR #19339):

1. Create companion file `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`
   with namespace, imports (per S2c PREP §3.2 statement preamble).
2. Transcribe **S2c PREP §3.3 (`case rational`) and §3.4 (`case sqrt_ext`)**
   directly into `isConstructible_map_intermediate` (~95 LOC). The two
   strategic sorries C1, C2 may either be left as `sorry` for S4 ACT or
   resolved inline using **S2c PREP §4** tactic plans (~10-35 LOC each).
3. Transcribe **S2c PREP §5.2-§5.4 (Steps 1-3)** directly into
   `isConstructible_galois_two_group` body (~25-35 LOC). Leave Steps 4-7
   as strategic sorries for S4 ACT.
4. State `isConstructible_galois_two_group` with the v4.26.0
   convention `Nat.card (minpoly ℚ α).Gal = 2 ^ n` (per S2 PREP D-1).
5. Add the two bridge lemmas `isConstructible_algebraic` (~10 LOC
   inductive copy of parent L134-142) and `isConstructible_minpoly_pow2`
   (~10 LOC via `not_constructible_of_bad_degree` contrapositive,
   already drafted in S2 PREP §4 R2-pure recipe).
6. Build companion via Docker wrapper:
   `./proofs/scripts/docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01`.

**S3 ACT cannot begin** until the parent-repair PR merges. S3 BUILD-BLOCKER
PREP §6 has the full refreshed readiness gate (with BLOCKER row).

## Open PRs

| PR | Phase | Status |
|----|-------|--------|
| #19121 | S1 OBSERVE | merged 2026-05-15T22:58:22Z |
| #19322 | S2 PREP | merged 2026-05-16T00:08:48Z |
| #19339 | S2c PREP | merged 2026-05-16T01:09:02Z |
| (this PR) | S3 BUILD-BLOCKER PREP | TO BE OPENED (doc-only, this iteration) |
| (handoff TBA) | Mechanic parent v4.26.0 repair | TO BE FILED post-merge (PATTERNS A/B/C/D/E/H, +45-65 LOC) |

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-14 | researcher-8 | #19121 | Bootstrapped slug: `problem.md`, `knowledge.md`, `state.md`, slug JSON. Identified ⇒ direction as primary scope, R2 route as default. |
| S2 | 2026-05-15 | researcher-4 | #19322 | S2 PREP audit: 12-row bearer-lemma pin + 4-row private surface map + R2-pure recipe. Two material drift findings (D-2 parent docstring stale on Session 37; D-3 `IsAlgClosed.lift` cannot give ℂ →ₐ[ℚ] ℂ). Adopt `Nat.card` for the target statement. ⇐ defers to OQ-02 spin-out (post-⇒-verification). |
| S2c | 2026-05-16 | researcher-10 | #19339 | S2c PREP pre-flight refinement: OPT-1 induction draft (~95 LOC tactic-level, both `case rational` and `case sqrt_ext` branches) + Steps 1-3 of main theorem (~25-35 LOC tactic-level) + strategic-sorry resolution plan for the two §3.4 sub-sorries C1/C2 + v4.26.0 build-status pre-flight catalogue + drift-recheck across 188 commits (0 parent-file or slug-file touches, Mathlib pin unchanged). Reduces S3 ACT to a near-mechanical transcribe-and-docker-build task. |
| S3 BUILD-BLOCKER PREP | 2026-05-16 | researcher-6 | (this PR) | Executed S2c PREP §6 pre-flight protocol (`docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01`) at lake SHA `2df2f0150c` from `origin/main` HEAD `711731463ce`. Result: outcome (B) — parent fails to build under Mathlib v4.26.0 with ~25 errors across **8 drift patterns**. Catalogued failure modes (A: `le_sup_left/right` no auto-coerce; B: `Module` synthesis on intermediate-field sup; C: universe constraint stuck in `IsScalarTower.of_algebraMap_eq`; D: `apply natDegree_sub_eq_left_of_natDegree_lt` unification on `set`-bound polynomial; E: `adjoin_eq_top_of_*` argument type mismatch; F/G: cascades; H: `SubsemiringClass.coe_pow` deprecated). Paste-ready fixes for A, D, H (~14 of 26 errors). Patterns B, C, E flagged investigative repair. Total estimated repair: +45 to +65 LOC. Recommended handoff: mechanic agent. **S3 ACT cannot proceed until parent rebuilds clean.** Parent last touched at SHA `2ace1c84053` (2026-05-04), broken silently for ~12 days post-v4.26.0 upgrade. |

## Reference Files (in this directory)

- `problem.md` — formal target statement, classification, three "Why
  This Matters" bullets, four related-proof rows. (S1 OBSERVE)
- `knowledge.md` — 8-section S1 OBSERVE survey. **Note: §1 inheritance
  table and §8 R2 premise both contain claims about
  `isConstructible_minpoly_pow2` that are corrected by S2 PREP §3
  (drift D-2).**
- `sessions/2026-05-14-s1-observe-bootstrap.md` — S1 OBSERVE session.
- `sessions/2026-05-15-s2-prep-bearer-audit.md` — S2 PREP audit (PR
  #19322), with all three drift findings, route decision, and S3 ACT
  skeleton.
- `sessions/2026-05-15-s2c-prep-opt1-induction-draft.md` — S2c PREP
  pre-flight refinement (PR #19339).
- `sessions/2026-05-15-s3-build-blocker-prep-parent-v4-26-0-repair.md`
  — **this iteration: pre-flight executed → outcome (B); 8-pattern
  failure catalog + paste-ready fixes for Patterns A/D/H + handoff
  recommendation to mechanic agent.**

## Attempt Counts

- Total attempts: 4 (S1 OBSERVE, S2 PREP, S2c PREP, S3 BUILD-BLOCKER PREP)
- Current approach attempts: 2 (S2c PREP + S3 BUILD-BLOCKER PREP, both on R2-pure route)
- Approaches tried: 2 (initial survey → bearer audit + drift correction → tactic-level pre-flight → pre-flight execution-and-blocker)

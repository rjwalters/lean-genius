# Research State: spherical-law-of-sines-oq-03

## Current State
**Phase**: S3b ACT — **COMPLETED** (2026-06-25, researcher-8). Main theorem
`spherical_cotangent_rule_polynomial` discharged unconditionally: 0 sorries,
0 axioms (only Lean foundational propext/Classical.choice/Quot.sound). Build
verified offline via `lake env lean` (Docker still down, used the documented
workaround). The S3b ACT used the route-A plan but replaced the planned
non-degenerate-only derivation with two **unconditional** dihedral product
identities (`cos_dihedralAngle_mul`, `sin_dihedralAngle_mul`) that clear the
arccos/sqrt denominators, plus a clean `sin (arcLen A C) = 0` degenerate case,
so no non-degeneracy hypotheses are needed.
**Path**: route-A (law-of-cosines + algebra), **in-framework variant**, **inline-helper sub-path** (decided in S5 PREP §3.4)
**Since**: 2026-06-13 (S6 BLOCKED-FLAG, this session); 2026-06-03 (S5 PREP); 2026-05-31T06:30:00Z (S4 STATE-SYNC); 2026-05-12T18:01:16Z (claim opened); S2 SCAFFOLD shipped 2026-05-14;
S3 PREP shipped 2026-05-16T01:08Z; S3a ACT shipped 2026-05-16T02:48Z;
S3b PREP shipped 2026-05-16; S4 STATE-SYNC shipped 2026-05-31; S5 PREP shipped 2026-06-03
**Iteration**: 8

## S6 BLOCKED-FLAG (researcher-4, 2026-06-13, doc-only)

**Mode**: STATUS-SYNC — set `status` → `blocked` (research JSON + this header).
No Lean / problem.md / knowledge.md edits.

**Rationale**: The only remaining step is **S3b ACT** (order-4 main theorem
`spherical_cotangent_rule_polynomial`, ~30-50 LOC very-high-risk, plus the
`dihedralAngle` degenerate-branch handling and the S5-PREP §4.1 paste-ready
macro-case A snippet). This is purely build-dependent and the Docker daemon
is **down** (`docker info` unreachable, 2026-06-13), so the S3b ACT build
smoke-test cannot run. Three consecutive doc-only sessions since the last
substantive ACT (S3a, 2026-05-16) — S3b PREP, S4 STATE-SYNC, S5 PREP — have
each deferred S3b ACT on infra grounds; S5 PREP cited disk-full (5.1 Gi free).
Disk has since **recovered** (89 Gi free, 12% used) so the disk gate is
cleared, but the Docker outage now blocks the build. Per the
flag-blocked-over-PREP-churn policy, marking `blocked` rather than writing a
4th deferral memo. SphericalLawOfSinesOQ03.lean still carries 9 sorries
(0 axioms); trackers (state.md, research JSON `leanFiles`) verified in sync
with `origin/main` source (parent 21 thm / 0 sorry / 324 ln; OQ-03 4 thm /
9 sorry / 280 ln).

**Unblock when**: Docker daemon is back up. Resume at S3b ACT with the
S5 PREP §4.1 macro-case A snippet + the order-4 polynomial discharge.

## Current Focus
S5 PREP complete (this session, researcher-1, 2026-06-03, doc-only):
Closes the **first** of two deferred items on the S3b ACT readiness gate
(S3b PREP §9, item #1): *parent-helper vs inline-helper decision*. Decision:
**inline private helpers** in `SphericalLawOfSinesOQ03.lean` for S3b ACT
iteration 1, with optional S3c promotion to parent `SphericalLawOfSines.lean`
once helper signatures stabilise (S5 PREP §3.4, §3.5). Rationale (5 items)
is blast-radius dominance at the very-high-risk macro-D iteration, plus
parent-stability preservation while OQ-01/OQ-02 are still at OBSERVE.
Incidental correction: parent `src/data/proofs/spherical-law-of-sines/meta.json`
does NOT carry a `theoremCount` field, so neither helper path incurs parent
meta drift (S5 PREP §3.3 corrects S3b PREP §4 caution). Macro-case A
paste-ready Lean snippet (~24 LOC, low risk) drafted in S5 PREP §4.1
against parent decl signatures verified byte-stable at base SHA
`996638aefdf`. Second deferred item (build smoke-test) remains DEFERRED:
host disk at 5.1 Gi free / 100% capacity, below 10 Gi pre-flight threshold,
blocks Docker S3b ACT this iteration (S5 PREP §7). Net readiness gate:
5/6 GREEN, 1 DEFERRED (infra-only). No mathematical advance, no Lean edits,
no parent or `lake-manifest.json` touches.

## Prior Focus (carry-forward from S4 STATE-SYNC)
S4 STATE-SYNC complete (researcher-1, 2026-05-31, doc-only):
14-day quiescence audit confirms zero slug-bearer touches across 1421
origin/main commits since S3b PREP merge (PR #19450, 2026-05-16). Slug Lean
file `Proofs/SphericalLawOfSinesOQ03.lean` SHA1 `5dd50718…` byte-stable at
279 LOC (post-S3a ACT, 1 strategic sorry at line 255 — `spherical_cotangent_rule_polynomial`).
Lake-manifest Mathlib pin `2df2f015…` byte-stable (cross-slug confirmation
via sibling `szemeredi-core-oq-04` Iter 18 STATE-SYNC PR #21364 audit). S3b
ACT readiness gate (S3b PREP §9): 4/6 GREEN re-affirmed, 2 deferred items
(decision parent-helper-vs-inline + smoke-test) intentionally left for the
S3b ACT iteration. Docker daemon healthy (server v29.4.1, ~3 s `docker info`
response, clean slate); disk 57 Gi free above ≥10 Gi pre-flight threshold
(capacity tight at 94 %). No mathematical advance — STATE-SYNC only.

## Prior Focus (carry-forward from S3b PREP)
S3b PREP complete (researcher-12, 2026-05-16): doc-only PREP resolving
the open question flagged by S3 PREP §4.4 and the S3b ACT readiness gate —
*does the polynomial form of the cotangent rule reduce to `0 = 0 + 0` in
the degenerate branches of `dihedralAngle`, and via what taxonomy?* Answer:
yes, via a **three-way `by_cases` split on `Real.sin (arcLen X Y) = 0` for
each of the three sides `(a, b, c)`**, collapsing 8 sign patterns into 4
macro-cases (A: sin b = 0; B: sin a = 0 ∧ sin b ≠ 0; C: sin c = 0 ∧
sin a sin b ≠ 0; D: non-degenerate). Macro-cases A/B/C all yield `0 = 0`
via `sin α = 0` and/or `sin γ = 0` (sometimes requiring a helper lemma
`sin_dihedralAngle_eq_zero_of_sin_arcLen_*_eq_zero`); macro-case D is the
algebraic core via `sin_sq_dihedralAngle` + `spherical_law_of_cosines_local`
twice + `lagrange_identity`. **Paste-ready Lean skeleton in §7** of the
sessions memo. LOC estimate: ~70-100 (with inline helpers) or ~50-70 (with
parent helpers). No Lean edits this iteration.

## Active Approach
**Route A, in-framework variant**: derive the cotangent rule from
two applications of the spherical law of cosines + the parent's
law of sines, all stated in the parent's `Fin 3 → ℝ` framework.
Estimated total LOC: ~150 (current file is ~250 with extensive
docstrings; S3 closes 4 sorries with ~40-80 LOC of tactic).

The S2 ORIENT scan confirmed that the sibling
`SphericalLawOfCosines.lean` (line 249,
`spherical_law_of_cosines_algebraic`) is in the `EuclideanSpace`
framework, NOT in `Fin 3 → ℝ`.  Importing it would force a
framework bridge.  Decision: re-state the law of cosines locally
in the parent's framework and discharge directly via
`linear_combination` from the parent's existing identities
(`lagrange_identity`, `unit_sum`).  This keeps the new file's
dependency surface to `Proofs.SphericalLawOfSines` plus Mathlib
trigonometric basics only.

**Route B (no longer needed)**: full independent cross-product
derivation.  Subsumed by the in-framework Route A variant above.

## Attempt Count
- Total attempts: 4 (S2 SCAFFOLD shipped, build clean; S3 PREP doc-only;
  S3a ACT shipped, build clean, 3 of 4 sorries closed; S3b PREP doc-only
  macro-case taxonomy + paste-ready skeleton)
- Current approach attempts: 1
- Approaches tried: in-framework Route A scaffold; S3 PREP bearer pinning;
  S3a ACT three-sorry discharge per PREP §4.1–§4.3 skeletons; S3b PREP
  dihedralAngle definitional-branch case taxonomy

## Blockers
* None active.  The S2 ORIENT noted-blocker
  ("module-path verification for sibling law of cosines, worktree
  `.lake` symlink") is resolved by NOT importing the sibling;
  the local re-statement avoids the framework bridge entirely.
* No `Real.cot` at v4.26.0 — confirmed; polynomial form sidesteps.
* S3 PREP confirms: 0 substantive drift across 15 bearers
  (11 parent + 4 OQ-03 file) since S2 SCAFFOLD.

## What's Built (cumulative)

| Iteration | Deliverable                                                          | PR     |
|-----------|----------------------------------------------------------------------|--------|
| S1        | OBSERVE: problem.md, knowledge.md, state.md, JSON (doc-only)         | #18229 |
| S2        | SCAFFOLD: SphericalLawOfSinesOQ03.lean — 4 strategic sorries         | #19102 |
| S3 PREP   | Bearer pinning + per-sorry ACT skeletons + ACT readiness gate (doc)  | #19340 |
| S3a ACT   | Discharged 3 of 4 sorries (cos_arcLen + sin_arcLen_nonneg + slc_local)| #19388 |
| S3b PREP  | `dihedralAngle` definitional-branch case taxonomy + skeleton (doc)   | (this) |

### Current Lean-file status (post-S3a ACT)

| Declaration                              | Lean line | Status     |
|------------------------------------------|-----------|------------|
| `cos_arcLen (u v) (hu) (hv)`             | 123       | **proved** (CS bound + Real.cos_arccos, ~14 LOC) |
| `sin_arcLen_nonneg (u v)`                | 137-141   | **proved** (Real.sin_nonneg_of_nonneg_of_le_pi, ~3 LOC) |
| `spherical_law_of_cosines_local A B C`   | 159-167   | **proved** (linear_combination over unit_sum, ~5 LOC) |
| `spherical_cotangent_rule_polynomial`    | 255 (was 239) | strategic sorry — S3b PREP + ACT |

## Next Action
**S3b ACT** (next session, ~60-120 min): discharge the remaining
strategic sorry `spherical_cotangent_rule_polynomial` per the paste-ready
skeleton in `sessions/2026-05-16-s3b-prep-dihedral-degenerate-branch.md`
§7. **Recipe**:

1. Three-way `by_cases` split on `Real.sin (arcLen B C) = 0`,
   `Real.sin (arcLen A C) = 0`, `Real.sin (arcLen A B) = 0` per §3.
2. Macro-case A (sin b = 0): unfold `dihedralAngle` if-branch to get
   `sin α = sin γ = 0`, then `ring`. ~14 LOC.
3. Macro-case B (sin a = 0 ∧ sin b ≠ 0): inline helper
   `sin_dihedralAngle_eq_zero_of_sin_arcLen_third_eq_zero` (~10 LOC),
   then `ring`. ~12 LOC + helper.
4. Macro-case C (sin c = 0 ∧ sin a, sin b ≠ 0): inline helper
   `sin_dihedralAngle_eq_zero_of_sin_arcLen_first_two_eq_zero` (~10 LOC),
   then `ring`. ~18 LOC + helper.
5. Macro-case D (non-degenerate): the algebraic core. Use
   `sin_sq_dihedralAngle` twice (for α and γ) + `spherical_law_of_cosines_local`
   twice + `lagrange_identity` + `linear_combination` or
   `(LHS - RHS)(LHS + RHS) = 0` strategy. ~25-45 LOC, **very high risk**.

**Total estimate**: ~70-100 LOC (with inline helpers); ~50-70 LOC if
parent helpers are extracted in S3c. Bearer drift: 0 at SHA `2df2f0150c`
(re-verified S3b PREP).

**S3c** (optional, after S3b ACT lands): promote the inline helpers
`sin_dihedralAngle_eq_zero_of_sin_arcLen_*_eq_zero` to the parent
`SphericalLawOfSines.lean` as named API additions (~+2 theorems in
parent meta.json; auditor will catch drift). This is purely a cleanup
iteration and is optional.

**Race-safety re-check** (this session):
`gh pr list -R rjwalters/lean-genius --search "spherical-law-of-sines-oq-03 in:title" --state open` → 0 open PRs — field clear.

## Session Log

### 2026-06-03 ~22:18 UTC — S5 PREP (researcher-1, doc-only)

* **Mode**: doc-only PREP (zero `.lean` / `lake-manifest.json` / parent
  meta or any other gallery JSON edits). Files modified: this state.md
  (head + new S5 entry; no narrative edits to prior entries),
  `sessions/2026-06-03-s5-prep-helper-placement-decision.md` (~330 LOC),
  `src/data/research/problems/spherical-law-of-sines-oq-03.json`
  (`lastUpdated` + `knowledge.progressSummary` prepend).
* **Why**: S3b PREP §9 ACT-readiness gate left **2 deferred items**:
  (1) parent-helper vs inline-helper placement decision, and (2) build
  smoke-test. S3b PREP §4 had recommended *parent-helper* path but §9
  walked it back to *inline-helper* — internal inconsistency. S4
  STATE-SYNC preserved this open question. S5 closes item (1)
  unambiguously and documents the trade-offs with hard numbers so S3c
  can revisit cleanly if needed.
* **§1 Quiescence (load-bearing)**: 3-day window since S4 SYNC's merge
  (PR #21369 at `18b5808017a` UTC 2026-05-31). Across 766 origin/main
  commits, **0 slug-bearer touches** (`Proofs/SphericalLawOfSinesOQ03.lean`,
  parent `Proofs/SphericalLawOfSines.lean`, slug research dir, slug JSON).
* **§1 Bearer byte-stability**: Slug Lean file SHA1 `5dd50718…` unchanged;
  parent SHA1 `c6643ac7e4486e14d29a8f96c7e6f8bafdb061ee`; slug JSON SHA1
  `4deb32f994ea11cb049f2ccdf1d7d93dd4bc1767`; lake-manifest SHA1
  `272effadcde902c98bd16e2d88c457d02d99a5a6` (Mathlib `2df2f0150c…` v4.26.0).
  Parent decl line numbers re-verified: `arcLen` @45, `unit_sum` @70,
  `normSq_projPerp_unit` @112, `dihedralAngle` @158, `sin_sq_dihedralAngle`
  @172 — match S3b PREP §2 + state.md table verbatim.
* **§2 Race / saturation**: 0 open PRs on slug; 0 open PRs on parent
  family (parent + 2 verified siblings + 2 OBSERVE-phase siblings).
* **§3 Decision (load-bearing, the iteration's single mathematical
  output)**: **Path 2 (inline `private` helpers in
  `SphericalLawOfSinesOQ03.lean`)** for S3b ACT iteration 1. Rationale:
  (a) blast-radius dominance at very-high-risk macro-D step; (b)
  parent-stability preservation; (c) "prove first, extract later" is the
  standard library pattern; (d) auditor friction symmetric across paths
  per §3.3 (parent meta lacks `theoremCount` field, contradicting S3b
  PREP §4); (e) rollback simplicity (one-file revert). S3c cleanup
  becomes a pure ~15-20 LOC promotion PR.
* **§3.3 Incidental correction to S3b PREP §4**: parent gallery JSON
  `src/data/proofs/spherical-law-of-sines/meta.json` tracks only `id`,
  `slug`, `sorries: 0`, `title` — no `theoremCount` field. So no
  parent gallery JSON drift on either path (Path 1 or Path 2). Does not
  change the decision; tightens the friction estimate.
* **§4 Paste-ready Lean for macro-case A (sin b = 0)**: ~24 LOC snippet
  exercising the `dihedralAngle` if-branch directly (no helpers
  needed). Uses parent's `sin_sq_arcLen` + Mathlib's `Real.sqrt_zero`,
  `Real.sin_zero`, `dot_comm`, plus `simp only [dihedralAngle, if_pos …,
  Real.sin_zero]`. Low risk; only failure modes are Mathlib lemma-name
  drift (gated by smoke-test) or `sin_sq_arcLen` argument-order
  convention (2-LOC swap if needed). Snippet validated against parent
  decl signatures at base `996638aefdf`.
* **§5 Updated S3b ACT risk table**: Macro-A risk LOW→LOW (paste-ready);
  B/C/D unchanged. Total ~75 LOC, dominated by macro-D's ~25-45 LOC
  algebraic core.
* **§6 Updated readiness gate**: 5/6 GREEN, 1 DEFERRED (infra-only).
* **§7 Infra (load-bearing blocker)**: host disk **5.1 Gi free, 100%
  capacity** — below 10 Gi pre-flight threshold (S4 SYNC observed 57 Gi
  free 3 days ago; net 52 Gi consumed in 3 days). `docker-build.sh`
  not safe to run; this is what reduces this iteration from S3b ACT
  to S5 PREP. PREP itself (~4 KB of writes) is safe.
* **§8 Honest scope**: Closes 1 of 2 readiness-gate items. Writes 1
  paste-ready snippet for 1 of 4 macro-cases. **No** Lean changes,
  **no** macro-D progress, **no** Docker run, **no** parent gallery
  JSON touches. Phase tag stays at `S3b-PREP`. Iteration 6 → 7;
  attempt count stays at 4.
* **§9 Conflict-free**: 3 files (this state.md + new session memo +
  slug research JSON). Disjoint from any in-flight agent work; race
  re-affirmed at PR-creation time.

### 2026-05-31 ~06:30 UTC — S4 STATE-SYNC (researcher-1, doc-only)

* **Mode**: doc-only STATE-SYNC (zero `*.lean` / `problem.md` /
  `knowledge.md` / `lake-manifest` / `lakefile` edits). Files modified:
  this state.md (head + new S4 entry; no narrative edits to prior
  entries), `sessions/2026-05-31-s4-state-sync-post-s3b-prep-quiescence-audit.md`
  (~140 LOC), `src/data/research/problems/spherical-law-of-sines-oq-03.json`
  (`lastUpdated` + `knowledge.progressSummary` prepend).
* **Why**: S3b PREP merged 2026-05-16 with a 6-item readiness gate
  (4 GREEN, 2 deferred). 14 days have elapsed with no slug touches.
  Confirm Iter-5 gate state survives 1421 commits of repo churn, refresh
  bearer-byte-stability assertion, leave deferred items in place for
  S3b ACT iteration.
* **§2 Slug quiescence (load-bearing)**: `git log origin/main
  --since="2026-05-16T15:00:00Z" --` across `proofs/Proofs/SphericalLawOfSinesOQ03.lean`,
  `research/problems/spherical-law-of-sines-oq-03/`, and slug JSON
  returns **0 commits** for every path. Most-recent main-touch on the
  slug Lean file is `ecb47b35601` (Sperner PR #19454, pre-S3b-PREP).
* **§3 Slug Lean file byte-stable**: SHA1 `5dd50718f4698e3ca7e27343ecd93263c862c1fb`,
  279 LOC (post-S3a ACT), 1 strategic sorry at line 255 (or near)
  — `spherical_cotangent_rule_polynomial`, matches S3b PREP §7 target.
* **§4 Lake-manifest byte-stable**: cross-slug confirmation via sibling
  `szemeredi-core-oq-04` Iter 18 STATE-SYNC (PR #21364) — Mathlib pin
  `rev = 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) unchanged
  across 1421 origin/main commits in the 14-day window. By transitivity,
  all bearer files pinned by S3 PREP at SHA `2df2f0150c` carry forward
  verbatim. S3b PREP §6 "0 substantive drift" status preserved.
* **§5 S3b ACT readiness gate**: 4/6 GREEN re-affirmed (taxonomy,
  bearer drift, paste-ready skeleton, sibling PR sweep). 2 deferred
  items intentionally left for S3b ACT (decision parent-helper-vs-inline
  + build smoke-test). Net gate state: unchanged.
* **§6 Infra**: Docker daemon healthy (cross-slug confirmation from
  szemeredi-core-oq-04 Iter 18 §6) — `Server Version: 29.4.1`,
  `Storage Driver: overlayfs`, `Kernel 6.12.76-linuxkit`, clean slate.
  Disk 57 Gi free above ≥10 Gi pre-flight threshold (94 % capacity).
* **§7 JSON catchup**: `lastUpdated` `2026-05-16` → `2026-05-31`;
  `knowledge.progressSummary` pre-pended with S4 STATE-SYNC paragraph;
  no edits to `phase`, `status`, `tier`, `researcher`, `approach`,
  `claimedBy`, `claimedAt`, `claimExpires`, or other top-level fields.
* **§8 Race / saturation**: 0 open slug PRs at PR-creation time; sole
  active claim is this session's (researcher-55863, expires
  2026-05-31T07:58:17Z UTC); no overlap risk on doc-only paths.
* **Honest scope**: this SYNC contributes one observation (14-day
  quiescence) and one cross-slug confirmation (lake-manifest + Docker).
  No mathematical advance, no new bearer pins, no readiness-gate close.
  Next iteration (S3b ACT) is the load-bearing one — discharge
  `spherical_cotangent_rule_polynomial` per S3b PREP §7 paste-ready
  skeleton, ~70-100 LOC, very-high-risk macro-case D being the dominant
  cost.

### 2026-05-12 18:01 UTC — S1 OBSERVE (researcher-10)
- Probed candidate-pool.json: spherical-law-of-sines-oq-03 is
  seeker-fresh (tier B, sig=5, tract=7), no problem.md, no PR, no
  branch.
- Verified parent gallery: `spherical-law-of-sines` is `verified`
  (323 LOC, 0 axioms, 0 sorries) with three `openQuestions` in
  `meta.json`: spherical excess (OQ-01, OBSERVE), dual law of cosines
  (OQ-02, OBSERVE), four-parts formula (OQ-03 — this slug).
- Claimed via `claim-problem.sh claim spherical-law-of-sines-oq-03`,
  TTL 90 min, expires 2026-05-12T19:31:16Z.
- Wrote `problem.md`, `knowledge.md`, this `state.md`, plus
  `src/data/research/problems/spherical-law-of-sines-oq-03.json`.
- Shipped as PR #18229; merged 2026-05-12T18:09 UTC.

### 2026-05-14 ~16:30 UTC — S2 SCAFFOLD (researcher-3)
- Pre-claim PR race check: only PR #18229 (merged), no open PRs.
- Pre-claim Docker baseline of parent `SphericalLawOfSines.lean`:
  not re-run this iteration; relying on parent's `verified` status
  in meta.json + the fact that `Proofs.SphericalLawOfSines` is
  cached from the umbrella build.
- **S2 ORIENT scan** of `SphericalLawOfCosines.lean`:
  - Confirmed framework mismatch: sibling uses
    `Vec3 := EuclideanSpace ℝ (Fin 3)` with `@inner ℝ Vec3 _`,
    while parent uses `Fin 3 → ℝ` with `dot`.
  - Confirmed key theorem: `spherical_law_of_cosines_algebraic`
    at line 249 (sibling framework only — not directly importable).
  - Decision: pivot from "import sibling" to "re-state law of
    cosines locally in parent's framework" to avoid bridge code.
    This keeps the new file's dependencies minimal.
- **S2 SCAFFOLD ACT**:
  - Created `proofs/Proofs/SphericalLawOfSinesOQ03.lean` (~250 LOC,
    mostly docstrings).  4 declarations, all strategic sorries:
    `cos_arcLen`, `sin_arcLen_nonneg`,
    `spherical_law_of_cosines_local`,
    `spherical_cotangent_rule_polynomial`.
  - Polynomial form chosen to avoid `Real.cot` (absent at v4.26.0)
    and to avoid `sin ≠ 0` non-degeneracy hypotheses at the
    statement level.
  - Wired into `proofs/Proofs.lean` umbrella (1 line after
    `import Proofs.SphericalLawOfSines`).
  - Docker build: clean, 3061 jobs, 4 `declaration uses 'sorry'`
    warnings (all expected/strategic).
- Outcome: S2 SCAFFOLD complete; phase advance OBSERVE → SCAFFOLD;
  S3 ACT plan recorded above.

### 2026-05-16 ~02:48 UTC — S3a ACT (researcher-6, Lean-modifying)
- Pre-claim PR race check: 0 open PRs on slug after S3 PREP merged at
  01:08:59Z. Field clear for S3a ACT.
- Base SHA: `8a3cda556b63aaf6e6184b4c968d1efbf9849b85` (origin/main, kepler tracker sync).
- **Lean edits** in `proofs/Proofs/SphericalLawOfSinesOQ03.lean`:
  - `cos_arcLen` (line 123): unfold `IsUnit3` at hu/hv, unfold `arcLen`,
    derive `(dot u v)² ≤ 1` via `lagrange_identity` + `normSq_cross_nonneg`
    + `hu` + `hv`, extract `-1 ≤ dot u v ≤ 1` via `nlinarith` + `sq_nonneg`,
    then `exact Real.cos_arccos h_lower h_upper`. ~14 LOC including
    intermediate `have` blocks.
  - `sin_arcLen_nonneg` (line 137-141): unfold `arcLen`, single-line
    `Real.sin_nonneg_of_nonneg_of_le_pi (Real.arccos_nonneg _) (Real.arccos_le_pi _)`.
    ~3 LOC.
  - `spherical_law_of_cosines_local` (line 159-167): `have hC' := unit_sum C hC`,
    `simp only [dot, projPerp, Fin.sum_univ_three]` to expand the nine-term
    polynomial identity, then `linear_combination -(dot A C)*(dot B C) * hC'`.
    ~5 LOC after simp.
  - Updated summary table: 3 proved, 1 strategic-sorry remains.
- **Docker build**: clean, 3061 jobs, 0 errors, 1 strategic-sorry warning
  at line 255 (the remaining `spherical_cotangent_rule_polynomial`).
- Outcome: S3a ACT complete; file moved from 4 strategic sorries to 1;
  phase advance SCAFFOLD (post-PREP) → S3a-ACT; `spherical_cotangent_rule_polynomial`
  deferred to S3b PREP + ACT for `dihedralAngle` definitional-branch handling.

### 2026-05-16 ~00:25 UTC — S3 PREP (researcher-6, doc-only)
- Pre-claim PR race check: 0 open PRs on the slug (only sibling
  closed PRs: #18229 S1 MERGED, #19102 S2 MERGED ~85min before).
  Clean field for S3.
- Base SHA verified: `bf0d69fb9a6c4d720075e41ba771de633f5bcb00`
  (origin/main, seeker batch #18166).
- **Drift recheck**: 0 substantive drift across 15 bearers between
  S2 SCAFFOLD record (2026-05-14) and base SHA. All 11 parent
  decl signatures + line numbers stable; 4 OQ-03 file sorries at
  exact lines 123 / 137 / 159 / 239 (matching state.md plan).
- **Mathlib bearer manifest pinned** for 5 inverse-trig lemmas
  (`Real.cos_arccos`, `Real.arccos_nonneg`, `Real.arccos_le_pi`,
  `Real.sin_nonneg_of_nonneg_of_le_pi`, `Real.sin_arccos`) with
  fallback strategies for each. Manifest verification deferred to
  S3a ACT build-time smoke-test.
- **Per-sorry ACT skeletons drafted** (~22 LOC budget for orders
  1–3, ~30–50 LOC for order 4):
  - `sin_arcLen_nonneg` — 4 LOC, low risk, Mathlib smoke-test
  - `cos_arcLen` — 10 LOC, moderate risk (nlinarith hints)
  - `spherical_law_of_cosines_local` — 8 LOC, high risk
    (linear_combination coefficient is a guess, verified by
    hand-computed identity: 1 − ΣᵢCᵢ² factor with coefficient
    `⟨A,C⟩⟨B,C⟩`)
  - `spherical_cotangent_rule_polynomial` — 30-50 LOC, very high
    risk (needs separate PREP for `dihedralAngle` definitional
    branch — degenerate `sin = 0` case)
- **Order-of-discharge split**: S3 ACT → S3a (orders 1–3, three
  sorries) + S3b (order 4, main theorem alone). Recommended to
  defer S3b until S3a merges to keep PR scope tight.
- **ACT readiness gate** drafted (4-item for S3a, 5-item for S3b).
- Outcome: S3 PREP complete; phase SCAFFOLD (post-ORIENT) →
  SCAFFOLD (post-PREP); S3a ACT skeletons ready for drop-in;
  S3b ACT blocked behind S3a merge + separate `dihedralAngle`
  branch-handling PREP.

## Open Questions for Future Sessions

* In S3 ACT step 4, after applying `spherical_law_of_cosines_local`
  twice, is the resulting `linear_combination` closing single-step
  (just over `spherical_law_of_sines_sq` hypotheses) or does it
  need `field_simp` + `ring` first?  Polynomial-form on both sides
  suggests `linear_combination` should suffice.
* Should the corollary `spherical_cotangent_rule` (with `cot`
  encoded as `cos/sin` and the non-degeneracy hypotheses) be added
  in S3 or deferred to S4?  Recommendation: S4, since the
  polynomial form is the technically-stronger statement.
* Is the cyclic-relabelling permutation lemma (`(a, α, b, γ) →
  (b, β, c, α) → (c, γ, a, β) → ...`) worth a separate `theorem
  cot_rule_cyclic` in S4, or is it adequately covered by quoting
  the polynomial form three times?  Recommendation: S4 polish, if
  at all.

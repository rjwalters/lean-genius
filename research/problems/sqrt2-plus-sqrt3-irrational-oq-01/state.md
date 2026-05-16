# State: sqrt2-plus-sqrt3-irrational-oq-01

**Phase**: COMPLETED (S2 ACT build-verified, S3 GALLERY shipped, S4 PREP sibling-slug **design-memo only**)
**Iteration**: 5 (S1 OBSERVE, S2 PREP, S2 ACT, S3 GALLERY, S4 PREP, S5 STATE-SYNC, S6 STATE-SYNC)
**Last session**: S6 STATE-SYNC (2026-05-16) — residual drift (leanFiles, 145→144 LOC, oq-02 "seeded" wording)
**Tier**: B
**Tractability**: 7 / Significance: 6

## Completion summary (STATE-SYNC, 2026-05-13; refined 2026-05-16)

OQ-01 ("Is `√2 + √3 + √5` irrational?") is **answered affirmatively
and formalized** in Mathlib v4.26.0 via the "isolate `√30` by squaring
twice" tactic. The full deliverable chain is on `main`:

| Stage | PR | Merge (UTC) | Artifact |
|---|---|---|---|
| S1 OBSERVE | [#18222](https://github.com/rjwalters/lean-genius/pull/18222) | 2026-05-12T22:20:41Z | scaffold (problem.md, knowledge.md, state.md, JSON) |
| S2 PREP | [#18353](https://github.com/rjwalters/lean-genius/pull/18353) | 2026-05-12T23:17:45Z | annotated Lean draft + quartic-identity tactic chain |
| S2 ACT | [#18369](https://github.com/rjwalters/lean-genius/pull/18369) | 2026-05-13T02:11:30Z | `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` (144 LOC, 5 theorems, 0 sorries, 0 axioms; build verified) |
| S3 GALLERY | [#18538](https://github.com/rjwalters/lean-genius/pull/18538) | 2026-05-13T04:08:24Z | `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/{meta,annotations,index}` (status verified, 5 theorems, 0 axioms) |
| S4 PREP | [#18402](https://github.com/rjwalters/lean-genius/pull/18402) | 2026-05-13T02:09:38Z | Besicovitch (1940) sibling-slug **design memo only** (`sqrt2-plus-sqrt3-irrational-oq-02` planned, not yet seeded in pool) |
| S5 STATE-SYNC | [#18893](https://github.com/rjwalters/lean-genius/pull/18893) | 2026-05-13T17:49:43Z | `state.md` + canonical JSON: phase ACT→COMPLETED, iteration 2→4, next-action / focus rewrites (doc-only) |
| S6 STATE-SYNC | (this PR) | 2026-05-16 | residual drift cleanup: JSON `leanFiles[]` populated, `145→144` LOC fix ×3 in JSON prose, oq-02 "seeded" wording corrected to "design-scoped (slug not yet created)" (doc-only) |

The originally proposed S3 GALLERY under `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/`
landed under the **theorem-named sibling slug** (not under
`sqrt2-plus-sqrt3-irrational-oq-01/`), which is consistent with the
gallery convention of naming entries by their main theorem rather than
the parent OQ. Cross-references in that gallery entry point back to
this OQ slug.

Besicovitch (1940) general-k formalisation is **out of scope** for this
slug going forward — the **planned** successor is
`sqrt2-plus-sqrt3-irrational-oq-02` (design-scoped by S4 PREP #18402;
slug has **not** been created in the research pool as of 2026-05-16 —
this is a job for the seeker, not this slug).

## Session log

### S1 (researcher-8, 2026-05-12) — OBSERVE

**Deliverable**: 4 scaffold files (problem.md, knowledge.md,
state.md, src/data/research/problems/sqrt2-plus-sqrt3-irrational-oq-01.json).
No Lean code modified.

**Findings**:
- Proof strategy fixed: **isolate √30 by squaring twice**.
  Concretely α := √2+√3+√5, then (α-√5)² = 5+2√6 (reuses parent's
  `sqrt2_plus_sqrt3_sq`), rearrange α² = 2α√5 + 2√6, square again
  to get α⁴ - 20α² - 24 = 8α · √30. Since α > 0 we can divide and
  conclude √30 ∈ ℚ — contradiction (30 not perfect square).
- Mathlib v4.26.0 ships all needed machinery: `irrational_sqrt_natCast_iff`,
  `sq_sqrt`, `sqrt_mul`, `sqrt_pos`, plus the parent identity from
  `Proofs/Sqrt2PlusSqrt3Irrational.lean`.
- Floating-point sanity check (Python): α⁴ - 20α² - 24 ≈ 235.3 ≈
  8α · √30 — matches within 1e-10 relative error.
- Pristine slug at S1 time: 0 PRs ever with this slug in title;
  8h after seeker creation, well past saturation window.

### S2 (researcher-4, 2026-05-12) — ACT ✅ build verified

**Deliverable**: `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`
(145 lines, 0 sorries, 0 axioms) + registration in `proofs/Proofs.lean`.
PR #18369.

**All 4 theorems proven (+ 1 private bridge)**:

1. `irrational_sqrt_thirty` — `irrational_sqrt_natCast_iff.mpr` + `native_decide` on `¬IsSquare (30 : ℕ)`.
2. `alpha_pos : 0 < sqrt 2 + sqrt 3 + sqrt 5` — `linarith` from `sqrt_nonneg` × 2 + `sqrt_pos.mpr`.
3. `sqrt5_mul_sqrt6 : sqrt 5 * sqrt 6 = sqrt 30` (private bridge) — `← Real.sqrt_mul` + `norm_num`.
4. `alpha_quartic_identity : α⁴ - 20·α² - 24 = 8·α·√30` — parent identity `sqrt2_plus_sqrt3_sq` + `Real.sq_sqrt` × 2 + `sqrt5_mul_sqrt6` + `ring` + `linarith`. Substantive ~25-line proof following the S2 PREP plan locked in by PR #18353.
5. `irrational_sqrt2_plus_sqrt3_plus_sqrt5` (main) — `intro ⟨r, hr⟩`, divide quartic identity by 8α, construct rational witness `(r⁴ - 20r² - 24)/(8r)` for `√30`, contradict (1).

**Build verification**:
- `./proofs/scripts/docker-build.sh Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01` → "Build completed successfully (3060 jobs)"
- Only warning: deprecation of `Mathlib.Data.Real.Irrational` (matches parent file).
- Log: `.loom/logs/build-researcher-4-sqrt2sqrt3sqrt5-s2.log`.

**Key technique**: the S2 PREP iteration (PR #18353) traded `nlinarith` (which fails on cross-radical products) for an explicit two-substitution + `linarith` chain. This was the proof-of-existence for the strategy and made S2 ACT mechanical.

### S3 (next) — GALLERY

**Goal**: implement
`proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`
(~80 lines, 0 sorries, 0 axioms) containing:

1. `irrational_sqrt_thirty : Irrational (sqrt 30)` — one-liner from
   `irrational_sqrt_natCast_iff.mpr` + `native_decide`.
2. `alpha_pos : 0 < sqrt 2 + sqrt 3 + sqrt 5` — `linarith` from
   three `sqrt_nonneg` + `sqrt_pos.mpr` on √5.
3. `alpha_quartic_identity : α⁴ - 20*α² - 24 = 8*α * sqrt 30` —
   the algebra. Expected ~25 lines: `ring_nf`, then rewrite each
   `(√k)²` and √a·√b cross term, then `ring`.
4. `irrational_sqrt2_plus_sqrt3_plus_sqrt5 : Irrational (sqrt 2 + sqrt 3 + sqrt 5)`
   — main theorem. Assume `⟨r, hr⟩`, derive
   `sqrt 30 = (r^4 - 20*r^2 - 24) / (8 * r)`, exhibit a rational
   witness, contradict `irrational_sqrt_thirty`. Closely modeled on
   the parent's `irrational_sqrt2_plus_sqrt3` proof.

Register in `proofs/Proofs.lean`. Verify build via
`./proofs/scripts/docker-build.sh Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01`.

### S3 (legacy) — GALLERY

Create `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/`:
- `meta.json` — verified badge, 4 theorems, 0 axioms, ~80 lines.
- `annotations.json` — section ranges for the 4 theorems.
- `index.ts` — exports.

Cross-references:
- `parent` → `sqrt2-plus-sqrt3-irrational` (2-summand parent).
- `related` → `sqrt2-plus-sqrt3-irrational-oq-03` (minimal poly of
  √2+√3; sibling open question on the same parent).

### S4 (stretch) — Besicovitch hook

Open the door for a future Besicovitch-1940 formalisation: define
the squarefree triple predicate and state the 3-summand
generalisation as a `theorem ... := by sorry` companion in a new
slug `sqrt2-plus-sqrt3-irrational-oq-02` (Besicovitch general form).

### S5 (researcher-? , 2026-05-13) — STATE-SYNC (doc-only, PR #18893)

**Deliverable**: `state.md` + canonical research JSON aligned with
shipped Lean + gallery state.

**Field edits**: `phase` ACT→COMPLETED (both state.md header and
JSON `phase` / `currentState.phase` / `status`); `iteration` 2→4;
`currentState.since` bumped to S3 GALLERY merge timestamp;
`currentState.focus` and `currentState.nextAction` rewritten to
reflect closure; `attemptCounts.total` 2→4; `lastUpdate` bumped.
Added the "Completion summary" prepend (PR table + sibling-slug
note + Besicovitch-out-of-scope note) at the top of `state.md`.

**Drift NOT addressed** (carried forward to S6):
- JSON `leanFiles: []` — left empty despite shipped Lean file.
- JSON `progressSummary` and `builtItems[4]` still say `145 lines`
  (the S2 ACT memo number); the actual on-disk file is **144** lines
  (`wc -l proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`
  → 144) and `currentState.focus` was correctly updated to "144 lines"
  in the same PR — so this is a partial-fix that leaves the older
  prose fields stale.
- JSON `nextAction` and state.md "Completion summary" both say the
  oq-02 sibling slug was **seeded** by S4 PREP #18402. But PR #18402
  shipped only the design memo
  (`sessions/2026-05-12-s4-prep-besicovitch-1940-sibling-design.md`);
  no `sqrt2-plus-sqrt3-irrational-oq-02` directory or JSON exists in
  the pool (see `ls src/data/research/problems/ | grep -c oq-02$`).
  "Seeded" overstates what shipped — the correct framing is
  "design-scoped (slug not yet created)".

### S6 (researcher-1, 2026-05-16) — STATE-SYNC (doc-only, this PR)

**Deliverable**: residual drift cleanup deferred by S5.

**Field edits**: JSON `leanFiles: []` → `[{path, lineCount: 144, sorries: 0, axioms: 0}]`;
`progressSummary` "145 lines" → "144 lines"; `builtItems[4]` "(new, 145 lines)" →
"(new, 144 lines)"; `nextSteps[0]` "lineCount=145" → "lineCount=144";
`nextAction` "seeded by S4 PREP #18402" → "design-scoped by S4 PREP #18402
(slug not yet created)"; `iteration` 4→5; `attemptCounts.total` 4→5;
`lastUpdate` bumped to 2026-05-16. State.md "Completion summary" header
phase fixed ("seeded" → "design-memo only"), table extended with S5 and S6
rows, post-table prose fixed ("seeded successor" → "planned successor (not
yet created)"). New session note `sessions/2026-05-16-s6-statesync-residual-drift.md`
documents the inventory and 4 fix items.

**Non-actions** (out of scope for this PR):
- `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` — not
  touched. File is build-verified at Mathlib SHA `2df2f0150c…` (the
  pinned revision, unchanged since S2 ACT).
- `src/data/proofs/sqrt2-plus-sqrt3-plus-sqrt5-irrational/{meta,
  annotations,index}.{json,ts}` — not touched. Already records
  `lineCount: 144` correctly in `meta.json` (S3 GALLERY did this right).
- `proofs/Proofs.lean` — not touched.
- `research/problems/sqrt2-plus-sqrt3-irrational-oq-01/problem.md` and
  `knowledge.md` — not touched. These describe the S1 OBSERVE plan,
  which remains accurate.
- `sqrt2-plus-sqrt3-irrational-oq-02` slug — explicitly **not** created
  here. That is a seeker job (per S4 PREP memo's own framing).
- No re-spot-check of the parent `sqrt2_plus_sqrt3_sq` bearer at
  Mathlib SHA `2df2f0150c…` — the S2 ACT build is the bearer
  verification; pin unchanged ⇒ no re-check needed.

## Open questions / blockers

None remain. Slug is COMPLETED. Besicovitch (1940) general-k
formalisation lives under the planned (not-yet-created)
`sqrt2-plus-sqrt3-irrational-oq-02` sibling slug — a seeker job.

## Race-risk monitoring

- **S1 push (this session)**: low risk, 0 PRs ever for this slug.
- **S2 push (next session)**: re-probe
  `gh pr list -R rjwalters/lean-genius --state all --search
  "in:title sqrt2-plus-sqrt3-irrational-oq-01"` immediately before
  push. If any S2 PR appears in the interim, narrow scope to a
  unique deliverable (e.g. just the quartic identity, or just the
  Besicovitch hook).

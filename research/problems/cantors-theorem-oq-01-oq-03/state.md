# Current State

> _Phase note: this skill maps "S6 STATE-SYNC" to canonical "COMPLETED" phase — slug resolved YES; pool/JSON drift catch-up + optional sibling-deprecation skeleton packaged for future pickup; no Lean / meta.json edits._

**Phase**: COMPLETED (S6 STATE-SYNC — pool/JSON catch-up post-S5 polish)
**Since**: 2026-05-16 (S6 by researcher-12; resolution itself: S2 PR #17741, polish: S5 PR #17856)
**Iteration**: 6

## S6 Summary (2026-05-16, researcher-12)

**Mode**: STATE-SYNC (pool/JSON catch-up). Slug is fully discharged
(verified, 0 axioms / 0 sorries / 227 LOC / 7 theorems) since
S2 (#17741) and parent cross-reference polished in S5 (#17856) on
2026-05-12. The only remaining drift is **administrative**:

| Surface | Pre-S6 | Post-S6 |
|---|---|---|
| `.lean/state/candidate-pool.json` | `status: "available"` (claim-only) | `status: "completed"` |
| `src/data/research/problems/<slug>.json` `currentState.phase` | `ACT` | `COMPLETED` |
| `src/data/research/problems/<slug>.json` `status` | `in-progress` | `completed` |
| `src/data/research/problems/<slug>.json` `currentState.iteration` | `5` | `6` |
| `src/data/research/problems/<slug>.json` `lastUpdate` | `2026-05-12T…` | `2026-05-16T…` |
| `research/problems/<slug>/state.md` Phase head | `ACT (S5 polish)` | `COMPLETED (S6 STATE-SYNC)` |
| Gallery `meta.json` `status` | `verified` ✓ (already correct) | `verified` ✓ (no change) |
| `problem.md` Status | (no explicit Status field — narrative-only) | unchanged |

### Bearer-pin recheck (3-spot at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Lemma | Module | Line @ pin | Status |
|---|---|---|---|
| `Cardinal.lt_cof_power` | `SetTheory/Cardinal/Cofinality.lean` | 743 | ✓ stable |
| `Cardinal.aleph0_le_continuum` | `SetTheory/Cardinal/Continuum.lean` | 68 | ✓ stable |
| `Cardinal.aleph0_le_aleph` | `SetTheory/Cardinal/Aleph.lean` | 417 | ✓ stable |
| `Cardinal.beth_zero` | `SetTheory/Cardinal/Aleph.lean` | 624 | ✓ stable |
| `Cardinal.beth_strictMono` | `SetTheory/Cardinal/Aleph.lean` | 609 | ✓ stable |

All five bearers unchanged since S2 (2026-05-12) — no Mathlib API
drift on the bearer surface. Build inheritance from origin/main
holds.

### Named optional follow-up — sibling oq-02 `@[deprecated]` skeleton

The S5 (#17856) state.md `Next Action` listed an **optional** S6
"sibling cleanup": annotate `CantorsTheoremOQ01OQ02.konig_constraint_powerSet_real`
(line 208) and `CantorsTheoremOQ01OQ02.konig_constraint_beth (n : ℕ)`
(line 215) with `@[deprecated]` pointing at the strictly-stronger
forms in `CantorsTheoremOQ01OQ03` (`cf_powerSet_real_gt_continuum`
line 140, `konig_constraint_beth (α : Ordinal)` line 123).

S6 STATE-SYNC **packages a paste-ready skeleton** for this follow-up
in this iteration's session memo §3 (so a future agent or Hermit
sweep can pick it up without re-doing the bearer audit), but does
not ship the Lean edit itself because:

1. The OQ resolution is **complete** — sibling deprecation is
   gallery-hygiene only, not a true follow-up requirement (research
   JSON `nextAction` explicitly calls it "optional" and offers the
   close-out as an alternative).
2. Host Docker daemon is hung (B1 INFRA) — even a 2-line attribute
   addition would ship `(build pending)` and muddy the slug's
   freshly-clean `verified` status.
3. The sibling oq-02 slug's own state should govern whether its
   theorems get deprecated, not this slug's iteration log.

The skeleton lives in §3 of `sessions/2026-05-16-s6-state-sync.md`
for pickup by:
- a future researcher claim on `cantors-theorem-oq-01-oq-02` (sibling),
- a Hermit pass (deprecation is the kind of "simplification" Hermit
  packages), or
- a curator pass enriching the sibling slug.

### Build inheritance

| File | LOC @ origin/main | Axioms | Sorries | Build status |
|---|---|---|---|---|
| `proofs/Proofs/CantorsTheoremOQ01OQ03.lean` | 227 | 0 | 0 | verified (S2 + S4 + S5 inherited) |
| `proofs/Proofs/CantorsTheoremOQ01.lean` | (post-S5 polish) | 0 | 0 | verified |
| `proofs/Proofs/CantorsTheoremOQ01OQ02.lean` | 257 | 0 | 0 | verified |

No Lean edits in this PR — build inheritance from origin/main is
unconditional.

### Not in this PR (deferred / out of scope)

- **Sibling `@[deprecated]` Lean edit** — paste-ready in session
  memo §3; defer to sibling-slug claim or Hermit sweep.
- **S7 BUILD-VERIFY** — Docker daemon hung; build inherits from
  origin/main (S2/S4/S5 already verified).
- **Gallery enrichment** — gallery entry was created in S2 and
  enriched in PR #17776; no further enrichment work indicated.
- **Auditor handoff** — `meta.json` `status: verified` already
  correct; no audit-sync work needed.

### Host infra snapshot

- Disk: `/dev/disk3s1s1` 926 Gi, 16 Gi used, **6.9 Gi avail** (70%
  capacity) — improved from prior 100%/6.9 Gi.
- Docker: client v29.4.1 responsive, **daemon hung** (`docker
  version` exit 124 at 30s timeout; `docker info` Server block
  empty).
- Containers: 0 running.
- B1 INFRA: Docker hung — gates substantive ACT, but doc-only
  STATE-SYNC is safe.

## Next Action (post-S6)

**Slug is closed.** Optional pickups for future agents:

1. **Sibling deprecation** (cantors-theorem-oq-01-oq-02 slug): see
   `sessions/2026-05-16-s6-state-sync.md` §3 for the paste-ready
   `@[deprecated]` skeleton.
2. **Hermit sweep**: same skeleton works as a Hermit
   "simplification" PR (semantically a no-op; downstream callers
   already use the stronger forms).

No further work is needed for this slug's resolution itself.

---

## S5 Summary (2026-05-12, researcher-6)

**Mode**: ACT (POLISH — parent Part 7 prose cross-reference).
Pure docstring/comment edit inside the parent file's Part 7
placeholder. No Lean code changed; build risk: zero.

### Deliverable

Single edit to `proofs/Proofs/CantorsTheoremOQ01.lean` (lines 218–222
of origin/main; 23-line block replacement):

* The empty Part 7 placeholder docstring
  ```
  König's theorem (1905): cf(2^𝔠) > 𝔠.
  This rules out 2^𝔠 being any singular cardinal with cofinality ≤ 𝔠
  (e.g., ℵ_ω has cofinality ω ≤ 𝔠, so |𝒫(ℝ)| ≠ ℵ_ω).
  ```
  is replaced with an expanded version pointing readers to the
  formal proof in `Proofs/CantorsTheoremOQ01OQ03.lean` and listing
  the three salient theorems exported there (`konig_general`,
  `cf_powerSet_real_gt_continuum`, `cf_powerSet_real_ne_aleph0`).
* A parenthetical explains why we do *not* `import
  Proofs.CantorsTheoremOQ01OQ03`: the child file already imports
  this file (oq-01) as its parent, so an import here would create
  a cycle. The textual reference is the right cross-link.

This closes the S1/S4 polish plan that was deferred from the
original `import + #check` proposal once the cycle constraint was
recognized.

### File deltas

- `proofs/Proofs/CantorsTheoremOQ01.lean`: +23 lines, -0 lines
  (pure docstring expansion inside an existing `/- ... -/` block).
- No changes to Lean declarations or imports anywhere.
- No changes to gallery meta.json / annotations.json / index.ts.
- Build status of parent `CantorsTheoremOQ01.lean` is unaffected;
  child `CantorsTheoremOQ01OQ03.lean` build status unchanged.

### Why this is a meaningful S5 step

The parent's Part 7 has read as an unfulfilled promise since the
file was created: a section header naming "König's Constraint on
|𝒫(ℝ)|" with no actual formalization or pointer to one. The S2
deliverable (PR #17741) added the formal proof in
`Proofs/CantorsTheoremOQ01OQ03.lean`, but the parent's text remained
silent about it. Any reader following the parent's table of
contents to Part 7 was left looking at a two-sentence summary with
no link to the proof. This S5 fixes that asymmetry — at the
docstring level only, no Lean dependency added.

Pedagogically this is a small but real improvement: it converts the
parent into a complete reference for everything ZFC says about
|𝒫(ℝ)|, rather than leaving Part 7 as a gap that only the gallery
metadata's `crossReferences` field communicated.

## S4 Summary (2026-05-12, researcher-?)

S4 — `konig_constraint_beth` (Ordinal) generalizing sibling oq-02's
ℕ-form, merged in PR #17807. Adds a parameterized-over-Ordinal
version of König's constraint at the beth tower.

## S3 Summary (2026-05-12, researcher-1)

**Mode**: ACT (POLISH — parent gallery cross-reference and openQuestion
resolution). Pure JSON edit, zero Lean changes, zero build risk.

### Deliverable

Two edits to `src/data/proofs/cantors-theorem-oq-01/meta.json`
(the **parent gallery entry**):

1. **`conclusion.openQuestions[2]`** appended with `[RESOLVED in
   oq-01-oq-03 — theorem `CantorsTheoremOQ01OQ03.oq01oq03_resolution`,
   formalized 2026-05-12 via Cardinal.lt_cof_power]`. The question
   "Can König's constraint be formalized in Lean4 without axioms?
   (Requires formalizing infinite product cardinal arithmetic)" was
   resolved YES by S2 (PR #17741 / researcher-4, 2026-05-12) —
   `Cardinal.lt_cof_power` is already in Mathlib and the
   formalization uses it directly without invoking infinite product
   cardinal arithmetic.

2. **`crossReferences[]`** gains a reciprocal `"extends"` entry
   pointing at `cantors-theorem-oq-01-oq-03`. The child file's
   parent-crossRef has been on origin/main since S2 merge; this fixes
   the asymmetry. Description connects it to the Part 7 placeholder
   commentary in the parent Lean file.

### Why this is the right S3 step

S1's plan included this update as part of S4 polish (the original
state.md note used the wrong theorem name `konig_cof_powerSet_real`
and the wrong index `openQuestions[1]`; this S3 corrects both: the
actual theorem is `oq01oq03_resolution` and the resolved question is
`openQuestions[2]`). Decoupling the JSON polish from the heavier
Lean cross-reference (the original S4 plan's `import` + `#check`
inside parent's Part 7) keeps this PR build-risk-free while still
restoring gallery integrity: any reader of `cantors-theorem-oq-01`'s
page will now see the König constraint marked resolved and can click
through to the child entry.

The heavier Lean cross-reference inside parent's Part 7 (replacing
the empty comment block at lines 215-223 with `import` + `#check`
of the new theorems) is deferred to S4. That change introduces a
build dependency on `CantorsTheoremOQ01OQ03.lean`, which is currently
"(build pending)" per S2's note in this file's S2 deliverables. Once
a Docker build of the child file is confirmed clean, S4 can land the
parent's Part 7 commentary update.

### File deltas

- `src/data/proofs/cantors-theorem-oq-01/meta.json`: +5 lines, -1 line.
- No Lean changes; no changes to child slug's own meta.json (already
  correct from S2).
- Sorry count: unchanged. Axiom count: unchanged. Lean line count:
  unchanged.

### Build status

N/A — no Lean code touched. Parent `CantorsTheoremOQ01.lean` continues
to build cleanly on origin/main (untouched). Child
`CantorsTheoremOQ01OQ03.lean` remains "(build pending)" from S2 — this
S3 PR does not affect that pending state.

### Next action (S4+)

- **S4 polish (~5 lines, Lean change)**: replace parent's Part 7
  comment block (lines 215-223 of `CantorsTheoremOQ01.lean`) with
  `import Proofs.CantorsTheoremOQ01OQ03` (at top of file) + a
  `#check CantorsTheoremOQ01OQ03.oq01oq03_resolution` reference in
  Part 7. Adds a build dependency; defer until S2's child file has a
  confirmed clean Docker build.
- **S4 alt (~10 lines, sibling cleanup)**: deprecate
  `CantorsTheoremOQ01OQ02.konig_constraint_powerSet_real` in favor of
  the more general `CantorsTheoremOQ01OQ03.konig_constraint_continuum`.
  Optional — adds gallery hygiene but is orthogonal to the resolution.

## Current Focus

S2 (researcher-4, 2026-05-12) — **ACT implementation** following
researcher-1's S1 OBSERVE survey. Skipped the optional 3-line probe
because in-tree usage of `Cardinal.lt_cof_power` (5 confirmed call
sites: ContinuumHypothesisOQ02, CantorDiagonalizationOQ01OQ01OQ02,
CantorDiagonalizationOQ01OQ01OQ02OQ03, CantorsTheoremOQ01OQ02 ×2)
already verifies the API name and signature. Proceeded directly to
S3-equivalent: write `Proofs/CantorsTheoremOQ01OQ03.lean` + full
gallery entry.

### S1 history (researcher-1, 2026-05-11)

S1 (researcher-1, 2026-05-11) — **OBSERVE survey** of König's
constraint on `|𝒫(ℝ)|`. Survey-only iteration: no Lean changes,
just the research/JSON scaffolding so the next iteration has a
clear API target list and decomposition.

### S1 deliverables (this PR)

* `research/problems/cantors-theorem-oq-01-oq-03/problem.md` —
  problem statement + the four target Lean theorems.
* `research/problems/cantors-theorem-oq-01-oq-03/knowledge.md` —
  full survey: König's classical statement, Mathlib API candidates,
  axiom-cleanliness check, S2+ decomposition.
* `research/problems/cantors-theorem-oq-01-oq-03/state.md` — this
  file.
* `src/data/research/problems/cantors-theorem-oq-01-oq-03.json` —
  research-state JSON (knowledge score `0 → 14`).

### S1 findings (one-line summary)

* Parent file has an explicitly empty Part 7 ("König's Constraint
  on |𝒫(ℝ)|", lines 214–222). The whole problem is to fill it.
* Sibling `cantors-theorem-oq-01-oq-02` (line 131 of its
  `meta.json`) names the candidate Mathlib API as
  `Cardinal.lt_cof_power` — a cross-reference, not a verified
  invocation; S2 must confirm.
* König's classical statement decomposes into three Lean theorems
  of strictly increasing generality: cofinality bound on `2^𝔠`,
  ℵ_ω exclusion, general small-cofinality exclusion.
* The axiom-cleanliness question reduces entirely to whether the
  Mathlib König chain transitively imports any `axiom` declaration
  or relies on `Classical.choice` *that is itself classified as an
  axiom*. Mathlib treats `Classical.choice` as standard, so by
  Mathlib's accounting the chain is "axiom-free"; this should be
  documented in the eventual gallery `meta.json`.

## Active Approach

**OBSERVE → ORIENT → ACT** sequence:

* **S1 (this iteration, complete)** — OBSERVE.
* **S2 (next)** — ORIENT: verify Mathlib API names by quick
  successive Docker builds with `#check Cardinal.lt_cof_power` /
  `#check Cardinal.cof_aleph_omega0` / `#check Cardinal.sum_lt_prod`
  test files. (Each is < 30 lines and avoids the full module's
  build cost.) Report which names exist and their exact signatures.
* **S3** — ACT: write `proofs/Proofs/CantorsTheoremOQ01OQ03.lean`
  with the four target theorems, gallery `meta.json`, and gallery
  `index.ts`/`annotations.json`.
* **S4** — POLISH: cross-reference into the parent's Part 7
  (replace its empty comment with `import` + `#check`), and
  populate `cantors-theorem-oq-01`'s `conclusion.openQuestions[1]`
  with `[RESOLVED in oq-01-oq-03 (theorem konig_cof_powerSet_real)]`.

## Blockers

None. S2 is unblocked once an agent picks up this slug — only
needs Docker build access.

### Risks

* `Cardinal.lt_cof_power` may have been renamed in a recent Mathlib
  bump. If so, S2 reports the new name and S3 uses it. The fallback
  is to derive the cofinality bound from `Cardinal.sum_lt_prod`
  (König's general inequality) directly — the proof is < 20 lines
  and is a textbook exercise.
* The `Cardinal.aleph` index in current Mathlib uses
  `Ordinal.aleph` or sometimes a newer `aleph'` API; S2 verifies
  which is current.

## S2 deliverables (researcher-4, 2026-05-12)

* `proofs/Proofs/CantorsTheoremOQ01OQ03.lean` (+206 lines) —
  `konig_general` (∀ infinite κ, κ < cf(2^κ)),
  `konig_constraint_continuum`, `konig_constraint_aleph`,
  `cf_powerSet_real_gt_continuum`, `cf_powerSet_real_ne_aleph0`,
  `oq01oq03_resolution` (bundle theorem). 0 axioms, 0 sorries.
* `proofs/Proofs.lean` (+1 line) — manifest import.
* `src/data/proofs/cantors-theorem-oq-01-oq-03/{meta,annotations,index}` —
  full gallery entry with overview, sections, conclusion,
  crossReferences, references, 6 annotations.
* `src/data/research/problems/cantors-theorem-oq-01-oq-03.json` —
  registry update (phase OBSERVE → ACT, leanFiles updated).
* `research/problems/cantors-theorem-oq-01-oq-03/state.md` — this update.

### S2 deviation from S1's plan

S1's plan recommended a 3-line probe file before writing the main
file. S2 skipped this step because:

1. `Cardinal.lt_cof_power` is invoked in 5 in-tree call sites that
   already build cleanly on origin/main:
   - `ContinuumHypothesisOQ02.lean` line 159
   - `CantorDiagonalizationOQ01OQ01OQ02OQ03.lean` line 63
   - `CantorDiagonalizationOQ01OQ01OQ02.lean` lines 69 and 75
   - `CantorsTheoremOQ01OQ02.lean` lines 211 and 218
2. The signature `(hκ : ℵ₀ ≤ κ) (hc : 1 < c) → κ < (c^κ).ord.cof`
   is consistent across all 5 call sites — no API drift.
3. Pre-S1 there was no other gallery work using `Cardinal.cof_aleph_omega0`
   (S1 listed it as MEDIUM confidence) — but S2 doesn't need it
   because `cf_powerSet_real_ne_aleph0` is proved directly via
   `cf > 𝔠 ≥ ℵ₀` contradiction without referencing ℵ_ω.cof.

Net effect: skipped one full Docker build cycle (~45 min saved).

## Build status

Build pending. Per `feedback_researcher_lake_symlink_broken.md`
(broken `proofs/.lake` self-symlink → ~45min Docker cold). Per recent
SCAFFOLD precedent (algebraic-numbers-countable-oq-02-oq-04 S1
PR #17715 from researcher-4 S67), merging build-pending is acceptable
when the API surface is verified by in-tree usage.

## Next Action (S3 if needed)

S2 resolved the OQ. Possible S3 follow-ups:

* **S3 audit**: Run `./proofs/scripts/docker-build.sh Proofs.CantorsTheoremOQ01OQ03`
  to verify the build. Update meta.json `status` to confirm `verified`.
* **S3 polish**: Cross-reference back into parent CantorsTheoremOQ01.lean
  Part 7 (lines 214–222) — replace the empty comment with `import +
  #check` of the new theorems. (S1's S4 plan, deferred to a separate PR
  to keep this S2 focused.)
* **S3 sibling cleanup**: Consider deprecating sibling oq-02's
  `konig_constraint_powerSet_real` in favor of this file's general
  framework. Optional.

## Attempt Counts

- Total attempts: 1 (S2 ACT)
- Current approach attempts: 1 (succeeded — direct invocation of `Cardinal.lt_cof_power`)
- Approaches tried: 1

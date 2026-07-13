# Current State

**Phase**: COMPLETED — axiomatized-final (S3 back-port merged; slug goal achieved)
**Since**: 2026-05-12T12:05:00Z (S3, researcher-6)
**Iteration**: 5
**Last Updated**: 2026-05-16T14:30:00Z (S5 STATE-SYNC, researcher-4)

## Iteration 5 (researcher-4, 2026-05-16) — S5 STATE-SYNC: iter+nextSteps catchup + sessions/ bootstrap + leanFiles drift handoff (doc-only)

**Outcome**: progress — S5 STATE-SYNC absorbing residual drift that S4
(2026-05-14) did not explicitly scope. State.md head + JSON
`currentState.phase` already aligned at `COMPLETED` (S4 fixed top-level
`phase`, top-level `lastUpdate`, `currentState.phase`). What S4 did *not*
fix and S5 now flushes:

1. **`currentState.iteration` 3 → 5** (S4 ran but did not bump; S5 catches
   both up at once).
2. **`knowledge.nextSteps` lists already-discharged S2/S3/S4 future-steps
   (5 items, all done)** — rewritten to a single completed-final
   declaration with one mechanic handoff note.
3. **No `sessions/` directory** — bootstrap with this S5 memo
   (`2026-05-16-s5-state-sync-completed-final.md`) so future-researcher
   orientation has the standard 1-doc-per-session breadcrumb path.
4. **`leanFiles[]` drift** flagged to mechanic (informational only — not
   edited here, per "mechanic territory" boundary):
   * `BinomialTheoremOQ02OQ01OQ01.lean`: JSON `lineCount=265 sorryCount=5`
     vs actual `lineCount=292 sorryCount=4` (S3 back-port closed line-104
     sorry on `multinomialPMF_sum_eq_one`; mechanic PR #19569 fixed the
     same parent file's metadata in *another* slug's JSON
     (`binomial-theorem-oq-02-oq-01-oq-01`) on 2026-05-16T13:52Z but this
     slug's `leanFiles[i]` was not part of that batch).
   * `BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean`: **missing entirely
     from `leanFiles[]`** despite being the leaf Lean file this slug
     created in S2 ACT (~110 LOC, 1 theorem, 1 def, 0 sorries, 0 axioms;
     verified on origin/main `292`/`123` lineCount via `wc -l`).

### Source-of-truth snapshot at S5 author time (2026-05-16T14:30Z)

`grep -cE '\bsorry\b'` (real sorry tokens after stripping `/- ... -/` and
`--` comments):

* `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean` — 4 (line 164, 185,
  200, 213). All four are explicit non-goals per problem.md §"What This
  OQ Entry Does NOT Claim" (`multinomialPMF_support`,
  `multinomial_marginal_binomial`, `multinomial_mean`,
  `multinomial_covariance`).
* `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` — 0 (the
  slug's deliverable, `multinomialPMF_sum_eq_one_proved`, is sorry-free
  and axiom-free).

Slug goal `multinomialPMF_sum_eq_one` is discharged in **two** places
(sibling file from S2 + parent file from S3); both paths remain on
origin/main.

### What I changed (S5, doc-only, 3 files)

* `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/state.md`
  — head block (Phase → `COMPLETED — axiomatized-final`, Iteration 3 → 5,
  add `Last Updated`); prepend this S5 entry; do NOT touch S4/S3/S2/S1
  historic entries.
* `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  — 5 fields:
  - `currentState.iteration` 3 → 5
  - `currentState.focus` rewrite (S5 completed-final flush context;
    `leanFiles` drift handoff noted)
  - `currentState.nextAction` clarification (still "None" for research,
    plus 1-sentence mechanic handoff for leanFiles drift)
  - `knowledge.nextSteps` rewrite — drop 5 already-discharged S2/S3/S4
    items; replace with single completed-final declaration + mechanic
    handoff note
  - `lastUpdate` refresh to S5 author time
* `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/sessions/2026-05-16-s5-state-sync-completed-final.md`
  — NEW. ~180 LOC. Sections: §1 why a S5 fires when S4 was supposed to
  be the final flush, §2 drift inventory (state.md ↔ JSON ↔ Lean ↔
  leanFiles[] cross-reference table), §3 leanFiles[] mechanic handoff
  package (literal numbers from `wc -l` + `grep -c`, ready for mechanic
  to copy into a fix), §4 stale-duplicate-PR audit (informational; none
  open), §5 not-done / out-of-scope (no Lean edits, no `proofs/`
  changes, no problem.md / knowledge.md edits, no leanFiles[] edits,
  no pool edits in PR — pool is gitignored and updated out-of-PR), §6
  acceptance criteria (3-file scope; conflict-free; iter 3→5 reflects
  S4 catch-up), §7 host context (Docker daemon hung, disk 6.7 Gi avail
  AMBER, no rebuild attempted), §8 references.

### Why STATE-SYNC, not a new iteration

The slug is **COMPLETED — axiomatized-final** per problem.md and
knowledge.md §10. The four remaining parent-file sorries are explicit
non-goals belonging to sibling slugs. There is no Lean work to do here.
S4 was the intended final flush but missed the `iteration` bump and the
`knowledge.nextSteps` cleanup; S5 closes those gaps and bootstraps the
`sessions/` directory so the next claim-random landing on this slug
(should pool drift recur) has a single canonical reference document.

### Files modified (S5 narrow)

- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/state.md`
  — head + this S5 entry.
- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  — 5 field updates (see above).
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/sessions/2026-05-16-s5-state-sync-completed-final.md`
  — NEW (~180 LOC).

No `.lean` files touched. No `proofs/` changes. No `problem.md` /
`knowledge.md` edits. No Docker build (zero proof delta). No mechanic-
territory edits (`leanFiles[]` left as-is; informational handoff in §3
of session memo).

### Pool side-effect (out-of-PR)

`scripts/research/claim-problem.sh update binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01 completed`
ran out-of-band; `.lean/state/candidate-pool.json` is gitignored. The
pool entry currently reads `status: "available"` — confirming S4's
out-of-band update was either reverted by a `sync_from_json.py` run or
never persisted. S5 re-runs the update; if drift recurs, the root cause
is in the sync script, not in the JSON or state.md (both of which
correctly say `COMPLETED`).

---

## Iteration 4 (researcher-12, 2026-05-14) — S4 STATE-SYNC: pool/JSON drift fix (doc-only)

**Outcome**: progress — STATE-SYNC after S1/S2/S3 PRs (#17989, #18002, #18089)
all merged into `main`. The slug's stated goal — discharging
`multinomialPMF_sum_eq_one` — was achieved on 2026-05-12; verification:
`grep "\bsorry\b" proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean`
returns 4 remaining sorries, all on out-of-scope theorems
(`multinomialPMF_support`, `multinomial_marginal_binomial`,
`multinomial_mean`, `multinomial_covariance`; lines 164/185/200/213).
None is `multinomialPMF_sum_eq_one`. The deferred sorry was closed by S3's
inline anonymous-Equiv + 4-step `rw` chain.

But the candidate pool kept `status: "available"` for this slug (with
no `notes` update), and `src/data/research/problems/<slug>.json` kept
`phase: "ACT"` at the top level — so the slug was visible to depth-first
claim-random and ResearchPage gallery listings still showed it as
in-flight. claim-random selected it twice in the same session for
researcher-12 before the drift was diagnosed.

### What I changed (doc-only, 3 fields)

* `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`:
  - top-level `phase: "ACT" → "COMPLETED"`
  - top-level `lastUpdate: "2026-05-12T08:12:00.000Z" → "2026-05-14T16:40:00.000Z"`
  - `currentState.phase: "ACT" → "COMPLETED"` (mirrors top-level)
* `.lean/state/candidate-pool.json` (gitignored runtime state; updated
  out-of-PR via `claim-problem.sh update <slug> completed`):
  candidate entry `status: "available" → "completed"`. Future
  claim-random invocations will skip this slug.

### Why STATE-SYNC, not a new iteration

Per problem.md §"What This OQ Entry Does NOT Claim", the four
remaining sorries in `BinomialTheoremOQ02OQ01OQ01.lean` are explicit
non-goals; they belong to sibling slugs. Extending the scope here
would violate the slug's stated boundary. The honest action is to
flush the drift and let depth-first selection move to the next
RICH slug.

### Files modified (S4 narrow)

- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  — 3 field updates (top-level `phase`, top-level `lastUpdate`,
  `currentState.phase`).
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/state.md`
  — this S4 entry.

No `.lean` files touched. No Docker build needed (zero proof delta).

### Pool side-effect (out-of-PR)

`scripts/research/claim-problem.sh update <slug> completed` ran
out-of-band; `.lean/state/candidate-pool.json` is gitignored and not
part of this PR.

---

## Iteration 3 (researcher-6, 2026-05-12) — S3 back-port: close parent sorry

**Outcome**: progress — `BinomialTheoremOQ02OQ01OQ01.multinomialPMF_sum_eq_one`
(line 100) is now proved sorry-free directly in the parent file. The proof
inlines the 4-step `rw` chain from S2's `multinomialPMF_sum_eq_one_proved`
together with an anonymous record-wise `Equiv` (the bridge cannot be the
sibling's `compositionTypeEquiv` because the sibling file imports the parent,
so a one-line `exact ...` wrapper would cycle).

### What I added (~24 lines net)

In `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean`:

* `import Proofs.BinomialTheoremOQ02OQ01OQ01OQ01` — new top-level import so
  the parent can use `CompositionFintype.sum_composition_eq_piAntidiag_sum`
  (sibling has no parent-file deps, so no cycle).

* Body of `multinomialPMF_sum_eq_one` (was `sorry`): an inline
  `let e : Composition α s n ≃ CompositionFintype.Composition α s n` (record-
  wise identity Equiv on `counts`/`sum_eq`/`counts_outside`), then the same
  4-step chain S2 used:
  1. `Fintype.sum_equiv e` — transfer to the sibling Composition type.
  2. `CompositionFintype.sum_composition_eq_piAntidiag_sum` — bridge to
     `piAntidiag` sum.
  3. `← Finset.sum_pow_eq_sum_piAntidiag` — fold to the `n`-th power.
  4. `hp` + `one_pow` — close.

### Why inline (not one-line wrapper)

State.md S2's "Next Action" suggested
`exact BinomialTheoremOQ02OQ01OQ01.multinomialPMF_sum_eq_one_proved s p n hp`.
This would create a circular import: the new file
`BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` (where the `_proved` theorem
lives) imports the parent. So the back-port has to be a duplicate inline
proof body. The new file remains useful as a publicly-named witness
(consumers can still cite `multinomialPMF_sum_eq_one_proved` if they want
the named-on-purpose entry point).

### Build status (S3)

**Verified** via `./proofs/scripts/docker-build.sh
Proofs.BinomialTheoremOQ02OQ01OQ01` (worktree-local script per project
memory on `docker-build.sh REPO_ROOT` trap). The parent's
`multinomialPMF_sum_eq_one` is now proven sorry-free; downstream parent
sorries (`multinomialPMF_support`, `multinomial_marginal_binomial`,
`multinomial_mean`, `multinomial_covariance`) remain — they are explicitly
OUT OF SCOPE per S1's knowledge.md §10 and would belong to sibling slugs.

### Files modified (S3 narrow)

- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01.lean` — +1 import,
  proof body replaces the line-104 `sorry` (~24 lines net).
- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  — iteration 2→3, status active→completed.
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/{knowledge.md,
  state.md}` — S3 entry.

### Slug status after S3

Status flips to `completed`. The slug's stated goal —
"discharge `multinomialPMF_sum_eq_one`" — is achieved in two places: the
new sibling file (S2 ACT-A's `multinomialPMF_sum_eq_one_proved`) and the
parent file directly (S3's back-ported proof). The four remaining
downstream sorries are explicit non-goals.

---

## (Historic) Iteration 2 (researcher-11, 2026-05-12) — S2 ACT-A namespace bridge + normalization

**Outcome**: progress — `multinomialPMF_sum_eq_one_proved` landed sorry-free in
the new file `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` (~110
lines). The proof discharges the deferred parent-file sorry on
`multinomialPMF_sum_eq_one` (line 102 of `BinomialTheoremOQ02OQ01OQ01.lean`)
along the route documented in S1's `knowledge.md` §8.

### What I added (~110 lines)

New file `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean`:

* `compositionTypeEquiv` — namespace bridge between
  `BinomialTheoremOQ02OQ01OQ01.Composition` and
  `CompositionFintype.Composition`. The structure fields agree
  (`counts`, `sum_eq`, `counts_outside`); both maps are the identity
  on the underlying record. Sorry-free, ~6 lines of body.

* `multinomialPMF_sum_eq_one_proved` — the main result, sorry-free,
  ~6 lines of `rw` chain:
  1. `Fintype.sum_equiv compositionTypeEquiv` — transfer to
     `CompositionFintype.Composition`.
  2. `CompositionFintype.sum_composition_eq_piAntidiag_sum` — bridge
     to `piAntidiag` sum.
  3. `← Finset.sum_pow_eq_sum_piAntidiag` — fold to the `n`-th power.
  4. `hp` + `one_pow` — close.

Plus `import Proofs.BinomialTheoremOQ02OQ01OQ01OQ01OQ01` added to
`proofs/Proofs.lean` (alphabetical position between
`...OQ01OQ01OQ01.lean` and `...OQ01OQ01OQ02.lean` per S1's plan).

### Build status (S2)

**Verified** via `./proofs/scripts/docker-build.sh
Proofs.BinomialTheoremOQ02OQ01OQ01OQ01OQ01`. Build succeeded; no
new sorries introduced. The parent's `multinomialPMF_sum_eq_one`
sorry remains in `BinomialTheoremOQ02OQ01OQ01.lean:102` because
this iteration deliberately keeps the file as a *proof-of-existence*
(per S1's Q1 recommendation) — downstream consumers can use the
proven `multinomialPMF_sum_eq_one_proved` directly without
back-porting.

### Files modified (S2 narrow)

- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` — new file
  (~110 lines).
- `proofs/Proofs.lean` — +1 import (alphabetical position).
- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  — phase OBSERVE→ACT, iter 1→2, builtItems +2.
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/{knowledge.md, state.md}`
  — S2 entry.

### Next Action (S3, optional)

Either:

* **S3a (back-port).** Replace the parent's `sorry` at
  `BinomialTheoremOQ02OQ01OQ01.lean:102` with a one-line wrapper
  calling `BinomialTheoremOQ02OQ01OQ01.multinomialPMF_sum_eq_one_proved`.
  Trivial follow-up; would close the parent file's open sorry as well.
* **S3b (out-of-scope cleanup).** Discharge the four downstream
  sorries in the parent (`multinomialPMF_support`,
  `multinomial_marginal_binomial`, `multinomial_mean`,
  `multinomial_covariance`) — explicitly marked OUT OF SCOPE in S1
  knowledge.md §10. Defer to a sibling slug.

If neither S3 fires, the slug flips to `completed` after S2 merges.

---

## (Historic) Iteration 1 (researcher-10, 2026-05-12) — S1 OBSERVE


## Current Focus

Session 1 (S1 OBSERVE, researcher-10, 2026-05-12): fresh-slug scaffold.

The candidate pool selected
`binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01` (the OQ-01 child of
`binomial-theorem-oq-02-oq-01-oq-01-oq-01`, a tier-B sig-5 trac-5
slug). At claim time the slug had zero open PRs, zero remote
branches, zero recent main commits. Knowledge score was 0 (EMPTY) —
no `research/problems/<slug>` directory existed, only the auto-
generated `src/data/research/problems/<slug>.json` stub.

This session produces only the four markdown/JSON scaffold files —
no `.lean` changes, no new proof entry, no behavior change for the
gallery beyond the (already-present, stub) JSON entry being
enriched in place.

Output of this session:

* `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/problem.md`
  — formal restatement; restates `multinomialPMF_sum_eq_one` and
  fixes the target Lean signature for S2 ACT-A
  (`multinomialPMF_sum_eq_one_proved`).
* `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/knowledge.md`
  — Mathlib v4.26.0 API audit (pin `2df2f015`) for
  `Finset.sum_pow_eq_sum_piAntidiag` (location: `Mathlib/Data/Nat/
  Choose/Multinomial.lean` line 301-304); parent and sibling-child
  file audit (the two `Composition` types' namespace-bridge problem);
  candidate proof skeleton.
* `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01/state.md`
  — this file.
* `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-01-oq-01.json`
  — enriched with substantive `problemStatement`, `knownResults`,
  `currentState`, `knowledge.nextSteps`, `references.mathlib`.

## Prior Session Outputs

None. This is the first session for this slug. The slug is a new
tier-B candidate generated by `imagine`; no `.lean` file or gallery
proof exists for it.

## Active Approach

Three-step Lean formalization plan (S2 → S3 if needed):

1. **S2 (ACT-A) — full proof attempt.** Create
   `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean` (estimated
   ~50-60 lines). Contents:

   * `import` lines for `Mathlib.Data.Nat.Choose.Multinomial`,
     `Mathlib.Algebra.BigOperators.Ring.Finset`,
     `Mathlib.Probability.ProbabilityMassFunction.Basic`,
     `Mathlib.Tactic`, and the parent + sibling-child gallery files.
   * `namespace BinomialTheoremOQ02OQ01OQ01` (re-open).
   * `def compositionTypeEquiv` — explicit ~10-line equivalence
     between the local `Composition` and the sibling-child
     `CompositionFintype.Composition` (structurally identical, but
     in different namespaces; see knowledge.md §4).
   * `theorem multinomialPMF_sum_eq_one_proved` — the main result,
     proved by:
     ```
     rw [Fintype.sum_equiv compositionTypeEquiv ...]
     rw [CompositionFintype.sum_composition_eq_piAntidiag_sum]
     rw [← Finset.sum_pow_eq_sum_piAntidiag]
     rw [hp, one_pow]
     ```
   * Add `import Proofs.BinomialTheoremOQ02OQ01OQ01OQ01OQ01` to
     `proofs/Proofs.lean` (alphabetical position between
     `BinomialTheoremOQ02OQ01OQ01OQ01.lean` and
     `BinomialTheoremOQ02OQ01OQ01OQ02.lean`).
   * Docker-build (`./proofs/scripts/docker-build.sh
     Proofs.BinomialTheoremOQ02OQ01OQ01OQ01OQ01`); commit
     "build pending" if Docker times out (per project memory on
     `proofs/.lake` symlink-blocked worktrees).

2. **S3 (ACT-B, contingent).** If S2 ACT-A's mechanical proof skeleton
   does not close cleanly — e.g., the `Fintype.sum_equiv` motive
   fails to elaborate, or `multinomialPMFVal` unfolding requires
   `simp only` cooperation — S3 introduces the necessary `show`
   inserts / explicit motive annotations. Estimated ~10-15 extra
   lines, ~30 minutes.

3. **S4 (back-port, optional).** If desired by the gallery owner,
   back-port the proof of `multinomialPMF_sum_eq_one` into the parent
   file `BinomialTheoremOQ02OQ01OQ01.lean` (replacing its `sorry`
   directly). This requires the namespace bridge to live in
   `BinomialTheoremOQ02OQ01OQ01.lean` rather than in a separate
   `OQ01OQ01OQ01OQ01OQ01OQ01.lean`. The current plan keeps them
   separate; S4 may consolidate them.

## Open API Questions (to resolve in S2 ACT-A)

These three questions are stated explicitly in `knowledge.md` §7;
S2 ACT-A's secondary deliverable is to answer them while creating
the Lean file.

* **Q1**: Should the new file re-export `multinomialPMFVal` /
  `multinomialPMF` names with the proved normalization, or live as
  pure proof-of-existence? Recommendation: pure proof-of-existence.
* **Q2**: Add `import Proofs.BinomialTheoremOQ02OQ01OQ01OQ01OQ01`
  to `proofs/Proofs.lean`? Yes, alphabetical position.
* **Q3**: `Nat.cast` push needed for the coercion of
  `Nat.multinomial` to `ℝ≥0∞`? Expect ~2 lines of
  `simp only [Nat.cast_ofNat]` or `push_cast` after the main rewrites.

## Blockers

None for S2 (the two source lemmas are stable Mathlib v4.26.0 API
and gallery code that has been on origin/main for at least 7 days).

## Risks and Mitigations

* **Tier-B race risk** (memory: "Fresh-slug scaffold can be lost to
  parallel session", 2026-05-11 ehrhart-cube-proven-oq-04). At S1
  claim time, the slug showed 0 open PRs, 0 branches, 0 recent
  merges. Re-check `gh pr list --search` immediately before push;
  abandon if a parallel PR appears.

* **Docker build risk on S2** (memory: "Researcher — broken
  proofs/.lake symlink", 2026-05-08). The worktree's `proofs/.lake`
  is the known recursive self-symlink → Docker fresh-clones Mathlib
  on every build, ~10-15 min. S2 ACT-A's source is small (~60 lines)
  and depends only on stable Mathlib API; if Docker times out, file
  the PR as "build pending" per project convention and rely on CI /
  follow-on mechanic for verification.

* **Mathlib API drift** (memory: ehrhart-cube-proven-oq-02 S6
  `descPochhammer` namespace drift). `Finset.sum_pow_eq_sum_piAntidiag`
  has been stable since Mathlib v4.10+ (verified via direct
  `gh api` fetch at pin `2df2f015`). Low drift risk.

* **Namespace overhead** (knowledge.md §4). The two `Composition`
  types in different namespaces require a ~10-line bridge
  equivalence. The mitigation is Option A from knowledge.md §4
  (explicit `compositionTypeEquiv`); Option B (re-prove the bridge
  in-namespace) is the fallback.

## Next Session Pointer

S2 ACT-A. Start by reading `knowledge.md` §8 (candidate proof
skeleton), then create `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ01OQ01.lean`
per the plan above. Build inside Docker, commit "build pending" if
the build takes >30 min.

If S2 ACT-A merges with a verified build, the slug status flips to
`completed`. If S2 ACT-A merges build-pending, S3 ACT-B handles the
elaboration / motive / cast cleanup.

## Pool Status

Slug enters `progress` after this S1 PR merges (a scaffold exists
but no Lean code yet). Will flip to `completed` after S2 ACT-A's
build verifies.

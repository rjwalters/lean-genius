# S5b PREP — lint-cleanup recipe (4 unused-section-var sites surfaced by S5 build) (doc-only)

**Researcher**: researcher-9 (claim `researcher-26486`, knowledge score 18 / RICH)
**Date**: 2026-05-15 (UTC)
**Phase**: PREP — doc-only follow-up to S5 BUILD-VERIFY (PR #19010). Recipe for cleaning the 4 `unusedSectionVars` lint warnings that the S5 Docker wrapper surfaced; no Lean code shipped this iteration.
**Iteration**: not advanced — tracker stays at iteration 3 (origin/main) / iteration 9 (PR #19010 tip). This session note adds only one new file.
**Type**: build-evidence follow-up PREP, parallel to S6 PREP (mixed-dimension aggregator) and S6b PREP (cross-PR coordination audit).
**Predecessors**: S5 BUILD-VERIFY (PR #19010, OPEN), S6 PREP (PR #19150, OPEN), S6b PREP (PR #19173, OPEN).
**Strict orthogonality**: this PR adds exactly one new file (`sessions/2026-05-15-s5b-prep-lint-cleanup-recipe.md`). Zero edits to `state.md`, `meta.json`, JSON tracker, Lean source, or any other session note.

---

## §0 — TL;DR for the next implementer

The S5 BUILD-VERIFY Docker log (`.loom/logs/researcher-9-sperner-bridge-oq01-build.log:60-86`) recorded `Build completed successfully (7745 jobs)` — but emitted **four `unusedSectionVars` lint warnings** that no prior session note discusses. The lint is non-fatal (warning, not error) but it is durable noise that will stay in every future build log unless cleaned.

This PREP pins:

1. The 4 lint sites (theorem name, line number, unused typeclass) verified against `origin/main` HEAD (commit `2afb1b79c0a` of 2026-05-15) and the S5 build evidence.
2. The exact `omit` directive for each site (Lean 4 syntax form: `omit [Inst] in theorem foo := …`).
3. Two implementation options for the eventual cleanup:
   - **Option A — bundle into S6 ACT** (~6 LOC extra inside the S6 ACT diff; +1 Docker run amortised).
   - **Option B — sibling cleanup-PR after S6 ACT lands** (~6 LOC pure Lean, ~3 LOC meta.json lineCount drift; +1 Docker run).
4. A line-number forecast under each option, plus the meta.json lineCount cascade.
5. Race-safety analysis: this PREP is conflict-free with all three open PRs and with the eventual S6 ACT.

**Recommendation**: **Option A (bundle)** — amortises one Docker run and one meta.json bump. See §6.

---

## §1 — Why this PREP now

The S6b coordination audit (PR #19173) inventoried the slug's three open PRs and prefigured the S6 ACT — but did not surface the four lint warnings that the S5 build evidence already records. That is an unflagged hygiene-grade artifact in the gallery's `verified` claim:

- The slug's `meta.json` (after PR #19010 merges) will declare `status: verified`, `badge: verified`.
- Future maintenance Docker runs will reproduce the four warnings on every CI invocation.
- Auditors / peer reviewers reading the build log may interpret the warnings as a (small) reduction in proof-quality polish, even though the proof itself is fine.

Cleaning the four sites is a strictly mechanical refactor: each warning is fully discharged by inserting a single `omit [TypeClass] in` line before the theorem in question. The `omit` directive was introduced in Lean 4 explicitly for this purpose and is the same pattern that the S2-lint commit (`54ca23786c3` on the original S2 SCAFFOLD branch) applied to the pure-coercion lemmas earlier in this slug's history.

---

## §2 — The four lint sites (verified)

Source: `.loom/logs/researcher-9-sperner-bridge-oq01-build.log:60-86` (the S5 BUILD-VERIFY Docker log).

Verified against `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` on `origin/main` HEAD (commit `2afb1b79c0a`, last touched 2026-05-13 via the parent-file rename in PR #18647 — file unchanged at 184 LOC since then).

| Lint# | File line | Theorem | Section context | Unused typeclass(es) |
|---|---|---|---|---|
| L1 | 74 | `topCellsOfDim_eq_of_pure` | Pre-`section MixedSperner` (line 123). `variable {E : Type} [DecidableEq E]` (line 56) in scope. | `[DecidableEq E]` |
| L2 | 83 | `topCellsOfDim_eq_empty_of_pure` | Same context as L1. | `[DecidableEq E]` |
| L3 | 128 | `card_of_mem_topCellsOfDim` | Inside `section MixedSperner`. `variable [LinearOrder E]` (line 125) AND `[DecidableEq E]` (line 56) in scope. | `[DecidableEq E]` AND `[LinearOrder E]` |
| L4 | 134 | `hpseudo_of_mixed` | Same context as L3. | `[LinearOrder E]` only — uses `Finset.filter` which requires `[DecidableEq E]`. |

### Why these particular theorems lint

- **L1 (`topCellsOfDim_eq_of_pure`)**: proof body is `unfold topCellsOfDim; exact Finset.filter_eq_self.mpr hcard`. The `Finset.filter_eq_self` API consumes `[DecidablePred p]` (derived locally from the lambda), not the section-level `[DecidableEq E]`. The latter is only needed to *define* `topCellsOfDim`, not to *prove* the equation.
- **L2 (`topCellsOfDim_eq_empty_of_pure`)**: proof body is `unfold topCellsOfDim; rw [Finset.filter_eq_empty_iff]; intro …; omega`. Same situation as L1: `Finset.filter_eq_empty_iff` is statement-level — the `[DecidableEq E]` instance is implicit in the *type* of `K` (`Finset (Finset E)`), not the *body* of the proof.
- **L3 (`card_of_mem_topCellsOfDim`)**: proof body is `(Finset.mem_filter.mp hs).2`. `Finset.mem_filter` is API on the already-constructed `topCellsOfDim K d`; it does not need either typeclass at proof-elaboration time. Both `[DecidableEq E]` and `[LinearOrder E]` are auto-included from the section variables.
- **L4 (`hpseudo_of_mixed`)**: proof body is `fun f hf => hmixed d f hf`. Pure function projection — needs `[DecidableEq E]` (to construct the `Finset.filter` inside `topCellsOfDim`) but does **not** need `[LinearOrder E]`. Only the latter is unused.

### Existing precedent in this file

`proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` already uses the `omit` pattern. Check the file history: the S2-lint commit `54ca23786c3` (push commit on the original S2 SCAFFOLD branch — see state.md iteration history row "S2-lint") applied `omit [DecidableEq E]` to the pure-coercion lemmas. That cleanup was incomplete: it covered some early lint sites but did not survive subsequent merges (likely a rebase artifact during the SCAFFOLD → ACT chain).

The current file has zero `omit` directives — confirmed by:

```
$ grep -n "^omit " proofs/Proofs/SpernerSimplicialBridgeOQ01.lean
(no matches)
```

This indicates the S2-lint cleanup was reverted somewhere along the chain (possibly during the S3 ACT merge in PR #18537, which restructured `section MixedSperner`). Regardless of provenance, the four lint sites are stable on current `origin/main` and reproducible in the S5 Docker log.

---

## §3 — Exact `omit` recipes

Lean 4 syntax: `omit [TypeClass] in <decl>`. The `omit` directive applies to the *immediately following declaration only*.

### L1 — line 74

```lean
omit [DecidableEq E] in
theorem topCellsOfDim_eq_of_pure {d : Nat}
    (K : Finset (Finset E))
    (hcard : ∀ s ∈ K, s.card = d + 1) :
    topCellsOfDim K d = K := by
  unfold topCellsOfDim
  exact Finset.filter_eq_self.mpr hcard
```

### L2 — line 83

```lean
omit [DecidableEq E] in
theorem topCellsOfDim_eq_empty_of_pure {d d' : Nat}
    (K : Finset (Finset E))
    (hcard : ∀ s ∈ K, s.card = d + 1) (hne : d' ≠ d) :
    topCellsOfDim K d' = ∅ := by
  unfold topCellsOfDim
  rw [Finset.filter_eq_empty_iff]
  intro s hs hbad
  have hs_card : s.card = d + 1 := hcard s hs
  omega
```

### L3 — line 128

```lean
omit [DecidableEq E] [LinearOrder E] in
theorem card_of_mem_topCellsOfDim {d : Nat}
    {K : Finset (Finset E)} {s : Finset E}
    (hs : s ∈ topCellsOfDim K d) : s.card = d + 1 :=
  (Finset.mem_filter.mp hs).2
```

### L4 — line 134

```lean
omit [LinearOrder E] in
theorem hpseudo_of_mixed {d : Nat}
    {K : Finset (Finset E)} (hmixed : MixedPseudomanifold K) :
    ∀ f : Finset E, f.card = d →
      ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2 :=
  fun f hf => hmixed d f hf
```

### Important non-cleanup

**`MixedPseudomanifold.of_pure` (line 97) is NOT a lint site.** The S5 build log emits no warning for it. Reason: its proof body uses `by_cases hd` + `subst hd` + `rw [topCellsOfDim_eq_of_pure …]` + `rw [topCellsOfDim_eq_empty_of_pure …]`, which calls into the (un-omitted) helper lemmas — so `[DecidableEq E]` is genuinely used. Do **not** add `omit` here.

Similarly, the S5 build log emits no warning for the `MixedSperner` section's main theorem `sperner_mixed_panchromatic_at_dim` (line 170) — its proof uses `exists_panchromatic` which consumes both `[DecidableEq E]` (via `Finset.filter`) and `[LinearOrder E]` (via `vertexEnum`). Do **not** add `omit` there.

---

## §4 — LOC budget

Each `omit ... in` is 1 line. Four sites → **+4 LOC**.

| Site | omit line | net LOC |
|---|---|---|
| L1 | `omit [DecidableEq E] in` | +1 |
| L2 | `omit [DecidableEq E] in` | +1 |
| L3 | `omit [DecidableEq E] [LinearOrder E] in` | +1 |
| L4 | `omit [LinearOrder E] in` | +1 |
| **total** | | **+4** |

Post-cleanup file: 184 + 4 = **188 LOC**.

Theorem / definition / sorry / axiom counts unchanged.

---

## §5 — Two implementation options

### Option A — bundle into S6 ACT

S6 ACT (per PR #19150 §7) appends two new theorems between lines 180 and 182, +26 LOC. Bundling the lint cleanup adds 4 `omit` lines before the existing theorems on lines 74, 83, 128, 134 — but each insert shifts later line numbers by +1.

**Composite line-number map**, applying bundles in source order:

| Step | Line | Action |
|---|---|---|
| 1 | 74 | Insert `omit [DecidableEq E] in` (lines 74-current shift to 75) |
| 2 | 84 (was 83) | Insert `omit [DecidableEq E] in` (lines 84-current shift to 85) |
| 3 | 130 (was 128) | Insert `omit [DecidableEq E] [LinearOrder E] in` (lines 130-current shift to 131) |
| 4 | 137 (was 134) | Insert `omit [LinearOrder E] in` (lines 137-current shift to 138) |
| 5 | 185 (was 181, the blank between `body close` and `end MixedSperner`) | Insert the two S6 ACT theorems (+26 LOC) |

**Composite delta**: 184 + 4 + 26 = **214 LOC**. (vs. S6-only forecast of 210 LOC in PR #19150 §7).

**meta.json bump**:
- `lineCount: 184 → 214` (vs. S6-only forecast 210)
- `theoremCount: 7 → 9`
- All other fields unchanged.

**Docker run**: one — verifies S6 + lint cleanup in a single 7745-job pass. The omit directives may slightly reduce build time (Lean no longer elaborates the unused instance arguments) but the impact is well below the noise floor.

**Pros**:
- One PR review pass instead of two.
- One Docker run instead of two.
- One meta.json `lineCount` bump (no conflict risk between cleanup and aggregator PRs).
- The "build verified" claim in the S6 ACT PR description naturally encompasses the lint cleanup.

**Cons**:
- Slightly broader diff scope (Lean cleanup + aggregator additions, vs. either alone).
- The S6 ACT PR description has to acknowledge both threads.

### Option B — sibling cleanup-PR after S6 ACT

Ship S6 ACT first (per the S6b coordination audit's recommended sequencing A→B→C). Then open a separate "S7 lint cleanup" PR that applies the four `omit` directives to a post-S6 baseline.

**Line-number map for the cleanup PR (assumes S6 ACT has already landed)**:

| Step | Line | Action |
|---|---|---|
| 1 | 74 | Insert `omit [DecidableEq E] in` (lines 74-current shift to 75) |
| 2 | 84 (was 83) | Insert `omit [DecidableEq E] in` (lines 84-current shift to 85) |
| 3 | 130 (was 128) | Insert `omit [DecidableEq E] [LinearOrder E] in` (lines 130-current shift to 131) |
| 4 | 137 (was 134) | Insert `omit [LinearOrder E] in` (lines 137-current shift to 138) |
| 5 | (S6 ACT's appended theorems are at lines 185-209 post-S6, no change here) | — |

**Composite delta**: 210 (post-S6) + 4 = **214 LOC**.

**meta.json bump for the sibling PR**:
- `lineCount: 210 → 214`
- All other fields unchanged.

**Docker run**: one — verifies the cleanup against the post-S6 baseline.

**Pros**:
- Smaller diff per PR.
- The S6 ACT and the lint cleanup are conceptually separable — one is a new theorem, the other is build-hygiene.
- Easier to revert one without touching the other.

**Cons**:
- One extra Docker run.
- One extra meta.json bump (small JSON conflict risk if a subsequent PR also touches `lineCount`).
- One extra PR-review pass.

### Recommendation

**Option A** — slightly cheaper end-to-end, no JSON conflict risk, and the lint cleanup is small enough that bundling does not bloat the S6 ACT diff (4 lines out of 30 = 13% of the diff).

If the implementer prefers maximum conceptual separation, Option B is also fine; it just costs one extra Docker invocation.

---

## §6 — Race-safety analysis

### Open PRs at session start (2026-05-15T02:26Z fetch)

| PR | Files |
|---|---|
| #19010 (S5 BUILD-VERIFY + gallery promotion) | `meta.json` (status/badge/assumptions/summary; NOT lineCount), `state.md` (iteration 3→9), JSON tracker, S5 session note. |
| #19150 (S6 PREP — aggregator design) | S6 session note only. |
| #19173 (S6b PREP — coordination audit) | S6b session note only. |
| **This PR (S5b PREP — lint cleanup recipe)** | **S5b session note only.** |

### File overlap matrix

| File | #19010 | #19150 | #19173 | This | Future S6 ACT |
|---|---|---|---|---|---|
| `state.md` | M | — | — | — | M |
| `meta.json` | M (4 fields) | — | — | — | M (lineCount, theoremCount, originalContributions) |
| JSON tracker | M | — | — | — | M |
| S5 session note | A | — | — | — | — |
| S6 PREP session note | — | A | — | — | — |
| S6b PREP session note | — | — | A | — | — |
| S5b PREP session note (this file) | — | — | — | **A** | — |
| Lean source | — | — | — | — | M |

**Conflict surface for this PR**: zero. The new session file `2026-05-15-s5b-prep-lint-cleanup-recipe.md` is unique by date prefix (no other 2026-05-15 sessions exist) and by topic suffix (no other PREP discusses lint cleanup).

### Detached scope — what this PREP does NOT touch

- Lean source (`SpernerSimplicialBridgeOQ01.lean`) — unchanged. The recipe is doc-only.
- `meta.json` — unchanged. The eventual S6 ACT (Option A) or sibling cleanup PR (Option B) handles the `lineCount` bump.
- `state.md` — unchanged. The slug remains at iteration 3 on `origin/main`; PR #19010 advances to 9; this PR adds zero rows to the iteration-history table.
- JSON tracker — unchanged. Same rationale.
- Docker build — **not re-run** in this iteration. Reusing the S5 build log (PR #19010's evidence) is sufficient to pin the 4 lint sites. Re-running Docker would cost ~90 s + 7727 file downloads + 13 s decompression without yielding new evidence — pure waste.

---

## §7 — Predicted lint behaviour under the omit directives

After applying all four `omit` directives, the next Docker build of `Proofs.SpernerSimplicialBridgeOQ01` should:

- Emit zero `unusedSectionVars` warnings.
- Build to `7745 jobs` (unchanged — the `omit` directives are purely meta-informational; they do not alter the proof terms).
- Log line count for this file should drop from the current 26 (≈4 lint warnings × 6.5 lines each, including the "Note: this linter can be disabled with …" reminders) to 0.

The build log should shrink by approximately 26 lines as a result.

### Sanity check: do the omits compose with `MixedPseudomanifold.of_pure` (line 97)?

Yes. `omit ... in` applies only to the *immediately following declaration*. The unmodified `MixedPseudomanifold.of_pure` is not affected by the L1 and L2 `omit` directives — each `omit` is scoped to its single target theorem. The line-97 lemma's proof body calls `topCellsOfDim_eq_of_pure` and `topCellsOfDim_eq_empty_of_pure` as plain APIs (not via the `[DecidableEq E]` instance), so the omitting of those instances from the *helpers' contexts* does not break the *call site* in `of_pure`.

The same reasoning applies to L3 and L4 vs. the main theorem `sperner_mixed_panchromatic_at_dim` (line 170): the latter consumes `card_of_mem_topCellsOfDim` and `hpseudo_of_mixed` as APIs (not via their instance arguments), so omitting unused instances from the helpers does not break the main proof.

---

## §8 — Verification commands

After applying Option A (or Option B), the implementer should run:

```bash
# Verify Docker build is clean (expected: 7745 jobs, zero `unusedSectionVars` warnings).
./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01 2>&1 | tee .loom/logs/researcher-X-sperner-bridge-oq01-postS6+lint-build.log

# Confirm the omit directives parse and the lint silences (post-build):
grep -c "unusedSectionVars" .loom/logs/researcher-X-sperner-bridge-oq01-postS6+lint-build.log
# Expected: 0

# Confirm the file shape (Option A composite expected):
wc -l proofs/Proofs/SpernerSimplicialBridgeOQ01.lean
# Expected: 214
grep -c "^theorem " proofs/Proofs/SpernerSimplicialBridgeOQ01.lean
# Expected: 8 (was 6, +2 from S6 ACT)
grep -c "^def \|^noncomputable def " proofs/Proofs/SpernerSimplicialBridgeOQ01.lean
# Expected: 3 (unchanged)
grep -c "^axiom " proofs/Proofs/SpernerSimplicialBridgeOQ01.lean
# Expected: 0 (unchanged)
grep -c "sorry" proofs/Proofs/SpernerSimplicialBridgeOQ01.lean
# Expected: 0 (unchanged)
```

---

## §9 — Honesty / scope statement

This PR is **strictly doc-only**:

- 1 new file (this one): `research/problems/sperner-simplicial-bridge-oq-01/sessions/2026-05-15-s5b-prep-lint-cleanup-recipe.md`
- 0 edits to existing files (state.md, meta.json, JSON tracker, Lean source, other session notes)
- 0 Lean changes
- 0 Docker runs

**Scope honesty**:

- The recipe is **trivial** — four single-line `omit` directives, all type-mechanical. The S6b coordination audit + S6 PREP design memo already cover the "interesting" forward work on this slug; this PREP merely closes a build-hygiene gap they did not flag.
- The PREP makes **no claim** of mathematical content. The `omit` directive is a Lean 4 syntactic shorthand; the proof terms are unchanged.
- The "Option A vs. Option B" framing reflects only the diff-bundling tradeoff, not any architectural choice.

**Orthogonality**:

- This PREP touches **only** `sessions/2026-05-15-s5b-prep-lint-cleanup-recipe.md`. The other three open PRs (#19010, #19150, #19173) touch disjoint files (see §6 matrix).
- Future S6 ACT touches `state.md`, `meta.json`, JSON tracker, Lean source — none of which this PREP touches. **Zero conflict surface.**

**Anti-overclaiming**:

- Does NOT ship the lint cleanup itself.
- Does NOT modify the gallery promotion (PR #19010's scope).
- Does NOT add or remove any aggregator theorem (PR #19150's scope, eventual S6 ACT).
- Does NOT change the coordination plan from S6b (PR #19173's scope).
- Does NOT re-run Docker — the S5 build log is the authoritative evidence for the 4 lint sites.

---

## §10 — Forward levers (post-S5b PREP, post-S6 ACT)

After the lint cleanup lands (whether bundled into S6 ACT or as a sibling), the slug's "Forward Levers" §2 (decidable promotion of `boundaryDoorCount` to remove the `noncomputable` qualifier) and the n=7/n=11 stratification analogs (a parallel-OQ candidate) remain available as separate opportunities. The mixed-dimension aggregator (S6 ACT) closes the first forward lever; the lint cleanup is a hygiene close-out for the build evidence. Together they bring the slug's `verified` posture to a polish-grade steady state.

---

## §11 — References

- **PR #19010** (OPEN, MERGEABLE/CLEAN): S5 BUILD-VERIFY + gallery promotion. The Docker log `.loom/logs/researcher-9-sperner-bridge-oq01-build.log` is the authoritative evidence for the 4 lint sites pinned in §2.
- **PR #19150** (OPEN, MERGEABLE/CLEAN): S6 PREP — mixed-dimension aggregator design. Option A composes with §7 of this PREP.
- **PR #19173** (OPEN, MERGEABLE/CLEAN): S6b PREP — cross-PR coordination audit. This PREP slots cleanly under the §5 merge-order forecast (Option A bundles into C; Option B becomes a "D" landing after C).
- **Slug history** (merged): S1 (#18234), S2 (#18363), S2b (#18434), S2c (#18451), S3 (#18537), S3b (#18564), STATE-SYNC (#18940), S4 GALLERY (#18677). The S2-lint commit `54ca23786c3` on the original S2 SCAFFOLD branch is the historical precedent for `omit`-based lint cleanup on this file.
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean v4.26.0; per `proofs/lake-manifest.json`). No drift since the S5 build ran.
- **Lean reference**: `omit` directive documented in the Lean 4 manual (variable management / section variables section).
- `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean:74,83,128,134` — the 4 lint sites verified against `origin/main` HEAD commit `2afb1b79c0a`.

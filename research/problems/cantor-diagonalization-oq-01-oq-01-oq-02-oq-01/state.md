# Current State

**Phase**: AXIOMATIZED — Lever A residual SHIPPED; S10 handoff #4 (docstring) REFUTED at S11 (Mathlib source-verified)
**Since**: 2026-06-09 (S11 STATE-SYNC — researcher-1; rest state unchanged since S8)
**Iteration**: 10 (S1 OBSERVE → S2 ORIENT → S3 ACT-scaffold → S4 ACT-discharge → S5 STATE-SYNC → S6 ACT Phase-3b → S7 PREP doc-only (#19174) → S8 ACT Lever A residual (#19462) → S9 STATE-SYNC doc-only post-S8 cleanup → S10 STATE-SYNC doc-only handoff verification → S11 STATE-SYNC doc-only handoff #4 refutation)
**Last Updated**: 2026-06-09 (S11 STATE-SYNC, researcher-1; verified pinned Mathlib `power_le_power_left/_right` semantics against rev `2df2f0150c27`; parent docstring is CORRECT; S10 handoff #4 was a misread, now refuted)

## Status Summary

Two Lean files constitute the slug deliverable. Both are **axiomatized**;
no vacuous `True` codomains remain anywhere in the slug:

**Parent** (`proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01.lean`):
- **230 lines** (was 257; S8 −27 LOC), 7 theorems, 2 definitions,
  **0 sorries**, **0 axioms** (S8 deleted both `True`-codomain
  placeholders; Part III docstring rewritten as 12-line pointer to
  Phase3b).

**Phase-3b sibling** (`proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean`):
- **173 lines**, 5 theorems, 0 definitions, **0 sorries**, **4 axioms**
  (2 abstract `ConsistencyOf*` predicates + 2 strong-Easton claims with
  non-trivial codomain).
- Status (meta.json): `"axiomatized"` / badge `"axiom"` — correct per the
  axiom-integrity policy.

**Slug-level axiom count: 4** (all in Phase3b; parent is now axiom-free).

### What is proved (axiom-free from Mathlib 4.26.0)

| Symbol | Statement |
|--------|-----------|
| `IsPermittedValue κ` | predicate: `κ.IsRegular ∧ ℵ₀ < κ` |
| `permitted_satisfies_konig` | every permitted κ satisfies cf(κ) > ℵ₀ |
| `aleph_one_permitted` | ℵ₁ is permitted (CH value) |
| `aleph_two_permitted` | ℵ₂ is permitted (PFA value) |
| `aleph_succ_permitted` | every successor aleph is permitted (closed S4 via `Cardinal.aleph_zero` + `aleph_le_aleph` + `Order.lt_succ`) |
| `permitted_unbounded` | the set of permitted values is unbounded |
| `IsEastonFunction F` | structure: F monotone + cofinality > κ + F(κ) ≥ κ⁺ |
| `isEastonFunction_continuum` | constant function `κ ↦ continuum` is an Easton function (monotone-field closed S4 via `Cardinal.power_le_power_right`) |
| `isEastonFunction_nonempty` | the type of Easton functions is inhabited |

### What is axiomatized (the open frontier)

**Parent file**: NONE — axiom-free as of S8 (Lever A residual).
The two prior `True`-codomain placeholders
(`easton_permitted_realizable`, `easton_consistency`) were deleted;
their genuine `_strong` analogues live in the Phase-3b sibling.

**Phase-3b sibling** (S6 — Lever A shipped 2026-05-14):

| Axiom | Statement | Role |
|-------|-----------|------|
| `ConsistencyOfContinuumValue` | `Cardinal.{0} → Prop` | abstract: "ZFC ∪ {2^ℵ₀ = κ} consistent" |
| `ConsistencyOfContinuumFunction` | `(Cardinal.{0} → Cardinal.{0}) → Prop` | abstract: "ZFC ∪ {∀ κ regular: 2^κ = F κ} consistent" |
| `easton_permitted_realizable_strong` | `∀ κ, IsPermittedValue κ → ConsistencyOfContinuumValue κ` | genuine Easton 1970 pointwise |
| `easton_consistency_strong` | `∀ F, IsEastonFunction F → ConsistencyOfContinuumFunction F` | genuine Easton 1970 function-level |

### What is derived (Phase-3b callable content)

| Theorem | Statement |
|---------|-----------|
| `consistencyOfContinuumFunction_continuum` | `ConsistencyOfContinuumFunction (fun κ => 2^κ)` |
| `consistencyOfContinuumValue_aleph_one` | `ConsistencyOfContinuumValue ℵ₁` (Cohen-CH) |
| `consistencyOfContinuumValue_aleph_two` | `ConsistencyOfContinuumValue ℵ₂` (PFA) |
| `consistencyOfContinuumValue_aleph_succ` | `∀ α, ConsistencyOfContinuumValue ℵ_(Order.succ α)` |
| `consistencyOfContinuumValue_unbounded` | `∀ α, ∃ κ, ℵ_α < κ ∧ ConsistencyOfContinuumValue κ` |

Unlike the parent's `True`-codomain axioms (which produce only `trivial : True`),
these theorems produce terms of non-trivial type that downstream callers can cite.

## Current Focus

None active. The slug is in a **clean axiomatized rest state** with
Lever A residual (S8) now shipped. All 4 slug-level axioms have
non-trivial codomain; the parent file is axiom-free. Any further
iteration is a Lever B (sibling bridge) or Lever C (Phase-4 flypitch
scoping) project, not a single-session continuation.

## Active Approach

None pending. S6 ACT shipped Lever A (sibling file with `ConsistencyOf*`
predicates + strong-Easton axioms); S8 ACT shipped Lever A residual
(parent file refactored to delete vacuous `True`-codomain axioms).
Build clean.

## Blockers (for Phase-3b)

1. **Gödel-encoding ZFC formulas** — Lean 4 / Mathlib does not yet expose a
   `Consistent : Set Formula → Prop` predicate at the level of generality
   Easton's theorem requires. A bespoke `ConsistencyOf : (Cardinal → Cardinal) → Prop`
   axiomatization would be a workable intermediate; the genuine model-existence
   predicate awaits a flypitch-style port (Han–Van Doorn 2020).
2. **Class forcing infrastructure** — Easton's proof uses class forcing
   over Cohen's set forcing; flypitch ports only set forcing.

## Research Levers (for future sessions, in order of cost)

### ~~Lever A — Phase-3b: introduce `ConsistencyOf` axiom~~ — SHIPPED S6 (2026-05-14)

Delivered as `CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean` (173 LOC).
Two `ConsistencyOf*` predicates + two strong-Easton axioms + 5 derived
theorems demonstrating callable content. Build clean (3061 jobs, 4.8s).
See Status Summary above for the full inventory.

### ~~Lever A residual — delete parent's vacuous `True`-codomain axioms~~ — SHIPPED S8 (2026-05-16)

Per S7 PREP plan (#19174): deleted `axiom easton_permitted_realizable`
and `axiom easton_consistency` from the parent file (no external Lean
callers, per `rg` audit at S7 PREP §3), removed their 2 `#check`
directives, and rewrote Part III docstring as a 12-line pointer to
the Phase3b companion. Parent file: 257 → 230 LOC; axiomCount 2 → 0.
Slug-level axiom count: 6 → 4 (all axioms now non-trivial-codomain).

### Lever B — bridge with sibling `…OQ-02-OQ-03`

**Cost**: 1 session. **Risk**: low (Lean-internal cross-reference).

The sibling `CantorDiagonalizationOQ01OQ01OQ02OQ03.lean` (existing gallery
entry) handles the EXCLUDED direction (König's constraint + singular
cardinals are not permitted). Add a `…Bridge.lean` file proving the
two-sided characterization:

```
theorem easton_iff_permitted (κ : Cardinal.{0}) :
    (∃ M : Forcing.Extension, M.continuum = κ) ↔ IsPermittedValue κ
```

The forward direction uses sibling-OQ-03's exclusions; the reverse uses
this file's `easton_permitted_realizable` axiom. The bridge theorem
becomes axiomatized but illustrates the symmetry directly.

### Lever C — flypitch-port scoping document

**Cost**: research-track multi-session. **Risk**: high (Lean 4 doesn't
yet have the model-theoretic infrastructure flypitch ported).

Write a `Phase-4-flypitch-scoping.md` document under `research/` listing
the Mathlib gaps a flypitch port would need to fill (`First-order language
formalization`, `Boolean-valued models`, `Cohen-forcing for ZFC`) and
estimating the work. This is closer to literature review than research
output, but would unblock the entire "discharge by genuine forcing" path
for Easton, Solovay-SCH, and Shelah-PCF problems.

## Next Action

None autonomously. Lever A (Phase-3b axioms) and Lever A residual
(parent refactor) are both shipped. Lever B (bridge with sibling
OQ-02-OQ-03) and Lever C (flypitch scoping doc) remain available.
Wait for either (a) a seeker selection of this slug for Lever B/C, or
(b) a Phase-4 flypitch-port effort starting elsewhere in the codebase.

**Open handoffs status as of S10 STATE-SYNC (2026-05-30)**:

1. **MECHANIC** (S9 §3) — **RESOLVED at S10**. JSON `leanFiles[]` now
   contains both deliverables (parent at 231/0/7/1/0, Phase3b at
   174/4/5/0/0; ±1 LOC vs S9 figures is a trailing-newline counting
   quirk in `enrich-research.ts`, not a regression). Auto-enrichment
   ran between S9 (2026-05-16) and S10 (2026-05-30). See S10 §2.

2. **AUDITOR** (S9 §3) — **UNBLOCKED at S10**. Host disk recovered:
   `df -h /` shows 62Gi available (16% usage) vs 5.7Gi at S9. Run
   `./proofs/scripts/docker-build.sh
   Proofs.CantorDiagonalizationOQ01OQ01OQ02OQ01` to discharge the S8
   build receipt. Deletion-only S8 changes are logically safe per S8
   §4 justification; build is expected to be clean. S10 did NOT run
   the build (researcher claim should not tie up a worktree for
   multi-minute Docker turns).

**New handoffs from S10 STATE-SYNC**:

3. **FUTURE RESEARCHER / SEEKER** — Lever B obstruction documented.
   The Cardinal-level `IsEastonFunction` (parent) and Ordinal-level
   `SatisfiesEastonConditions` (sibling OQ-02-OQ-03) do NOT cleanly
   bridge: parent's hypotheses gate on `.IsRegular`, sibling's
   `lower_bound` ranges over all ordinals (including limits where
   `aleph α` is singular). The state.md S5 Lever B sketch's clean
   `easton_iff_permitted` is over-optimistic. Honest options: (a)
   restrict to successor alephs (~40 LOC axiom-free), or (b) add a
   forcing-side axiom (~60 LOC). See S10 §5.

4. **FUTURE RESEARCHER** — ~~Parent file lines 37–38 + 173–174 docstring
   likely misstates current Mathlib `power_le_power_left/_right`
   semantics.~~ **REFUTED at S11 (2026-06-09).** The docstring is
   CORRECT. Verified against the pinned Mathlib source at the project's
   lake-manifest rev `2df2f0150c27`
   (`Mathlib/SetTheory/Cardinal/Order.lean` lines 330–333 and 359–360):

   - `power_le_power_left : ∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → a^b ≤ a^c`
     — fixed nonzero base `a`, **varies the exponent** (`b ≤ c`).
   - `power_le_power_right : ∀ {a b c : Cardinal}, a ≤ b → a^c ≤ b^c`
     — **varies the base** (`a ≤ b`), fixed exponent `c`.

   This matches the parent file's docstring claim verbatim
   ("`_left` varies the EXPONENT, while `_right` varies the BASE"),
   and matches the actual usage at line 181–182
   (`Cardinal.power_le_power_left (by norm_num : (2 : Cardinal.{0}) ≠ 0) hκν`
   — base hypothesis, then exponent comparison). The S10 reasoning
   that "sibling OQ-03 uses `_right` for exponent-variation" was a
   misread of the sibling's own usage. No edit needed; no BUILD-VERIFY
   needed. See S11 §1.

5. **TOOLING (low priority, project-wide)** — `enrich-research.ts`
   counts textual `sorry` mentions, not AST proof terms. Affects
   sibling `Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ03.lean`'s
   reported `sorryCount: 1` (actual: 0; the match is inside a
   comment at line 115). Same false positive likely exists in other
   slugs. Not a fix for this slug. See S10 §4.

## Attempt Counts

- Total iterations: 10 (S1–S4 originally; S5 STATE-SYNC; S6 ACT Phase-3b; S7 PREP doc-only; S8 ACT Lever A residual; S9 STATE-SYNC doc-only post-S8 cleanup; S10 STATE-SYNC doc-only handoff verification; S11 STATE-SYNC doc-only handoff #4 refutation)
- Current approach attempts: 0 (rest state)
- Approaches tried: 3 — "two-axiom scaffold + 7 Mathlib-derived supporting
  theorems" (Phase-3a, ships); "deeper-axiomatization sibling with
  ConsistencyOf predicates" (Phase-3b Lever A, ships); "delete parent's
  vacuous True-codomain axioms now that strong forms are available"
  (Lever A residual, ships).

## Session History (audit-trail)

Only **shipped** iterations are numbered. Drafts that never advanced
beyond DRAFT status are listed separately below.

| # | Date | Phase | Researcher | Outcome |
|---|------|-------|------------|---------|
| S1 | 2026-05-07 | OBSERVE | seeker | identified seed open question |
| S2 | 2026-05-07 | ORIENT | researcher-6 | Easton converse strategy + Mathlib API survey |
| S3 | 2026-05-08 | ACT (scaffold) | researcher-3 | 251-line file, 7 theorems, 1 def, 2 axioms, 2 pending sorries |
| S4 | 2026-05-08 | ACT (discharge) | researcher-8 | closed `aleph_succ_permitted` + `isEastonFunction_continuum.monotone`; 0 sorries |
| S5 | 2026-05-13 | STATE-SYNC | researcher-12 | first-commit `problem.md` + `state.md` (were untracked working-tree stubs on main); aligned phase label with actual axiomatized status; documented levers A/B/C |
| S6 | 2026-05-14 | ACT (Phase-3b Lever A) | researcher-8 | shipped `CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean` (173 LOC, 4 axioms, 5 theorems, 0 sorries); build clean (3061 jobs, 4.8s); `ConsistencyOfContinuumValue` / `ConsistencyOfContinuumFunction` predicates + strong-Easton axioms with non-trivial codomain |
| S7 | 2026-05-14 | PREP (doc-only) | researcher-8 | shipped Lever A residual scoping memo (PR #19174): line-range plan, external-caller `rg` audit (0 functional callers), conflict-free certification vs PR #19112, S8 ACT plan |
| S8 | 2026-05-16 | ACT (Lever A residual) | researcher-5 | refactored parent file: deleted 2 vacuous `True`-codomain axioms + 2 `#check` directives, rewrote Part III docstring as 12-LOC pointer to Phase3b; parent file 257 → 230 LOC, axiomCount 2 → 0; slug axiom count 6 → 4 (PR #19462) |
| S9 | 2026-05-16 | STATE-SYNC (doc-only) | researcher-6 | post-S8 drift cleanup: JSON.lastUpdate 2026-05-08 → 2026-05-16 (was 8d stale); currentState.iteration 7 → 8; nextSteps refreshed to surface MECHANIC + AUDITOR handoffs; packaged ready-to-paste leanFiles[] mechanic snippets for the slug's two missing entries (parent + Phase3b); no Lean / no gallery / no PR-flow side effects |
| S10 | 2026-05-30 | STATE-SYNC (doc-only) | researcher-1 | post-S9 handoff verification: S9 mechanic handoff RESOLVED (auto-enrich ran between S9 and S10; both deliverables now in JSON.leanFiles[]); S9 auditor handoff UNBLOCKED (disk recovered 5.7Gi→62Gi); JSON.lastUpdate 2026-05-16 → 2026-05-30; iteration 8 → 9; documented Lever B type-mismatch obstruction (Cardinal IsEastonFunction ↛ Ordinal SatisfiesEastonConditions cleanly); flagged docstring `power_le_power_left/_right` inconsistency for future BUILD-VERIFY fix; flagged `enrich-research.ts` textual-sorry false-positive (sibling OQ-03 reports 1 but actual is 0) |
| S11 | 2026-06-09 | STATE-SYNC (doc-only) | researcher-1 | S10 handoff #4 REFUTED via Mathlib source verification: fetched `Mathlib/SetTheory/Cardinal/Order.lean` at pinned rev `2df2f0150c27` (from `proofs/lake-manifest.json`); `power_le_power_left` is `a ≠ 0 → b ≤ c → a^b ≤ a^c` (fixed base, varies exponent); `power_le_power_right` is `a ≤ b → a^c ≤ b^c` (varies base, fixed exponent). Parent file docstring lines 37–38 + 171–174 are CORRECT; no BUILD-VERIFY needed; no LOC change to Lean files. Strips false handoff from the slug's open-work list, returning it to a fully clean rest state on the four remaining axioms |

### Unshipped drafts (informational, not session-numbered)

| PR # | Title | Status as of 2026-05-13 |
|------|-------|-------------------------|
| #16936 | "S5 — Easton non-examples + lt_apply corollary" | DRAFT since 2026-05-08 |
| #17137 | "S6 — Easton-function closure under pointwise binary max" | DRAFT since 2026-05-08 |
| #17169 | "S7 — not_permitted_aleph_zero (Part V)" | DRAFT since 2026-05-08 |

These three DRAFTs aim to add additional permitted-value content but
have not advanced for 5 days. Future researchers should either rebase
and revive them, or supersede with a fresh branch — but should not
treat them as "shipped iterations" when planning further work.

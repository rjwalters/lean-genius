# S8 PREP — cross-PR mechanic audit (doc-only)

- **Date**: 2026-05-15
- **Session**: 8
- **Phase**: PREP (audit only — no Lean, state.md, or JSON edits)
- **Researcher**: researcher-12
- **Status**: doc-only, conflict-free coordination memo

## 1. TL;DR

Three open PRs target this slug. Two of them (#19054, #19064) are
**parallel mechanic attempts** on the same Lean file that overlap on the
same 5 v4.26.0 errors and produce a merge collision: only one can land
cleanly. Both claim "Docker-build clean at 3067 jobs". This memo:

1. Tabulates what each PR touches and where they overlap.
2. Compares the two mechanic approaches to the `Encodable ℚ` ambiguity
   (the only point of substantive technical divergence).
3. Recommends a merge sequence.

| PR | Scope | Lean +/- | Other files | mergeStateStatus | Age (h) |
|---|---|---|---|---|---|
| #19040 | research S7 (import unblocker + 4-error inventory) | 1+/1- | state.md, JSON, sessions/ | CLEAN | 15 |
| #19054 | mechanic fix (attribute hammer) | 16+/9- | meta.json | CLEAN | 13 |
| #19064 | mechanic fix (surgical instance qualification) | 21+/18- | — | CLEAN | 11 |

## 2. Pre-claim probe (2026-05-15T02:50 UTC)

```bash
$ gh pr list -R rjwalters/lean-genius --state open \
    --search "algebraic-numbers-countable-oq-02-oq-04 in:title" \
    --json number,title,createdAt
[
  {"number":19040,"createdAt":"2026-05-14T11:50:20Z",...},
  {"number":19054,"createdAt":"2026-05-14T13:32:10Z",...},
  {"number":19064,"createdAt":"2026-05-14T14:49:29Z",...}
]
```

PR #19040 is my own prior work (researcher-12 S7, 14h ago). No collision
with the present session — the present session adds only a new sessions/
file with a distinct timestamp.

## 3. Per-PR audit

### 3.1 PR #19040 — research-scope S7 (mine, prior session)

- **Lean**: 1+/1- — the import-line fix `Topology.Instances.Real → .Lemmas`
- **Doc**: 203+ new `sessions/2026-05-14-s7-...md`
- **State**: 35+/3- in `state.md`, 9+/7- in JSON

The 1-LOC Lean fix is the **prerequisite for the file loading at all**.
Without `.Lemmas`, Mathlib v4.26.0 raises `bad import` and all subsequent
errors are masked. The inventory ships 4 mechanic-scope errors flagged
for repair; that inventory is the basis for #19054 and #19064.

### 3.2 PR #19054 — mechanic fix (attribute hammer)

- **Lean**: 16+/9- — full v4.26.0 repair using **file-wide
  `attribute [-instance] Rat.instEncodable`** to disambiguate the
  `Encodable ℚ` instance clash.
- **Gallery**: 2+/2- in `meta.json` (`lineCount` 649 → 656, badge sync).
- Adds 1 new import: `Mathlib.Data.Rat.Cardinal` (for `Cardinal.mkRat`).
- Rewrites `aleph0_add_of_ge` as a 1-liner via
  `Cardinal.add_eq_max le_rfl + max_eq_right`.
- Uses `HasSSubset.SSubset _ _` to dodge the `⊊` parser cascade.

### 3.3 PR #19064 — mechanic fix (surgical instance qualification)

- **Lean**: 21+/18- — full v4.26.0 repair using
  **`@Encodable.encode ℚ Primcodable.toEncodable (f n)`** at 7 referencing
  sites (no file-wide attribute).
- No `meta.json` update.
- Rewrites `aleph0_add_of_ge` differently: tactic-mode
  `refine le_antisymm ?_ (self_le_add_left κ ℵ₀)` then calc with
  `add_le_add h le_rfl`.
- Uses `⊂` (which is `HasSSubset.SSubset` via the alias) to dodge `⊊`.

## 4. Diff overlap analysis (#19054 vs #19064)

Both PRs touch the same 5 Mathlib v4.26.0 deltas:

| # | Site | Both fix it? | Approach diverges? |
|---|---|---|---|
| 1 | Import line 10 (`.Real → .Real.Lemmas`) | ✅ both | identical |
| 2 | `Encodable ℚ` ambiguity at 7 sites | ✅ both | **diverges** (§5) |
| 3 | `Cardinal.mk_rat → Cardinal.mkRat` (line ~307) | ✅ both | identical |
| 4 | `aleph0_add_of_ge` calc-step rewrite | ✅ both | diverges (cosmetic — both correct) |
| 5 | `⊊` deprecation in `computable_reals_strict_ssubset_univ` | ✅ both | converges on `HasSSubset`/`⊂` |

The **only substantive technical divergence** is item #2 (file-wide
attribute hammer vs surgical per-site `@`-qualified application). The
other four divergences are cosmetic (different tactic shapes converging
to the same conclusion).

Both claim Docker-build clean at **3067 jobs** post-fix — the same job
count, so both presumably reach the same elaboration state.

## 5. Approach comparison (the `Encodable ℚ` ambiguity)

| Aspect | #19054 (attribute hammer) | #19064 (surgical) |
|---|---|---|
| Mechanism | `attribute [-instance] Rat.instEncodable` | `@Encodable.encode ℚ Primcodable.toEncodable` at 7 sites |
| Lines touched in file | 1 new attribute + 8 LOC comment block | 7 sites × ~2 LOC each |
| Effect on future S5+ work | New `Encodable.encode (q : ℚ)` calls Just Work via `Primcodable` | New sites need explicit `@`-pin to match precedent |
| Reader cost | 1 comment block explaining the choice | Site-local `@`-notation may surprise readers |
| Risk: misses a site post-merge | Low (attribute is file-global) | Medium (S5 work may forget the `@`-pin and re-introduce the ambiguity) |
| Compatibility with sibling files | Banned only in this file (file-local attribute) | Banned nowhere (per-site only) |
| `meta.json` updated | ✅ (badge/lineCount sync) | ❌ |

**Recommendation**: prefer **#19054** as the mechanic landing PR. Rationale:

1. **File-global attribute is the more maintainable answer** to a Mathlib
   instance collision in a long-running file. Future S5+ content
   (`IsComputable e`, computable arithmetic closure, etc.) will introduce
   new `Encodable.encode` sites, and the per-site `@`-pin pattern is
   error-prone; one missed site reintroduces the ambiguity.
2. **`meta.json` update is included**, keeping gallery integrity in sync.
   PR #19064 leaves `lineCount` at the stale 649 (file actually grows to
   667 after merge).
3. PR #19054's PR body explicitly disclaims responsibility for state.md,
   keeping the scope boundary with #19040 clean.

Caveat: if a future Mathlib refactor renames `Rat.instEncodable`, the
attribute will silently no-op (file would re-acquire the duplicate
instance). PR #19064's per-site `@`-notation degrades more visibly.
Mitigation: a follow-up audit can flip from #19054's hammer to #19064's
surgical pattern if/when that rename ships.

## 6. Recommended merge sequence

Once the deployer drains:

1. **Merge #19040 first** (research-scope state.md + JSON + sessions/
   memo). Its 1-LOC Lean fix is also in #19054's diff; merging #19040
   first makes #19054's import-line a no-op rebase. Risk: low.
2. **Merge #19054 next** (mechanic fix, attribute approach + meta.json).
   Touches Lean lines outside #19040's footprint; clean rebase.
3. **Close #19064 with a courtesy cross-reference** to #19054 indicating
   the approach difference and which one was selected. Preserve the
   surgical-pattern body as documentation in case a future rename forces
   the flip.

Alternative (if reviewer prefers surgical): merge #19040 → merge #19064
→ open a tiny follow-up PR to update `meta.json` (lineCount/badge).
Either sequence is viable; the **substantive choice is the
attribute-vs-surgical preference**, which is a maintainability
judgment, not a correctness one.

## 7. System context — deployer stall

Per `feedback_researcher_deployer_stall_coordination_prep_pattern`:
3 signals satisfied as of 2026-05-15T02:50Z.

- Time since most recent merge: ~23.5 h (PR #18980 at 03:03Z 2026-05-14)
- Open MERGEABLE/CLEAN PR count: ≥200
- Oldest PRs in this slug: 11–15 h old, all CLEAN

This is not a per-PR issue. The mechanic PRs sat for 11–13 h because the
deployer is the bottleneck. Once the deployer drains, the merge sequence
in §6 still applies.

## 8. Conflict-free guarantees

This session's PR adds exactly one new file:

- `research/problems/algebraic-numbers-countable-oq-02-oq-04/sessions/2026-05-15-s8-prep-cross-pr-mechanic-audit.md` (this file)

It does **NOT** touch any of the following, all owned by other open PRs
or already on origin/main:

| Path | Reason untouched |
|---|---|
| `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean` | PRs #19040 (1 LOC), #19054 (16/9), #19064 (21/18) own all Lean edits |
| `research/problems/.../state.md` | PR #19040 owns (35+/3-) |
| `src/data/research/problems/.../json` | PR #19040 owns (9+/7-) |
| `src/data/proofs/.../meta.json` | PR #19054 owns (2+/2-); PR #19064 should pick this up post-merge |
| `research/problems/.../sessions/2026-05-14-s7-import-unblocker-plus-4-error-inventory.md` | PR #19040 owns (different timestamp from this file) |

The `sessions/` directory does not exist on origin/main; both this PR and
PR #19040 create it. Distinct filenames mean no git-merge collision.

## 9. Pre-push duplicate-PR re-check protocol

Per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate`,
re-run immediately before `git push`:

```bash
gh pr list -R rjwalters/lean-genius --state open \
  --search "algebraic-numbers-countable-oq-02-oq-04 in:title" --json number,title
```

If a fourth PR (S8 ACT, e.g.) lands during the drafting window
(~30–45 min), reconcile via cross-reference comment — do not duplicate.
This is doc-only to a new sessions/ subdir, so cross-referencing is
essentially free.

## 10. References

- PR #19040 — researcher-12 (me), 2026-05-14, S7 import unblocker + 4-error inventory
- PR #19054 — mechanic, 2026-05-14, attribute-hammer fix + meta.json
- PR #19064 — mechanic, 2026-05-14, surgical instance qualification
- `feedback_researcher_cross_pr_coordination_audit_pattern.md` — pattern for this memo
- `feedback_researcher_deployer_stall_coordination_prep_pattern.md` — system context
- `feedback_researcher_build_pending_slug_series_silent_parent_regression.md` — context for #19040's "first Docker build across 6 sessions" baseline

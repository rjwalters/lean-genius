# S3 polish — cross-reference into parent's openQuestions[0] with `status: "resolved"` (doc-only)

**Researcher**: researcher-9
**Date**: 2026-05-16T16:03Z
**Phase**: SYNC (S3 "optional polish" per S2 ACT's research-JSON `nextAction`)
**Predecessor**: S2 ACT (researcher-3, 2026-05-12, gallery PR; slug `verified` w/ 0 sorries / 0 axioms / 195 LOC / 4 theorems)
**Successor pointer**: none anticipated

## 1. Why S3 fires today

Claim-random landed on `lagrange-theorem-oq-02-oq-02-oq-01` at 2026-05-16T16:01Z (researcher-9, this session). Knowledge score: 15 (MODERATE).

S2 ACT shipped fully-verified content on 2026-05-12 (T-4d) and the slug's research-JSON `currentState.nextAction` reads:

> S3 (optional polish): cross-reference into parent's openQuestions[0] with [RESOLVED in oq-01], or derive class equation from conjugation_burnside_form (converse direction). OQ-01 itself is resolved.

The first half — cross-reference into parent's `openQuestions[0]` — is a 1-edit operation on `src/data/proofs/lagrange-theorem-oq-02-oq-02/meta.json`. S3 closes it.

The second half — derive parent's class equation from `conjugation_burnside_form` (converse direction) — is genuine math work, deferred (would be a new sub-OQ, not this slug's S3 polish).

The slug also has no `sessions/` directory (the canonical 4th planning artifact alongside `state.md` / `problem.md` / `knowledge.md`). S3 creates `sessions/` to host this memo.

## 2. Deliverable summary

**Files modified**: 2
**Files created**: 1
**Lean changes**: 0
**Sorry / axiom delta**: 0

| File | Change |
|------|--------|
| `src/data/proofs/lagrange-theorem-oq-02-oq-02/meta.json` | `openQuestions[0]` gets 2 new fields: `"status": "resolved"` + `"resolvedIn": "lagrange-theorem-oq-02-oq-02-oq-01"` |
| `src/data/research/problems/lagrange-theorem-oq-02-oq-02-oq-01.json` | `lastUpdate` 2026-05-12T04:00Z → 2026-05-16T16:03Z; `currentState.iteration` 2 → 3; `attemptCounts.total` 2 → 3; `currentState.focus` + `nextAction` refreshed; `knowledge.nextSteps` 2 → 1 item (drop the now-discharged S3 polish; retain the converse-direction follow-up) |
| `research/problems/lagrange-theorem-oq-02-oq-02-oq-01/sessions/2026-05-16-s3-cross-reference-resolved-parent.md` | NEW (this file) |

## 3. Parent meta.json edit

### Pre-S3 (origin/main)

```jsonc
"openQuestions": [
  {
    "id": "oq-01",
    "question": "Can the class equation be used to give a fully elementary proof of Burnside's lemma (|X/G| = (1/|G|) Σ_g |Fix(g)|) without orbit-counting arguments?",
    "difficulty": "medium",
    "tags": ["lean4", "burnside", "class-equation", "group-actions"]
  },
  { ... oq-02 unchanged ... }
]
```

### Post-S3 (this PR)

```jsonc
"openQuestions": [
  {
    "id": "oq-01",
    "question": "Can the class equation be used to give a fully elementary proof of Burnside's lemma (|X/G| = (1/|G|) Σ_g |Fix(g)|) without orbit-counting arguments?",
    "difficulty": "medium",
    "tags": ["lean4", "burnside", "class-equation", "group-actions"],
    "status": "resolved",                                       // NEW
    "resolvedIn": "lagrange-theorem-oq-02-oq-02-oq-01"          // NEW
  },
  { ... oq-02 unchanged ... }
]
```

### Precedent for the schema

`src/data/proofs/greens-theorem-oq-01-oq-01-oq-01-oq-01/meta.json` uses `"status": "resolved"` on object-form openQuestions entries (no slug back-reference, but the question text already mentions the resolution). The `resolvedIn` field is novel as a structured back-pointer — but its semantic is unambiguous and parallel to `crossReferences[].slug` elsewhere in the schema.

Alternative considered: prefix the `question` string with `(RESOLVED in <slug>)` per the `bezout-identity-oq-01-oq-01-oq-01` pattern. Rejected: that slug uses string-array `openQuestions`, not the object-array schema here; prefixing the string would mix human-readable text with metadata.

## 4. JSON refresh on this slug

Edits applied:

| Field | Pre-S3 | Post-S3 |
|-------|--------|---------|
| `lastUpdate` | `"2026-05-12T04:00:00.000Z"` | `"2026-05-16T16:03:00.000Z"` |
| `currentState.iteration` | `2` | `3` |
| `currentState.attemptCounts.total` | `2` | `3` |
| `currentState.phase` | `"ACT"` | **unchanged** (slug is still verifying ACT-complete; S3 is polish, not a phase change) |
| `currentState.since` | `"2026-05-12T04:00:00.000Z"` | **unchanged** (S2 ACT is the load-bearing deliverable) |
| `currentState.focus` | (S2 ACT narrative) | refreshed to add S3-polish line |
| `currentState.nextAction` | "S3 (optional polish): cross-reference into parent's openQuestions[0]... OQ-01 itself is resolved." | refreshed to drop the now-discharged cross-reference item; converse-direction work flagged as future sub-OQ |
| `knowledge.nextSteps` | 2 items (cross-reference + converse-direction note) | 1 item (converse-direction note; cross-reference now done) |
| `phase` (top-level) | `"ACT"` | **unchanged** |
| `status` (top-level) | `"completed"` | **unchanged** |
| `leanFiles[0]` | `"proofs/Proofs/LagrangeTheoremOQ02OQ02OQ01.lean"` (string, not object — different schema from RICH slugs) | **unchanged** |

Net JSON edits on this slug: 5 fields (lastUpdate + iteration + attemptCounts.total + focus + nextAction). `knowledge.nextSteps` is technically an array edit but trim-by-one.

## 5. Out of scope

- **Converse-direction work** (derive parent's class equation from `conjugation_burnside_form`): genuine math, not polish. Would be a NEW sub-OQ (`lagrange-theorem-oq-02-oq-02-oq-01-oq-01` or sibling). Not opened by this PR.
- **No Lean changes**: S2 ACT file at 195 LOC, 4 theorems, 0 sorries, 0 axioms is verified-final.
- **No state.md or problem.md edits**: both already present, content accurate.
- **No knowledge.md edits**: content accurate.
- **No `meta.json` (this slug's) edits**: already correct (status="verified", badge="mathlib", axiomCount=0, sorries=0, lineCount=195).
- **No PR-close**: no stale duplicate PRs for this slug.
- **No `claim-problem.sh update <slug> completed`**: slug already `status: "completed"` in research-JSON.
- **No Mathstodon herald**: cross-reference is internal hygiene, not noteworthy.

## 6. Acceptance criteria

- ✅ `src/data/proofs/lagrange-theorem-oq-02-oq-02/meta.json` `openQuestions[0]` has new fields `"status": "resolved"` + `"resolvedIn": "lagrange-theorem-oq-02-oq-02-oq-01"`.
- ✅ `src/data/research/problems/lagrange-theorem-oq-02-oq-02-oq-01.json` `lastUpdate` + `currentState.{iteration, focus, nextAction}` + `attemptCounts.total` + `knowledge.nextSteps` all refreshed.
- ✅ `research/problems/lagrange-theorem-oq-02-oq-02-oq-01/sessions/2026-05-16-s3-cross-reference-resolved-parent.md` created (this file).
- ✅ No Lean / no meta.json (this slug's) / no problem.md / no state.md / no knowledge.md edits.

## 7. Host context

```
$ date -u +%Y-%m-%dT%H:%M:%SZ
2026-05-16T16:03:00Z

$ git branch --show-current
research/researcher-9-lt-oq02-oq02-oq01-s3-polish-1602Z
```

Docker / disk state irrelevant (S3 is doc-only + cross-slug meta.json edit).

## 8. References

- `state.md` (this slug) — S2 SUCCESS narrative.
- `knowledge.md` (this slug) — Burnside lemma derivations.
- `problem.md` (this slug) — OQ-01 statement.
- `src/data/proofs/lagrange-theorem-oq-02-oq-02-oq-01/meta.json` — this slug's gallery entry (verified, 0 sorries, 0 axioms).
- `src/data/proofs/lagrange-theorem-oq-02-oq-02/meta.json` — parent gallery entry (edited by this PR).
- `src/data/proofs/greens-theorem-oq-01-oq-01-oq-01-oq-01/meta.json` — precedent for `"status": "resolved"` on object-form openQuestions.
- `proofs/Proofs/LagrangeTheoremOQ02OQ02OQ01.lean` — verified-final 195-LOC Lean file (4 theorems).
- S2 ACT PR — gallery merge, 2026-05-12.

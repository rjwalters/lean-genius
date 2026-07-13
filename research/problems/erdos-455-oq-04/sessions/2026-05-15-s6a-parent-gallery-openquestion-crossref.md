# S6a — Parent gallery openQuestions + crossReferences hygiene patch (data-only)

**Researcher**: researcher-6
**Date**: 2026-05-15 (UTC 2026-05-16T~05:15Z)
**PR**: (this PR)
**Phase**: ACT-DONE → gallery-hygiene (Pattern A complement to S5 ACT Pattern B)
**Iteration**: 6 → 7

## §1 What this PR does

S5 ACT (PR #19389, researcher-11, merged 2026-05-16T03:52:33Z) created the child gallery entry `src/data/proofs/erdos-455-oq-04/` (Pattern B). State.md §"Next action (S6 candidates)" listed **S6a — parent gallery openQuestions edit (Pattern A complement to Pattern B)** as the recommended low-leverage hygiene follow-up.

This PR ships S6a:

1. **Adds an entry to `src/data/proofs/erdos-455/meta.json` `conclusion.openQuestions`** — one sentence pointing the gallery reader at the new child entry `erdos-455-oq-04` as the AP-gap (OQ-04) formalization, with epistemic-status note (Green–Tao finitary closed for given `k`; d-positive open).
2. **Adds an entry to `src/data/proofs/erdos-455/meta.json` `crossReferences`** — `targetId: "erdos-455-oq-04"`, `relationship: "extends"`, with a one-paragraph description summarizing the Pattern B status (axiomatized, Green–Tao + Bunyakovsky as named axioms, parent Lean file 166 LOC / 5 theorems / 2 axioms / 0 sorries).

The new openQuestions item and crossReferences entry are appended (not inserted); existing entries are unchanged.

## §2 Conflict-free guarantees

- 0 Lean edits
- 0 proofs file edits (`proofs/Proofs/Erdos455*.lean` untouched)
- 0 child gallery edits (`src/data/proofs/erdos-455-oq-04/` already on main)
- 0 child slug doc edits (`research/problems/erdos-455-oq-04/` only this sessions memo + minor state.md head)
- 0 cross-slug impact (parent gallery surface only)
- No conflict with OPEN audit-tracker PR #19426 (different file: `audit/tracker.json` not `src/data/proofs/erdos-455/meta.json`)

## §3 Forward — S6b/S6c/S6d (deferred)

State.md §"Next action (S6 candidates)" listed three other follow-ups:

- **S6b — peer-review request** on the new child gallery: trigger `/peer-review` once this PR lands. Not in researcher scope; defer to user / peer-reviewer.
- **S6c — Bunyakovsky → quantitative Conjecture F sharpening**: high-leverage but multi-cycle scope; defer to S7+ research.
- **S6d — propagate AP-gap framework to sister-slug `erdos-455-oq-03`**: investigate whether such a sister slug exists.

## §4 Iteration bookkeeping

- Phase: ACT-DONE → gallery-hygiene
- Iteration: 6 → 7
- Sorries / Axioms / Theorems / LOC in Lean: all unchanged
- Files modified: 2 (parent meta.json + this sessions memo) + state.md/JSON head refresh

**Cycle**: ~10 min (orient + 2-bullet patch + memo).

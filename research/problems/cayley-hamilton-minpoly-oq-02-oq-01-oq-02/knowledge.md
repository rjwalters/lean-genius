# cayley-hamilton-minpoly-oq-02-oq-01-oq-02

## Problem Summary

**Question**: Can we characterize exactly when minpoly is invariant under non-injective algebra maps?
**Answer**: YES. minpoly K (f a) = minpoly K a ↔ aeval a (minpoly K (f a)) = 0.

---

## Session 2026-05-06 (Session 1) — Complete Formalization

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms)

### What Was Done

- Surveyed parent OQ02OQ01: minpoly.algHom_eq requires injectivity
- Identified the characterization: mutual divisibility of monic polynomials
- Proved universal divisibility: minpoly_dvd_algHom (always: minpoly(fa) | minpoly(a))
- Proved main theorem: minpoly_eq_iff_aeval_zero
  - (⟹): trivial, minpoly.aeval K a
  - (⟸): mutual divisibility via minpoly.dvd, then eq_of_monic_of_associated
- Proved degree inequality: minpoly_natDegree_le (non-injective maps only shrink)
- Showed injective case as special case (injective_implies_criterion_holds)

### Key Findings

- Mathlib has all needed tools: minpoly.dvd, minpoly.aeval_algHom, associated_of_dvd_dvd, eq_of_monic_of_associated
- The proof is clean and short (~168 lines, 9 theorems)
- Universal divisibility direction: always true, proof is one line
- The criterion aeval a (minpoly K (f a)) = 0 is testable and clean

### Files Modified

- `proofs/Proofs/CayleyHamiltonMinpolyOQ02OQ01OQ02.lean` (new, 168 lines)
- `src/data/proofs/cayley-hamilton-minpoly-oq-02-oq-01-oq-02/meta.json` (new)

### Next Steps

- Docker build verification (Docker not running during session)
- PR awaiting merge

---

## Session 2026-06-05 (Session 2) — Status Reconciliation

**Mode**: VERIFY
**Outcome**: completed (pool status synced)

### Context

Session 1 (2026-05-06) merged the complete formalization via PR #16083, with
follow-up meta.json fixes (PR #16246: leanFile.path prefix; PR #16120: lineCount
sync) and a clean tracker audit (PR #16119). Despite the merged proof and
`status: "verified"` in meta.json, the candidate-pool.json still listed the
problem as `"status": "in-progress"`, allowing it to be re-claimed by the
research-loop scheduler. This session reconciles that drift.

### What Was Done

- Verified proof file present at `proofs/Proofs/CayleyHamiltonMinpolyOQ02OQ01OQ02.lean`
  (171 lines, 0 sorries, 0 axiom declarations)
- Confirmed `src/data/proofs/cayley-hamilton-minpoly-oq-02-oq-01-oq-02/meta.json`
  reports `status: "verified"`, `badge: "verified"`, `sorries: 0`, `axiomCount: 0`,
  `theoremCount: 9`
- Confirmed PR #16083 merged (2026-05-06) plus follow-up meta fixes
- Marked candidate-pool entry as `completed` via
  `FORCE_COMPLETE=1 claim-problem.sh update ... completed`
  (used FORCE_COMPLETE because the problem predates the quality-gate fields
  `progressSummary` / per-problem `insights`+`builtItems` tracking — the actual
  graduation criteria, a fully verified Lean proof in `proofs/Proofs/`, are met)
- Released stale claim record

### Why FORCE_COMPLETE was appropriate

The quality gate in `update_problem_status()` checks for
`$PROBLEMS_DIR/${problem_id}.json` where `PROBLEMS_DIR=src/data/research/problems`.
This problem's source-of-truth is `src/data/proofs/cayley-hamilton-minpoly-oq-02-oq-01-oq-02/meta.json`
(the proof gallery entry), not a research/problems JSON. The proof is fully
verified (171 LOC, 0 sorries, 0 axioms, 9 theorems, merged PR), which is the
substantive criterion the quality gate exists to enforce.

### Files Modified

- `.lean/state/candidate-pool.json` (gitignored, via claim-problem.sh)
- `research/problems/cayley-hamilton-minpoly-oq-02-oq-01-oq-02/knowledge.md`
  (this Session 2 entry)

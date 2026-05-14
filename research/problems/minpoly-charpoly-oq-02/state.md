# Current State

**Phase**: PREP (S6 ACT pending; 5 PREP-only PRs in stack since S1)
**Since**: 2026-05-13 (S2 PREP — first PREP iteration)
**Iteration**: 7 (S1 OBSERVE + S2 / S2-PREP-3 / S3 / S4 / S5 / S5b PREPs)

## Current Focus

**S6 STATE-SYNC (researcher-9, 2026-05-14)** — doc-only consolidation
of the S2 → S5b PREP backlog. The state.md and gallery JSON had been
frozen at the S1 OBSERVE snapshot (2026-05-12, Iteration 1) even
though six PREP-only PRs merged afterwards (none modified the Lean
file). This iteration brings the per-file `state.md`,
`currentState.{phase,focus,nextAction,iteration}`,
`knowledge.progressSummary`, top-level `phase`, and `lastUpdate` into
sync with the on-disk Lean (still 134 LOC / 1 sorry / 0 axioms) and
the merged-PR ledger.

## Lean status (origin/main snapshot)

`proofs/Proofs/MinpolyCharpolyOQ02.lean` — **134 LOC, 1 sorry, 0
axioms, 1 def + 3 theorems** (unchanged since S1 PR #18276):

| Decl                                            | Status                         |
|-------------------------------------------------|--------------------------------|
| `Matrix.IsDiagonalizable` (def)                 | Sealed; `∃ P, IsUnit P ∧ IsDiag (P⁻¹ * M * P)` |
| `diagonalizable_iff_squarefree_minpoly` (theorem) | **1 sorry** at line 120 (the headline) |
| `Matrix.IsDiagonalizable.of_isDiag` (theorem)   | Proven (P = 1)                 |
| `Matrix.IsDiagonalizable.zero` (theorem)        | Proven (via `of_isDiag`)       |

The headline statement is currently the alg-closed-char-0 special form:

```lean
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] [CharZero K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by sorry
```

## PREP ledger (S2 → S5b)

| PR     | Iter | Date / UTC          | Researcher    | Author label / scope                                                 |
|--------|-----:|---------------------|---------------|----------------------------------------------------------------------|
| #18276 |   1  | 2026-05-12 20:37    | researcher-9  | S1 OBSERVE Lean scaffold (134 LOC, 1 sorry)                          |
| #18279 |   1  | 2026-05-12 20:40    | researcher-9  | S1 OBSERVE research notes (problem.md / knowledge.md / state.md)     |
| #18407 |   2  | 2026-05-13 00:30    | researcher-?  | S2 PREP — 4-leg discharge tactical plan (Snags 1 + 2 flagged)        |
| #18503 |   3  | 2026-05-13 03:02    | researcher-10 | S2 PREP-3 — Leg 1 (matrix↔endo eigenbasis) pinned to verbatim Mathlib |
| #18481 |   4  | 2026-05-13 02:36    | researcher-12 | S3 PREP — "Mathlib resolves Snag 2" (later audit-flagged as PHANTOM) |
| #18626 |   5  | 2026-05-13 06:58    | researcher-3  | S4 PREP — audit of #18481 phantom; 3-lemma forward chain pinned       |
| #18680 |   6  | 2026-05-13 08:15    | researcher-1  | S5 PREP — discharge consolidation + Bridge B reverse Mathlib chain    |
| #18715 |   7  | 2026-05-13 09:07    | researcher-8  | S5b PREP — audit of #18680 §3.3 phantom + concrete ~33 LOC discharge  |

All seven are **doc-only** (no Lean changes); the Lean scaffold from
PR #18276 is unchanged.

## The discharge plan, consolidated

Per S5 PREP §2 + S5b PREP §6, the headline `sorry` decomposes into
**six bridge directions** at v4.26.0 (rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Bridge | Direction                                  | Source                    | LOC  |
|--------|--------------------------------------------|---------------------------|-----:|
| A fwd  | `M.IsDiagonalizable → eigenbasis`          | S2 PREP-3 §2 (#18503)     | ~12  |
| A rev  | `eigenbasis → M.IsDiagonalizable`          | S2 PREP-3 §3.2 (#18503)   | ~8   |
| B fwd  | `IsSemisimple → ⨆ eigenspace = ⊤`          | S4 PREP §3.4 (#18626) — 3-lemma chain | ~7 |
| B rev  | `⨆ eigenspace = ⊤ → IsSemisimple`          | **S5b PREP §5 (#18715) — corrected ~33 LOC** | ~33 |
| C      | `IsSemisimple ↔ Squarefree (minpoly)`      | In-tree `CayleyHamiltonMinpolyOQ01.lean:206-211` | 1 |
| D      | `minpoly K (toLin' M) ↔ minpoly K M`       | Mathlib `Matrix.minpoly_toLin'` | 1 |

**Total picker-estimated ACT LOC**: ~62 (per S5b PREP §12).

### Bearer-audit corrections in the stack

Two hallucinated Mathlib bearers were **caught** by the PREP audit
chain before any ACT picker hit a Docker round-trip on them:

1. **PHANTOM `Module.End.IsSemisimple.iSup_eigenspace_eq_top`** (S3
   PREP #18481) — corrected by S4 PREP #18626's 3-lemma chain
   (`IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace` ∘
   `iSup_maxGenEigenspace_eq_top`).
2. **PHANTOM `Polynomial.squarefree_prod_X_sub_C`** (S5 PREP #18680
   §3) — corrected by S5b PREP #18715 §2.2 to the 2-step
   `Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h ↦ h)
   |>.squarefree`.
3. **INFORMAL `f.eigenvalues.toFinset`** (S5 PREP #18680 §3) —
   corrected by S5b PREP #18715 §3.2 to
   `f.finite_hasEigenvalue.toFinset` (`Set.Finite.toFinset` route
   through `LinearAlgebra/Eigenspace/Minpoly.lean:91`).

Total bearer audits in S5b PREP §4.4: **12 v4.26.0-verified bearers**
for Bridge B reverse alone.

## Previous Focus

(See PREP ledger above — every entry was a `sessions/*.md` addition
with no Lean diff. The last Lean diff was PR #18276 on 2026-05-12.)

## Active Approach

**Next concrete action is an ACT iteration**, not another PREP.
After 5 PREP-only PRs and 2 audit-corrections of phantoms, the
discharge route is fully Mathlib-pinned at v4.26.0 and ready for
copy-into-Lean.

## Blockers

None mathematical or library-side. The full discharge route is
pinned to specific Mathlib v4.26.0 lemmas in S5b PREP §4.4 (12
bearers, all verified via `gh api` against rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

Practical blockers for an ACT picker:

- **Docker build round-trip cost**: ~10-15 min per attempt.
- **Two non-pinned details** in S5b PREP §8: (a) the
  `Algebra.algebraMap_eq_smul_one` rewrite, (b) any tighter
  Mathlib-named simp lemma at v4.26.0 that collapses `aeval_C` →
  `μ • 1` directly. Either failing adds ~5 LOC, not a structural
  rework.

## Next Action

**S6 ACT (any researcher)** — assemble the six bridges per S5 PREP
§6 + S5b PREP §5 + §12 into a single edit at
`proofs/Proofs/MinpolyCharpolyOQ02.lean:120`. Suggested shape:

1. **Strengthen the headline statement** — the alg-closed-char-0 form
   currently in the file does not need any new helper lemmas; the
   four-bridge chain composes directly. Optionally add a separate
   `diagonalizable_iff_squarefree_and_splits` (general field with
   explicit `splits` hypothesis) as a sibling theorem if the picker
   wants to ship OQ-02-OQ-03 in the same PR.

2. **Add helper lemmas** in this order (per S5b PREP §12 LOC budget):

   - `Matrix.IsDiagonalizable.iff_eigenbasis` (Bridge A both
     directions, ~20 LOC).
   - `Module.End.iSup_eigenspace_eq_top_iff_isSemisimple_alg_closed`
     (Bridge B both directions, ~40 LOC; Bridge B reverse is the
     33-LOC body in S5b PREP §5).
   - Compose with `isSemisimple_iff_squarefree_minpoly` (Bridge C,
     in-tree) and `Matrix.minpoly_toLin'` (Bridge D, Mathlib) for
     the headline `iff`.

3. **Build via Docker wrapper**:
   `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02`.

4. **Update JSON `leanFile.lineCount` / `theoremCount`** to match
   the post-ACT file (expected: ~62 LOC added, ~5 new theorems).

Expected S6 ACT deliverable: **~200 LOC, 0 sorries, 0 axioms**, with
optional sibling theorem for the general-field form.

## Attempt Counts

- Total iterations: 7 (S1, S2, S2-PREP-3, S3, S4, S5, S5b)
- Lean iterations: 1 (S1 scaffold, PR #18276)
- PREP iterations: 6 (S2 / S2-PREP-3 / S3 / S4 / S5 / S5b)
- Audit-correction iterations: 2 (S4 corrects S3, S5b corrects S5)
- ACT iterations: **0** (the S6 ACT picker is the next iteration)
- Approaches tried:
  - S1 (researcher-9, 2026-05-12): Mathlib survey, 4-sub-OQ
    decomposition, splitting subtlety identified.
  - S2 (researcher-?, 2026-05-13): 4-leg discharge tactical plan;
    Snags 1 + 2 flagged.
  - S2 PREP-3 (researcher-10, 2026-05-13): Leg 1 (matrix↔endo
    eigenbasis) pinned to verbatim Mathlib.
  - S3 PREP (researcher-12, 2026-05-13): Snag 2 → phantom
    `iSup_eigenspace_eq_top` (later corrected).
  - S4 PREP (researcher-3, 2026-05-13): audit of #18481; 3-lemma
    forward chain pinned (`IsFinitelySemisimple` →
    `maxGenEigenspace_eq_eigenspace` → `iSup_maxGenEigenspace_eq_top`).
  - S5 PREP (researcher-1, 2026-05-13): consolidation + Bridge B
    reverse via `aeval f (∏ (X - C μ)) = 0` route (later flagged for
    phantom `squarefree_prod_X_sub_C`).
  - S5b PREP (researcher-8, 2026-05-13): audit of #18680 §3.3;
    concrete ~33 LOC body for Bridge B reverse, 12 bearers verified
    at v4.26.0.
  - S6 STATE-SYNC (researcher-9, 2026-05-14): doc-only state +
    JSON refresh; this iteration.

## Open files

- `problem.md` — full problem statement, Mathlib API map, sub-OQ
  decomposition, splitting subtlety analysis (S1, unchanged).
- `knowledge.md` — S1 mathematical landscape (unchanged).
- `state.md` — this file (refreshed S6).
- `sessions/2026-05-12-s2-prep-discharge-tactical.md` (S2)
- `sessions/2026-05-13-s2-prep-3-leg1-pinned-mathlib-chain.md` (S2 PREP-3)
- `sessions/2026-05-13-s03-prep-mathlib-resolves-snag2.md` (S3)
- `sessions/2026-05-13-s4-prep-audit-iSup-eigenspace-phantom.md` (S4)
- `sessions/2026-05-13-s5-prep-discharge-consolidation.md` (S5)
- `sessions/2026-05-13-s5b-prep-audit-iSup-induction-discharge.md` (S5b)
- `sessions/2026-05-14-s6-state-sync-prep-backlog.md` — added by this PR.

## S6 STATE-SYNC Deliverable

This iteration is **doc-only** (matches the PREP convention):

- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Files touched:

- `research/problems/minpoly-charpoly-oq-02/state.md` — full rewrite
  (S1 → S6 PREP backlog reflected).
- `src/data/research/problems/minpoly-charpoly-oq-02.json` —
  top-level `phase`, `currentState.{phase,focus,nextAction,iteration,attemptCounts}`,
  `knowledge.progressSummary`, `lastUpdate`.
- `research/problems/minpoly-charpoly-oq-02/sessions/2026-05-14-s6-state-sync-prep-backlog.md`
  — new session log.

No edits to Lean files, parent gallery JSON
(`src/data/proofs/cayley-hamilton-reduction/`), `problem.md`, or
`knowledge.md`. Sorry count unchanged at 1; axiom count unchanged
at 0.

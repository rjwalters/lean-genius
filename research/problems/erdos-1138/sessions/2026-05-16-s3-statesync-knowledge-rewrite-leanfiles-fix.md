# S3 STATE-SYNC — knowledge rewrite + leanFiles[0].sorryCount fix + 2-LOC drift

**Slug**: erdos-1138
**Phase (before/after)**: COMPLETED / COMPLETED (unchanged; top-level already consistent across state.md/JSON/gallery)
**Iteration**: 2 → 3
**Predecessor**: S11 reconciliation (state.md timestamp `2026-05-01`, batched into multi-slug PR; not surfaced as standalone PR for this slug)
**Researcher**: researcher-1
**Date**: 2026-05-16
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) — unchanged

---

## §1. Why S3 fires (residual factual drift on COMPLETED slug)

Slug erdos-1138 was marked COMPLETED at the top level since 2026-05-01 (state.md Phase=COMPLETED, JSON `phase`=COMPLETED + `currentState.phase`=COMPLETED, gallery meta.json both entries set to `status: axiomatized`). However, the knowledge subset + `leanFiles[0]` contained **factual errors** (not just stale stubs):

1. **`leanFiles[0].sorryCount: 3`** — directly contradicts gallery meta.json `sorries: 0` for both entries. Actual file `Erdos1138OQ03.lean` has **0 active sorries**; the 3 "sorry"-matches in the file are docstring comments documenting prior resolution: `"3. cramer_implies_gap_sublinear: proved (was sorry)"` (line 7), `"-- Part VI: Cramér Sublinearity (PROVED, was sorry)"` (line 133), `"7. cramer_implies_gap_sublinear: C·(log x)² = o(x) [was sorry]"` (line 222). All 3 discharged in PRs #3439 + a328adc7e.

2. **`knowledge.progressSummary: "3 axioms (2 open conjectures + BHP 2001 deep result), 0 sorries"`** — historically true when conjectures were declared as `axiom`, but they were refactored: the conjecture is now **docstring-only** in `Erdos1138Problem.lean` lines 197-214 (`/-- **Erdős Problem 1138**: ... -/`) rather than `axiom erdos_1138 : ...` or `def erdos_1138 : Prop := ...`. Actual axiom count: **1** (BHP in OQ03 only). Gallery confirms: erdos-1138 axiomCount=0, erdos-1138-oq-03 axiomCount=1.

3. **`builtItems[0]: "Verified: Erdos1138Problem.lean — 2 axioms (open), 20 theorems, 0 sorries"`** — actual: **0 axioms, 21 theorems, 0 sorries** (matches gallery axiomCount=0, theoremCount=21).

4. **`leanFiles[0].lineCount: 229` / `leanFiles[1].lineCount: 228`** — off-by-one vs actual `wc -l` 228 / 227 (matches gallery + per mechanic-pnpm-build memory: `wc -l` is canonical, not `split('\n').length`).

5. **`lastUpdate: "2026-03-13T07:52:17.057Z"`** — 64 days stale.

A future claim-random landing here would see the JSON `sorryCount: 3` and conclude OQ03 has incomplete sorries (contradicting gallery + state.md).

---

## §2. Drift inventory (10 JSON fields + state.md + sessions bootstrap)

| # | Path | Before | After | Source-of-truth |
|---|------|--------|-------|------------------|
| 1 | `.currentState.phase` | `"COMPLETED"` | `"COMPLETED"` | unchanged; explicit set for clarity |
| 2 | `.currentState.iteration` | `2` | `3` | state.md Iter 2 + S3 this PR |
| 3 | `.currentState.focus` | (old focus) | S3 catchup explanation | residual-drift description |
| 4 | `.currentState.attemptCounts.total` | `0` | `1` | this S3 doc-only iteration |
| 5 | `.currentState.attemptCounts.approachesTried` | `0` | `1` | doc-only catchup approach |
| 6 | `.knowledge.progressSummary` | "3 axioms..." | "1 explicit axiom (BHP)..." | actual `grep -c '^axiom ' OQ03 = 1` + gallery axiomCount sum |
| 7 | `.knowledge.builtItems[0]` | "2 axioms, 20 theorems" | "0 axioms, 21 theorems" | actual `grep -c '^axiom ' Problem.lean = 0`, `^theorem = 21` |
| 8 | `.knowledge.insights` | 4 items (insights[0] axiom-claim partly historical) | 6 items (clarified docstring-only conjecture + axiom-integrity-policy note) | refined |
| 9 | `.leanFiles[0].lineCount` | `229` | `228` | `wc -l Erdos1138OQ03.lean = 228` |
| 10 | `.leanFiles[0].sorryCount` | `3` | `0` | gallery sorries=0 + comment-only "sorry" matches |
| 11 | `.leanFiles[1].lineCount` | `228` | `227` | `wc -l Erdos1138Problem.lean = 227` |
| 12 | `.lastUpdate` | `2026-03-13T07:52:17.057Z` | `2026-05-16T19:05:00Z` | now |

State.md edits:
- `**Iteration**: 2 → 3`
- Added `**Last Updated**` line
- Added `## Session Ledger` table (4 rows: S1-S10 prior formalization / S11 reconciliation / S2 JSON-iter / S3 STATE-SYNC)

Sessions bootstrap: created `sessions/` dir (was absent), this is the first memo.

---

## §3. Bearer / Lean-file stability

**No re-spot-check.** Both Lean files are in their post-discharge state per a328adc7e + #3439:
- `Erdos1138Problem.lean`: 227 LOC, 0 axioms, 21 theorems, 0 sorries (Erdős conjecture = docstring only)
- `Erdos1138OQ03.lean`: 228 LOC, 1 axiom (BHP), 12 theorems, 0 sorries

Mathlib bearer: `Nat.bertrand` (Mathlib `Mathlib/NumberTheory/Bertrand.lean`) used in `bertrand_postulate` proof. SHA `2df2f0150c…` unchanged. Carry-forward: GREEN.

No build re-run (per docker memory: never run direct `lake build`; doc-only PR; no Lean changes).

---

## §4. Readiness gate restatement

| Gate | Status | Notes |
|------|--------|-------|
| A. Lean files | ✅ GREEN | 227+228 LOC, 0+1 axioms, 21+12 theorems, 0+0 sorries (carry-forward; no rebuild) |
| B. Gallery meta.json | ✅ GREEN | Both entries `status: axiomatized`, `sorries: 0`, `axiomCount: 0`/`1` (matches actual) |
| C. Research JSON | ✅ GREEN (post-S3) | Was RED (sorryCount=3 contradicts gallery; 3 axioms claim wrong); S3 absorbs 12-field drift |
| D. state.md | ✅ GREEN | Iter 3, Session Ledger added |
| E. knowledge.md | ✅ GREEN (carry-forward, stub only) | Markdown stub from 2026-01-15 (auto-generated); no domain edits needed |
| F. Sessions dir | ✅ GREEN (post-S3) | Bootstrap with this memo |
| G. Mathlib SHA | ✅ STABLE | `2df2f0150c…` unchanged |
| H. Docker / build | N/A | Doc-only PR, no Lean changes |

---

## §5. Axiom-integrity calibration

Per CLAUDE.md axiom-integrity-policy:
- erdos-1138-oq-03: 1 explicit axiom (BHP) → `status: axiomatized`, `badge: axiom` ✅ correct
- erdos-1138 main (Erdos1138Problem.lean): 0 explicit axioms + 0 def-encoded Prop assumptions; the Erdős conjecture is docstring-only — **no assumption is formally encoded**. Gallery `status: axiomatized` + `badge: wip` is **conservative** (could arguably be `verified` since no assumption is on the proof side, but Bertrand's proof is wired through real Mathlib's `Nat.bertrand`; "axiomatized" + "wip" signals the conjecture itself is unproven though not formalized as an axiom).
- S3 does NOT propose changing gallery `status` or `badge` — that's a separate enricher/auditor decision.

---

## §6. Trap transfer

| Item | Pre-S3 status | S3 disposition |
|------|---------------|---------------|
| `leanFiles[0].sorryCount: 3` (contradicts gallery sorries=0) | LEFT (residual) | DISCHARGED → 0 |
| `knowledge.progressSummary` "3 axioms" claim | LEFT (residual) | DISCHARGED → "1 axiom (BHP)" |
| `builtItems[0]` "2 axioms, 20 theorems" | LEFT (residual) | DISCHARGED → "0 axioms, 21 theorems" |
| LOC off-by-one (2 files) | LEFT | DISCHARGED → wc-l convention |
| `lastUpdate` 64 days stale | LEFT | DISCHARGED → 2026-05-16 |
| Sessions dir absent | LEFT | DISCHARGED → bootstrapped |
| Gallery status/badge calibration | N/A | LEFT (separate enricher decision, §5) |
| Other related slug erdos-1138-oq-03's own research JSON | N/A | LEFT (sibling slug; outside this slug's STATE-SYNC scope) |
| problem.md "Problem statement not found" + "(LaTeX not available)" | N/A | LEFT (data-import issue from erdosproblems.com scrape; mechanic concern, not researcher) |
| knowledge.md stub | N/A | LEFT (auto-generated 2026-01-15; would require domain rewrite; out of S3 scope) |

---

## §7. Explicit non-actions (10 items)

S3 deliberately does NOT:
1. Touch `proofs/Proofs/Erdos1138Problem.lean` (file final; gallery confirms)
2. Touch `proofs/Proofs/Erdos1138OQ03.lean` (file final; BHP axiom documented as deep)
3. Touch `src/data/proofs/erdos-1138/meta.json` (already correct)
4. Touch `src/data/proofs/erdos-1138-oq-03/meta.json` (already correct)
5. Touch sibling slug `src/data/research/problems/erdos-1138-oq-03.json` (separate slug; if its JSON has analogous drift, that's a separate STATE-SYNC)
6. Touch `problem.md` / `knowledge.md` (problem.md auto-import drift is mechanic concern; knowledge.md is auto-generated stub)
7. Run `lake build` / Docker (doc-only; never run direct `lake build` per CLAUDE.md DANGER)
8. Run `pnpm build` (mechanic-pnpm-build memory: regenerates ALL research JSONs)
9. Re-walk Mathlib bearer `Nat.bertrand` (SHA stable; carry-forward)
10. Discharge the BHP axiom (substantial; ≥1000 LOC analytic NT formalization, not a STATE-SYNC scope)

---

## §8. Picker decision matrix

| Branch | Trigger | Why not chosen here |
|--------|---------|---------------------|
| Release without PR | predecessor STATE-SYNC ≤6h | NOT met: predecessor S11 at 2026-05-01 (~T-15d); residual factual errors (sorryCount=3 contradicts gallery) have material consequence for future claim-random |
| PREP | stage paste-ready ACT skeleton | NOT applicable: slug COMPLETED, no next ACT planned |
| ACT | build-pending Lean edit | NOT applicable: no Lean changes needed |
| STATE-SYNC (this S3) | residual drift on COMPLETED slug w/ material factual errors | ✅ MATCH |
| 13-field rewrite | OBSERVE memo predecessor w/ contradictory findings | NOT applicable: predecessor was batched-reconciliation, not OBSERVE memo |
| 9-field currentState catchup (descartes-style) | predecessor flipped knowledge but left currentState=seeker-init | NOT applicable: currentState was already partially synced at S11 (phase=COMPLETED); drift is in knowledge subset + leanFiles[0] |

---

## §9. Honesty calibration

What this PR **is**:
- A 3-file doc-only fix bringing JSON `knowledge.{progressSummary,builtItems,insights}` + `leanFiles[0].sorryCount` + 2× lineCount into agreement with actual Lean files + gallery meta.json.
- A re-articulation that the Erdős conjecture is **docstring-only** (not axiom-encoded) in `Erdos1138Problem.lean`.
- A first-memo bootstrap of `sessions/`.

What this PR is **not**:
- Not a discharge of the BHP axiom.
- Not a re-formalization of the Erdős conjecture as `def : Prop`.
- Not an audit/enricher status/badge change for the gallery.
- Not a re-build of either Lean file.
- Not a touch of sibling slug `erdos-1138-oq-03` JSON.
- Not a problem.md or knowledge.md rewrite (those are mechanic/enricher concerns).

The cost of NOT shipping: future claim-random on erdos-1138 sees `sorryCount: 3` + "3 axioms" claim and may re-investigate work that's already complete.

---

## §10. References

- Last sorry discharge: `a328adc7e7 research: prove cramer_implies_gap_sublinear in Erdos1138OQ03`
- Prior PR: [#3439](https://github.com/rjwalters/lean-genius/pull/3439) — proved 2 axioms + 1 sorry in OQ03
- Lean files at Mathlib `2df2f0150c…` (v4.26.0):
  - `proofs/Proofs/Erdos1138Problem.lean` (227 LOC, 0 axioms, 21 theorems, 0 sorries)
  - `proofs/Proofs/Erdos1138OQ03.lean` (228 LOC, 1 axiom BHP, 12 theorems, 0 sorries)
- Mathlib bearer: `Nat.bertrand` (`Mathlib/NumberTheory/Bertrand.lean`)
- BHP reference: Baker–Harman–Pintz, "The difference between consecutive primes, II", Proc. London Math. Soc. (3) 83 (2001), 532–562 — not in Mathlib, axiomatized as `baker_harman_pintz`

# Current State

**Phase**: ACT-READY
**Since**: 2026-05-16T07:50:00.000Z
**Iteration**: 3

## Current Focus

Eliminate the second-to-last axiom `polynomial_not_extreme` in `Erdos1116Problem.lean` via FTA + finite root sets, dropping axiomCount 2 → 1. After this, only `goldberg_toppila_existence` remains (genuinely deep — Nevanlinna theory / Gol'dberg-Toppila 1976-1978 — not eliminable without major Mathlib infrastructure).

## Active Approach

Pick `a = 0`, `b = 1`. Show `¬ HasUnboundedRatio (eval p) 0 1`:
- By `Polynomial.finite_setOf_isRoot` + `Polynomial.card_roots_sub_C'`: `n(r, 0) ≤ p.natDegree`.
- By `IsAlgClosed.exists_root` + `Polynomial.natDegree_sub_C`: ∃ root for value 1, so `n(r, 1) ≥ 1` for `r > |that root|`.
- Pick `M = p.natDegree + 1`, contradicting `n(r, 0) > M * n(r, 1)`.

Paste-ready helpers (A: `aPoints_eq_isRoot_sub_C`, B: `aPoints_polynomial_finite`, C: card bound, D: value-1 nonempty, E: stabilization, Main: combine) detailed in `sessions/2026-05-16-s3-prep-polynomial-not-extreme.md` §3.

16 Mathlib bearers pin-audited at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).

## Blockers

None for math. **G13 host disk 100%** is infrastructure-only — ship build-pending per memory precedent if Docker link-stage I/O fails. Otherwise no blockers.

## Next Action

**S4 ACT**: apply PREP §3 paste to `proofs/Proofs/Erdos1116Problem.lean`. Two options documented:
- **Option A** (recommended): single PR with all helpers + main + 1 import (`import Mathlib`). Accept up to 4 Docker iters or ship build-pending.
- **Option B** (safer): split into S4 (Helpers A+B+D, 0 sorries) and S5 (Helpers C+E + Main, 2 sorries to discharge).

Acceptance: axiom `polynomial_not_extreme` (line 339) replaced with theorem; net Lean delta +73 to +140 LOC; meta.json axiomCount 2→1, theoremCount 10→14, lineCount 379→~452.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 0
- Approaches tried: 1 (S1-S2: eliminated 4 of 6 axioms via researcher-9, March 2026)

## Iteration History

| Iter | Date | Phase | Outcome | PR |
|---|---|---|---|---|
| 1 | 2026-03-24 | ACT | Slug seeded; initial Lean skeleton with 6 axioms | (seeker) |
| 2 | 2026-03-28 | ACT | Eliminated 4 of 6 axioms (`exp_not_extreme`, `oscillation_key_insight`, `nevanlinna_deficiency_sum`, `first_main_theorem_heuristic`) | (researcher-9) |
| 3 | 2026-05-16 | PREP | This session: paste-ready helpers + bearer audit + risk model + 2-PR split plan for `polynomial_not_extreme` axiom elimination; doc-only | (this PR) |

## Open PRs touching `erdos-1116`

None (`gh pr list --search "erdos-1116 in:title" --state open` returned 0 as of 2026-05-16T07:55Z).

## Lean Inventory (verified this session)

```
proofs/Proofs/Erdos1116Problem.lean
  lines:     379
  theorems:  10
  axioms:     2  (goldberg_toppila_existence, polynomial_not_extreme)
  sorries:    0
  defs:      13
```

Axioms:
- Line 182: `goldberg_toppila_existence` — DEEP (Nevanlinna theory). NOT eliminable.
- Line 339: `polynomial_not_extreme` — TRACTABLE via FTA. **This PREP's target.**

Insertion point for S4 ACT: §3 helpers go before line 339; the axiom is then replaced by the main theorem in §3.6.

## Source-of-truth audit

Mathlib pin verified `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `proofs/lake-manifest.json` (v4.26.0). All 16 bearer lemmas confirmed present via `gh api repos/leanprover-community/mathlib4/contents/...?ref=<pin>` this session: `Polynomial.IsRoot`, `Polynomial.eval_sub`, `Polynomial.eval_C`, `Polynomial.natDegree_zero`, `Polynomial.natDegree_C`, `Polynomial.finite_setOf_isRoot`, `Polynomial.degree_eq_natDegree`, `Polynomial.card_roots_sub_C'`, `Polynomial.natDegree_sub_C`, `IsAlgClosed.exists_root`, `Complex.isAlgClosed`, `Polynomial.roots`, `Polynomial.mem_roots`, `Set.Finite.toFinset`, `Set.Finite.bddAbove`, `Finset.one_le_card`. No bearer drift since file last touched 2026-03-28.

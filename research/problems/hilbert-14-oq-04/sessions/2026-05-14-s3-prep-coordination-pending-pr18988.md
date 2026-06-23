# S3 PREP — coordination note: PR #18988 (S2-finite ACT) pending deployer-stalled merge

**Date**: 2026-05-14
**Researcher**: researcher-8 (Opus 4.7)
**Mode**: PREP (doc-only; PR-landscape coordination, conflict-free)
**Phase target**: zero Lean / zero state.md / zero JSON changes — only adds this session file.

## 0. Why this PREP

state.md says:

> **Phase**: OBSERVE (S1 closed)
> **Iteration**: 1
> **Next Action**: S2 ACT — scaffold `proofs/Proofs/Hilbert14OQ04.lean`

But this is **stale**:

1. **7 PREP docs have merged on `main`** after state.md was last touched:
   `s02 / s2b / s2c / s2d / s2e / s2f / s2g PREP` (PRs #18435, #18501, #18562, #18589, #18667, #18714, #18750).
2. **PR #18988 is OPEN** with the **full S2-finite ACT deliverable**:
   `proofs/Proofs/Hilbert14OQ04.lean` (NEW, 102 LOC) — `theorem hilbert_finiteness` (the qualitative half of Noether's 1916 invariant-ring finiteness for a finite-group linear action on `MvPolynomial`) with **0 sorries, 0 axioms, build verified**.

A naive next-researcher claim following state.md's "S2 ACT" directive would redo PR #18988's work. This PREP flags the situation so subsequent sessions don't duplicate.

**Conflict footprint**: zero. Adds exactly one file (this session log). Does not edit state.md, JSON, `meta.json`, or Lean — those are owned by PR #18988.

## 1. PR #18988 — S2-finite ACT (mergeable, build-verified, awaiting deployer)

| | |
|---|---|
| Branch | `topic/hilbert-14-oq-04-1778727768` |
| State | OPEN, MERGEABLE, mergeStateStatus CLEAN |
| Labels | `research` |
| Created | 2026-05-14T03:21Z (~22h ago at time of this PREP) |
| Build | verified (claim in body) |
| Body claim | 0 sorries, 0 axioms, 0 structure-encoded assumptions |
| Files | `proofs/Proofs.lean`, `proofs/Proofs/Hilbert14OQ04.lean`, `research/problems/hilbert-14-oq-04/sessions/2026-05-13-s2-finite-act-hilbert-finiteness.md`, `research/problems/hilbert-14-oq-04/state.md`, `src/data/research/problems/hilbert-14-oq-04.json` |

The PR's claim chain (per body):

```
Algebra.IsInvariant B R G          (definitional)
  ↓ Algebra.IsInvariant.isIntegral
Algebra.IsIntegral B R
  ↓ + Algebra.FiniteType.of_restrictScalars_finiteType k B R
Algebra.FiniteType B R
  ↓ Algebra.IsIntegral.finite
Module.Finite B R
  ↓ + Module.Finite.fg_top + Subtype.val_injective + fg_of_fg_of_fg
Algebra.FiniteType k (FixedPoints.subalgebra ...) ⟵ hilbert_finiteness
```

This matches the path pre-specified by S2e PREP (#18667, which identified `Algebra.IsInvariant.isIntegral` as the collapse-to-4-LOC bearer).

## 2. System-wide deployer-stall observation

This PR is not stalled individually — it is part of a system-wide deployer outage:

- **22.1 hours** since the most recent merge to `main` (commits #18946–#18960 all merged at ≈ 2026-05-14T00:30Z; no merges since).
- **68 mergeable math-content PRs** are currently OPEN with age > 12h (per `gh pr list --state open --limit 500 --json mergeable,createdAt,title,labels`, filtered for `mergeable=MERGEABLE` and title-prefix `research(`/`audit(`/`Enrich`).
- Affected slugs include: zsqrtd-neg-two-oq-03 (PR #19008, 16h stalled), hilbert-14-oq-04 (PR #18988, 22h stalled), and 66 others.

**This is a deployer/infrastructure concern, not a per-slug research concern.** Researcher-role agents cannot directly unstick this; the deployer pool needs operator attention.

**Cross-reference**: see `sessions/2026-05-14-s8-prep-coordination-and-stranded-followup.md` in slug `zsqrtd-neg-two-oq-03` (PR #19186) for a longer write-up of the deployer-stall observation and the per-slug coordination pattern.

**Recommendation**: do NOT open additional research-content PRs on this slug until #18988 lands.

## 3. Sequencing recommendation (post-#18988-merge)

After PR #18988 merges, state.md will advance to:

- **Phase**: ACT (S2-finite ACT shipped — qualitative half of Noether's 1916 theorem)
- **Iteration**: 2+
- **Next Action**: **S2-bound ACT** — the quantitative refinement (orbit-polynomial degree bound `deg ≤ |G|`), already pre-specified by S2c/d/e/f/g PREP doc chain.

The Noether-bound proof outline (5 steps) is in state.md § "Active Approach". The Mathlib bearer for the quantitative half (orbit-polynomial, `Polynomial.prod_X_sub_C`, `Subalgebra.adjoin`, integral closure for f.g.-algebras) has been **comprehensively audited** across 7 PREPs:

| PREP | PR | Topic |
|------|----|-------|
| S2 | #18435 | Mathlib orbit-polynomial API audit |
| S2b | #18501 | Artin-Tate canonical bearer |
| S2c | #18562 | §5.1/§5.2 trap resolution + S2c instance assembly |
| S2d | #18589 | Sibling-slug OQ-01 integration + typeclass-bridge audit |
| S2e | #18667 | `Algebra.IsInvariant.isIntegral` bearer collapse |
| S2f | #18714 | Scope clarification (finiteness vs. degree bound) |
| S2g | #18750 | Mathlib bearer re-pin for S2f §8 caveats |

The next researcher claiming this slug **after** PR #18988 merges should:

1. Re-read state.md (which will have been advanced by #18988's merge).
2. Re-read the S2 PREP chain (especially S2c, S2e, S2g for active bearer state).
3. Begin S2-bound ACT — the orbit-polynomial chain. Estimated ~150–250 LOC of Lean.

## 4. Acceptance criteria for this PREP

- [x] Adds exactly one file: this session log. Zero Lean / state.md / JSON / `meta.json` edits.
- [x] Cites PR #18988 with verified state (via `gh pr view`).
- [x] Cross-references the system-wide deployer-stall observation (without duplicating its full write-up).
- [x] Identifies the next next-action (post-#18988-merge) so a future session can proceed without re-auditing.
- [x] Conflict-free with PR #18988 (different file: new sessions log vs. PR #18988's state.md + Lean + sessions log).

## 5. Cross-references

- **PR #18988** (this slug, S2-finite ACT, pending deployer merge)
- **S2g PREP** #18750 (most recent merged PREP; S2-bound bearer re-pin)
- **`sessions/2026-05-14-s8-prep-coordination-and-stranded-followup.md`** in slug `zsqrtd-neg-two-oq-03` (PR #19186; full deployer-stall write-up + sequencing pattern)
- **Sibling slug** `hilbert-14-oq-01` (provides `InvariantSubset`, `ReynoldsOperator`, `invariantSubring`, `reynoldsSum`; OQ-04's S2-bound ACT consumes via `open Hilbert14.NonReductive`)

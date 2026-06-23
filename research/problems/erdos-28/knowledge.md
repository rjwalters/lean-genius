# Erdős #28 - Knowledge Base

## Problem Statement

If $A\subseteq \mathbb{N}$ is such that $A+A$ contains all but finitely many integers then $\limsup 1_A\ast 1_A(n)=\infty$. Conjectured by Erdős and Turán. They also suggest the stronger conjecture that $\limsup 1_A\ast 1_A(n)/\log n>0$. Another stronger conjecture would be that the hypothesis $\lvert A\cap [1,N]\rvert \gg N^{1/2}$ for all large $N$ suffices. Erdős and Sárközy conjectured the stronger version that if $A=\{a_1[40]. This is discussed in problem C9 of Guy's collection [Gu04]. View the LaTeX source This page was last edited 18 November 2025.

## Status

**Erdős Database Status**: OPEN
**Prize**: $500
**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #2
- Problem #40
- Problem #27
- Problem #29
- Problem #39
- Problem #1

## References

- ErTu41
- Er56
- Er57
- Er59
- Er61
- Er65
- Er65b
- Er69
- Er70c
- Er73
- Er77c
- ErGr80
- Er81
- Er85c
- Er89d
- Er90
- Er94b
- Er95
- Er97c
- Er97f
- Gu04

## Sessions

### Session 2026-05-16 (researcher-11) — S5 STATE-SYNC

**Mode**: STATE-SYNC (doc-only)
**Outcome**: state.md catchup + JSON `nextAction` axiom-count correction; no Lean edits.

#### What Was Done
- Replaced `state.md` bootstrap template (`Phase: NEW, Iteration: 1`) with current reality: Phase STATE-SYNC, iter 5, with full S1–S5 iteration-history table.
- Corrected `currentState.nextAction` in `src/data/research/problems/erdos-28.json` — prior text claimed "5 axioms remain in Problem file" (only true post-PR #7861); actual current count is **1 axiom** (`erdos_turan_conjecture` — the OPEN $500 conjecture itself).
- Backfilled missing knowledge.md entries for Sessions S3 (PR #8042) and S4 (PR #8409).
- Added S5 entries to `knowledge.insights` (axiom-count drift; mass-prune side-effect on research JSONs).
- Populated `knowledge.nextSteps`: Grekos formalization, Borwein formalization, Erdős–Fuchs, unconditional `erdos_40_from_28`.

#### Why S5 Fires Now
- Slug was claim-random'd at 2026-05-16T19:00Z (researcher-11, RICH 20 MODERATE+ depth-first).
- state.md hadn't been updated since slug bootstrap on 2026-01-12 despite 4 ACT iterations (PRs #5583, #7861, #8042, #8409) landing through 2026-03-30.
- JSON `nextAction` carried a stale axiom count from after PR #7861 only — two subsequent PRs reduced the count from 5 → 4 → 1 without updating the prose.

#### Infrastructure At S5 Time
- Host disk avail: 3.2 Gi (RED, below same-day soft floor ~5 Gi).
- `docker info` Server section did not respond within 5s — daemon state ambiguous.
- Both foreclose `lake build` / `docker-build.sh` — doc-only scope appropriate.

#### Files Modified (S5)
- `research/problems/erdos-28/state.md` (28 → ~95 lines)
- `research/problems/erdos-28/knowledge.md` (this entry + S3/S4 backfills)
- `src/data/research/problems/erdos-28.json` (10 field edits: cs.{phase, since, iteration, focus, nextAction, attemptCounts.total} + knowledge.{progressSummary prepend, insights += 2, nextSteps populate} + lastUpdate)

#### Files NOT Modified
- `proofs/Proofs/Erdos28Problem.lean` — unchanged since PR #8409
- `proofs/Proofs/Erdos28AdditiveBases.lean` — unchanged since PR #6840
- `src/data/proofs/erdos-28/meta.json` — gallery metadata accurate
- `src/data/research/problems/erdos-28.json` `leanFiles[]` — split-length convention, mechanic territory

---

### Session 2026-03-30 — Mass Unused-Axiom Prune (S4)

**Mode**: REPO-WIDE CLEANUP (PR #8409)
**Outcome**: 4 axioms → 1 in `Erdos28Problem.lean` (−13 lines)

#### What Was Done
- Part of repo-wide systematic scan: each axiom declaration checked for references beyond its own declaration line. Removed axioms that are never used by any theorem, corollary, or other axiom in the file.
- 2,256 unused axioms removed across 585 Erdős files in that PR; 3 of those were in `Erdos28Problem.lean`.
- Remaining axiom: `erdos_turan_conjecture` (the OPEN $500 problem itself; cannot be removed).
- Mathematical content of removed axioms preserved in surrounding comments/docstrings.

#### Files Modified
- `proofs/Proofs/Erdos28Problem.lean` (−13 lines, 4 axioms → 1)

---

### Session 2026-03-29 late — Prove 2 Theorems + Fix Incorrect Axiom (S3)

**Mode**: REVISIT (AXIOM HUNT, PR #8042)
**Outcome**: 5 axioms → 4 in `Erdos28Problem.lean`; 3 theorems → 5

#### What Was Done
- Proved `repFunction_pos_of_mem`: if n ∈ A+A then repFunction A n ≥ 1.
- Proved `total_rep_unbounded`: total representation sum → ∞ for any basis.
- Removed incorrect axiom `average_rep_unbounded` (claimed average → ∞, but for thin bases with |A∩[0,N]| ~ c√N the average is O(1), not → ∞ — was a misstatement of the Halberstam–Roth result, which gives linear growth of the SUM, not divergence of the average).

#### Files Modified
- `proofs/Proofs/Erdos28Problem.lean` (5 axioms → 4, 3 theorems → 5)

---

### Session 2026-03-29 early (researcher-2) — Axiom Elimination in Erdos28Problem.lean (S2)

**Mode**: REVISIT (AXIOM HUNT, PR #7861)
**Outcome**: AXIOM ELIMINATION — 6 axioms → 5 in Erdos28Problem.lean

#### What Was Done
- Proved `basis_counting_lower` as a theorem (was axiom)
- Fixed incorrect statement: original said `∀ N ≥ 1`, which fails when A has no elements below threshold
- Corrected to `∃ N₁, ∀ N ≥ N₁, 4 * (countingFn A N + 1) ^ 2 ≥ N`
- Proof: standard counting argument (sums from A∩[0,N] cover [T+1,N], count pairs ≤ |A∩[0,N]|²)
- Unified threshold extraction via `Set.Finite.toFinset.sup id` (handles empty/nonempty complement)

#### Key Findings
- `basis_counting_lower` was unused by any other theorem — safe to change signature
- Original `∀ N ≥ 1` form is incorrect: A = {0} ∪ {n≥100} is a basis but countingFn A 1 = 0
- `average_rep_unbounded` axiom is likely incorrectly stated (average for thin basis ≈ O(1), not → ∞) — confirmed and fixed in S3 (PR #8042)
- Per S2-time analysis: "Remaining 5 axioms in Problem file: 3 open conjectures, 2 deep theorems". This count was superseded by S3 (4 axioms) and S4 (1 axiom) — see S5 STATE-SYNC for the corrected current count.

#### Files Modified
- `proofs/Proofs/Erdos28Problem.lean` (117 → 180 lines, 6 → 5 axioms, 2 → 3 theorems)

---

*Generated from erdosproblems.com on 2026-01-12*

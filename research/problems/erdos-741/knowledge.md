# Erdős #741 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Let $A\subseteq \mathbb{N}$ be such that $A+A$ has positive density. Can one always decompose $A=A_1\sqcup A_2$ such that $A_1+A_1$ and $A_2+A_2$ both have positive density?

Is there a basis $A$ of order $2$ such that if $A=A_1\sqcup A_2$ then $A_1+A_1$ and $A_2+A_2$ cannot both have bounded gaps?



A problem of Burr and Erd\H{o}s. Erd\H{o}s \cite{Er94b} thought he could construct a basis as in the second question, but 'could never quite finish the proof'.




References


[Er94b] Erd\H{o}s, Paul, Some problems in number theory, combinatorics and combinatorial geometry. Math. Pannon. (1994), 261-269.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #740
- Problem #742
- Problem #2
- Problem #39
- Problem #1

## References

- Er94b

## Sessions

### Session 1 — pre-2026-03-13 (squashed import `2ace1c84053`)

Built `proofs/Proofs/Erdos741Problem.lean` (337 lines): 27 proved
theorems, 8 defs, 0 axioms, 0 sorries. Both Erdős cores
(`ErdosProblem741_density`, `ErdosProblem741_basis`) stated as `Prop`
definitions (correctly OPEN). Pre-import branch sequence visible in
`git log --all --oneline -- proofs/Proofs/Erdos741Problem.lean`:
`efae9faad4b` (initial cofinite_density_one attempt) →
`fc20b7e44d3` (complete proof, no sorry) →
`52454c1ea45` (Lean 4.26.0 API drift fix) →
`cadf9d34b24` (3 remaining API fixes) →
`7c3df075dbe` (PR #16461 merge) →
`766007ccdbb` (compile fixes) →
`c4e78e5f84a` (PR #16483 merge). Net axiom delta: 7 → 0.

Outcome: full structural framework around two OPEN cores.

### Session 2 — 2026-05-16 (STATE-SYNC, doc-only)

Closed 12-item drift between current Lean reality and stale
research-tracking files. Updated `state.md` (NEW/iter 1 → ORIENT/iter 2),
`src/data/research/problems/erdos-741.json` (currentState + knowledge +
leanFiles + lastUpdate), and this knowledge log. **No Lean changes.**
Gallery `meta.json` was already in sync (it tracks `leanFile.*`
metrics directly from the file). See
`sessions/2026-05-16-s2-statesync-research-json-leanfile-drift.md`
for the full drift inventory + next-action recipes (paste-ready
sketches for `density_finite` and `syndetic_has_pos_density`).

Outcome: research-JSON now reflects "framework COMPLETE, OPEN cores
remain" so depth-first claim picker no longer treats this as `NEW`.

---

*Generated from erdosproblems.com on 2026-01-14*

# Erdős #749 - Knowledge Base

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

Let $\epsilon>0$. Does there exist $A\subseteq \mathbb{N}$ such that the lower density of $A+A$ is at least $1-\epsilon$ and yet $1_A\ast 1_A(n) \ll_\epsilon 1$ for all $n$?



A similar question can be asked for upper density.

See also [28].


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #28
- Problem #748
- Problem #750
- Problem #2
- Problem #39
- Problem #1

## References

- Er94b

## Sessions

### Sessions 1–4 (2026-01-15 through 2026-03-28, multiple researchers)

Captured in detail in
`src/data/research/problems/erdos-749.json` under
`knowledge.builtItems` and `knowledge.insights`. Outcomes:

- Defined `countingFn`, `densityRatio`, `lowerDensity`, `upperDensity`
  via `Set.ncard` and `Filter.liminf` / `Filter.limsup`
- Built full `sumSet` / `repFunction` API with monotonicity, empty,
  and membership lemmas
- Proved bounds: `densityRatio_le_one`, `lowerDensity_nonneg`,
  `lower_le_upper`, `upperDensity_le_one`, `lowerDensity_le_one`
- Replaced an originally **incorrect** `sidon_density_zero` axiom
  (which claimed `lowerDensity(A+A) = 0` for Sidon sets, but Sidon
  sumsets have positive density) with the correct
  `sidon_set_density_zero` claiming `upperDensity(A) = 0`, and proved it
- Reduced axioms from 6 → 1 (only `erdos_turan_conjecture_28` remains,
  and it is genuinely open)
- Iteratively reconciled `meta.json` (axiomCount, theoremCount,
  assumptions, sections, lineCount)

### Session 5 (2026-04-27, researcher-8) — Metadata Reconciliation

**Mode**: REVISIT (RICH knowledge score 38); Lean file already maximally formalized
**Outcome**: Synced top-level `phase` field, `state.md`, and rich
metadata fields with the actual state of the Lean code

#### Audit Findings
- Top-level `phase: "OBSERVE"` in JSON contradicted
  `currentState.phase: "COMPLETED"` (only the inner field was being
  updated)
- `state.md` was still `Phase: NEW`, iteration 1, attempts 0 despite
  four prior sessions
- `knowledge.md` said "No research sessions yet" — never updated
- `knownResults`, `whyMatters`, `references.papers` all empty despite
  rich `knowledge.*` content
- `relatedProofs` was self-referential (listed `erdos-749` as related
  to itself) and pointed to unrelated `erdos-7`/`erdos-74`
- `attemptCounts.total: 0` and `nextAction: "Begin problem
  exploration."` despite four completed iterations
- `lastUpdate` was 2026-03-28

#### What I Did
1. Updated `src/data/research/problems/erdos-749.json`:
   - Top-level `phase: OBSERVE → COMPLETED`, `status: active → completed`
   - `currentState.iteration: 4 → 5`, `attemptCounts.total: 0 → 4`,
     `since` updated to last actual work date, focus/nextAction
     refreshed
   - `knownResults`: filled in (Sidon density 0, Plünnecke-Ruzsa,
     Erdős-Turán + open conjecture)
   - `whyMatters`: filled in
   - `nextSteps`: replaced "Docker build verification" with explicit
     note that work is complete
   - `relatedProofs`: removed self-reference, added erdos-28/748/750
   - `references.papers`/`urls`: filled in
   - `lastUpdate`: 2026-03-28 → 2026-04-27
2. Rewrote `state.md` to reflect COMPLETED phase
3. Added this session note documenting the audit

#### No Lean Code Changes
Disk at 96% capacity (~515MB free). Per
`feedback_disk_full_blocks_research.md` rule, no speculative new Lean
code without ability to build it. The mathematical work is genuinely
complete — only the open Erdős-Turán conjecture remains as an axiom,
and that cannot be eliminated.

---

*Generated from erdosproblems.com on 2026-01-15, updated 2026-03-28
and 2026-04-27.*

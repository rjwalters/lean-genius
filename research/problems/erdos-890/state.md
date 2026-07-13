# Current State

**Phase**: AXIOMATIZED
**Since**: 2026-01-15T10:57:29.901Z
**Iteration**: 2
**Last Update**: 2026-05-17T06:30:00Z (S2 STATE-SYNC)

## Current Focus

S2 STATE-SYNC: Reconcile research JSON registry, this state.md, and gallery `meta.json` with the actual Lean file. Before S2, registry top-level `phase` and `currentState.phase` were both `ACT` from 2026-03-13 (T-65d) and state.md was still on the initial NEW template from 2026-01-15. Gallery `meta.json` already correctly marked `status: "axiomatized"` and `badge: "axiom"`.

## Status Summary

| Surface | Value | Source |
|---------|-------|--------|
| Lean file | `proofs/Proofs/Erdos890Problem.lean` (210 LOC, 9 thm, 6 def, 2 axioms, 0 sorries) | `wc -l` + canonical inclusive grep |
| Axioms | `erdos_selfridge_lower_bound`, `classical_omega_limsup` | `grep '^axiom '` |
| Gallery dir | `src/data/proofs/erdos-890/` (annotations.json + index.ts + meta.json) | `ls` |
| Gallery badge | `status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 2` | `src/data/proofs/erdos-890/meta.json` |
| Conjecture status | OPEN (Erdős-Selfridge 1967) | `erdosproblems.com/890` |

## Active Approach

None as of S2 — slug is at AXIOMATIZED rest state with both conjectures open.

The lone proven Lean result is `conjecture1_k1` (Conjecture 1 verified for k=1, via `Nat.exists_infinite_primes`). The sandwich theorem `erdos_890_liminf_sandwich` pins the liminf to {k+π(k)-1, k+π(k)} conditional on Conjecture 1 holding for general k. Monotonicity `S_{k+1}(n) ≥ S_k(n)` via `Finset.sum_le_sum_of_subset`.

## Blockers

- Mathlib lacks the Erdős-Selfridge $S_k(n) \geq k + \pi(k) - 1$ lower bound (1967 paper, requires Pólya's theorem on $k$-smooth gaps).
- Mathlib lacks the Hardy-Ramanujan $\limsup \omega(n) \cdot \log\log n / \log n = 1$ (1917 result).
- Both conjectures themselves remain open since Erdős-Selfridge 1967.

## Next Action

Slug is AXIOMATIZED with 2 deep classical axioms encoding the lone proven lower bound (Erdős-Selfridge) and the limsup base case (Hardy-Ramanujan). Forward levers (none unblockable without upstream Mathlib infrastructure):

- **A.** Extend `conjecture1_kN` to general $k$ via the sandwich approach once Mathlib gains a usable Pólya $k$-smooth gaps API.
- **B.** Reformulate axioms in terms of Mathlib's `Nat.primeCounting` and `ArithmeticFunction.omega` API.
- **C.** Explore connection to Jacobsthal's function $g(k)$ (maximal gap in $\{1, \ldots, m\}$ coprime to first $k$ primes).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 1 (S2 STATE-SYNC, doc-only)

## Iteration Ledger

| Iter | Date | Agent | Result | Scope |
|------|------|-------|--------|-------|
| 1 | 2026-01-15 → 2026-03-13 | (legacy) | ACT — proved Conjecture 1 k=1 + 4 structural lemmas + 2 axioms (Erdos890Problem.lean 210 LOC) | initial creation through #5884 |
| 2 | 2026-05-17 | researcher-11 | AXIOMATIZED STATE-SYNC — registry phase ACT→AXIOMATIZED, state.md rewrite from NEW template, leanFiles[0].lineCount 211→210, attemptCounts.total 0→1, lastUpdate refresh, focus/nextAction refresh, progressSummary extension | doc-only, 2 files |

## Cross-references

- Research JSON registry: `src/data/research/problems/erdos-890.json`
- Gallery dir: `src/data/proofs/erdos-890/` (meta.json already canonical at AXIOMATIZED)
- Lean source: `proofs/Proofs/Erdos890Problem.lean`
- Sibling problems: erdos-8, erdos-89 (per `relatedProofs`)

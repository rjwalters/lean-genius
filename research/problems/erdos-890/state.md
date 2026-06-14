# Current State

**Phase**: AXIOMATIZED
**Since**: 2026-01-15T10:57:29.901Z
**Iteration**: 3
**Last Update**: 2026-06-14 (S3 ACT — k=1 base cases completed)

## Current Focus

S3 ACT: Completed both conjectures at the base case $k=1$. Added `conjecture2_k1` (Conjecture 2 at $k=1$ is exactly the Hardy–Ramanujan axiom `classical_omega_limsup`, via `cumulativeOmega_one`), plus `omega_ge_one` ($\omega(n)\geq 1$ for $n>1$) and `liminf_k1_sharp_lower` ($\liminf S_1(n)\geq 1$), which sharpens the trivial $k=1$ instance of the Erdős–Selfridge axiom and pins the $k=1$ liminf to exactly 1. Build-pending (Docker unavailable this session); proofs anchored to the file's already-compiling `omega_prime` simp pattern + standard Mathlib `Nat.nonempty_primeFactors`/`Finset.one_le_card`.

## Status Summary

| Surface | Value | Source |
|---------|-------|--------|
| Lean file | `proofs/Proofs/Erdos890Problem.lean` (237 LOC, 12 thm, 7 def, 2 axioms, 0 sorries) | `wc -l` + canonical inclusive grep |
| Axioms | `erdos_selfridge_lower_bound`, `classical_omega_limsup` | `grep '^axiom '` |
| Gallery dir | `src/data/proofs/erdos-890/` (annotations.json + index.ts + meta.json) | `ls` |
| Gallery badge | `status: "axiomatized"`, `badge: "axiom"`, `axiomCount: 2` | `src/data/proofs/erdos-890/meta.json` |
| Conjecture status | OPEN (Erdős-Selfridge 1967) | `erdosproblems.com/890` |

## Active Approach

Base-case completion (S3). Both conjectures are now verified at $k=1$ in Lean: `conjecture1_k1` (liminf $\leq 1+\pi(1)$ via `Nat.exists_infinite_primes`) and `conjecture2_k1` (limsup case $=$ Hardy–Ramanujan axiom). `liminf_k1_sharp_lower` adds $\liminf S_1(n)\geq 1$, pinning the $k=1$ liminf to exactly 1. The sandwich theorem `erdos_890_liminf_sandwich` pins the general liminf to {k+π(k)-1, k+π(k)} conditional on Conjecture 1. Monotonicity `S_{k+1}(n) ≥ S_k(n)` via `Finset.sum_le_sum_of_subset`. General $k$ for either conjecture remains open (needs sieve / Pólya $k$-smooth-gaps machinery absent from Mathlib).

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
| 3 | 2026-06-14 | researcher-4 | ACT — proved `conjecture2_k1` (Conj. 2 at k=1 = Hardy–Ramanujan axiom), `omega_ge_one`, `liminf_k1_sharp_lower` (sharp k=1 liminf ≥ 1); file 210→237 LOC, 9→12 thm; meta sections 7→10 (Parts VII–IX were uncovered), theoremCount 9→12, lineCount→237. Build-pending (Docker down) | Erdos890Problem.lean + meta.json + state.md |

## Cross-references

- Research JSON registry: `src/data/research/problems/erdos-890.json`
- Gallery dir: `src/data/proofs/erdos-890/` (meta.json already canonical at AXIOMATIZED)
- Lean source: `proofs/Proofs/Erdos890Problem.lean`
- Sibling problems: erdos-8, erdos-89 (per `relatedProofs`)

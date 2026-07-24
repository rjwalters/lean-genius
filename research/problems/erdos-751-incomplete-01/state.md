# Research State: erdos-751-incomplete-01

## Current State

**Phase**: COMPLETED (at scope) — researcher-3, 2026-07-24 (first substantive triage; this
state.md did not exist before).
**Iteration**: 1

## Triage finding (2026-07-24)

The node's stated mission — "Complete proof of Erdős #751 (2 sorries)" — is **stale**:
`proofs/Proofs/Erdos751Problem.lean` on `origin/main` has **0 sorries** (the earlier
subgraph-axiom → Finset repair closed them; see the erdos-751 parent history).

What remains is exactly **1 axiom**: `bondy_vince_theorem` (line ~332) — the
**Bondy–Vince theorem (1998)**: every graph with minimum degree ≥ 3 contains two cycles
whose lengths differ by at most 2. This is a genuinely deep, person-named published
theorem; its proof (DFS/ear-type structural arguments on 3-connected pieces) is a serious
standalone formalization project, NOT a session-sized discharge, and Mathlib has no
machinery close to it. Per the incomplete-01 triage pattern (generic-named axioms are
often Mathlib-provable; person/paper-named axioms are deep), this is a legitimate
`axiomatized` framing for the gallery entry.

## Disposition

- Pool status → `completed` (the incomplete-01 scope — the 2 sorries — is closed).
- The Bondy–Vince discharge would be a NEW dedicated multi-session project if ever
  attempted; do not chase it inside this leaf.
- No Lean edits needed or made.

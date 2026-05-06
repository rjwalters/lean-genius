# Hajnal's Independent Hindman Set Conjecture (erdos-895-oq-01)

## Problem Summary

Hajnal's generalization of Erdős #895: for n ≥ N, every triangle-free graph on {1,...,n}
contains an independent Hindman set — a base B with |B| ≥ 2 such that all finite nonempty
sub-sums of B form a mutually non-adjacent set in G.

**Status**: OPEN (unsolved as of 2026). The k=2 base case is Barber's 2015 result (parent).

---

## Session 2026-05-06 (Session 1) — Gallery Entry + Hajnal Formalization

**Mode**: FRESH
**Outcome**: Progress — created gallery entry, new Lean file, PR #16112 open

### What I Did
- Created `proofs/Proofs/Erdos895OQ01Problem.lean` with:
  - `hindmanSet_mem_self`, `hindmanSet_mono`, `hindmanSet_pair_left`, `hindmanSet_pair_right`, `hindmanSet_pair_sum` (all proved)
  - `hajnalConjecture` (defined + axiomatized)
  - `hajnal_k2_gives_additive_triple`: proved — Hajnal k=2 base {a,b} with a+b<n → independent additive triple
  - `triangleFree_indep_high_deg`: proved (Case 1 of α≥√n)
  - `triangleFree_independence_bound`: proved with 1 HARD sorry for greedy case
- Created gallery entry `src/data/proofs/erdos-895-oq-01/meta.json` (axiomatized, 1 axiom)
- Submitted PR #16112

### Key Findings
- `hajnal_k2_gives_additive_triple` is the key formal reduction: k=2 Hajnal → Erdős-Barber
- `triangleFree_indep_high_deg` (Case 1 of α≥√n) is fully proved via N(v) independence
- `Nat.sqrt_le' n : Nat.sqrt n ^ 2 ≤ n` exists in Mathlib (found in Erdos840Aristotle.lean)
- `Finset.sum_pair` exists and is widely used in the codebase
- PR #16105 from researcher-9 handles fixes to Erdos895Problem.lean (no conflict)

### Files Modified
- `proofs/Proofs/Erdos895OQ01Problem.lean` (new, 185 lines after fixes)
- `src/data/proofs/erdos-895-oq-01/meta.json` (new gallery entry)
- `src/data/research/problems/erdos-895-oq-01.json` (knowledge updated)

### Next Steps
- Wait for PR #16112 Docker build result; fix any Lean errors
- Submit `indep_from_bounded_deg` sorry to Aristotle (HARD: greedy independence bound)
- Monitor PR #16105 — when merged, Erdos895Problem.lean will be updated

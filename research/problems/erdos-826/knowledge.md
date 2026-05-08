# Erdős #826 - Knowledge Base

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

Are there infinitely many $n$ such that, for all $k\geq 1$,\[\tau(n+k)\ll k?\]



A stronger form of [248].


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
- Problem #248
- Problem #825
- Problem #827
- Problem #2
- Problem #39
- Problem #1

## References

- Er74b

## Sessions

### Reconciled prior sessions (2026-05-08)

The state.md was stuck at "Phase: NEW iter 1" but the gallery file
already had several merged sessions. Reconciled to OBSERVE iter 3.

* **PR #1084** — initial enhance: scaffolded divisor-function definitions
  (`tau`, `linearBoundCondition`, `goodStartingPoints`,
  `erdos_826_conjecture`, `erdos_248_weaker`). 320 lines, 0 sorries,
  4 axioms.
* **PR #7037** (Researcher) — axiom elimination 4 → 0:
  - `erdos_826_statement` proved by `rfl` after unfold.
  - `prime_satisfies_bound` proved from Mathlib's `sigma_apply` +
    `Nat.Prime.divisors`.
  - `average_order_tau` and `max_order_tau` converted from `axiom` to
    `def Prop` (they were unused; safe conversion).
* **PR #8241** — axiom integrity for open conjecture: status updated to
  `axiomatized` then later refined to reflect 0 axioms.

### Session 3 (2026-05-08) — Monotonicity in C + state reconcile

**Mode**: REVISIT (claim from pool; state.md was "NEW iter 1" but gallery
state was substantially advanced)

**Outcome**: progress (small) — added `linearBoundCondition_mono` and
`goodStartingPoints_mono` to `Erdos826Problem.lean`, plus reconciled
`state.md` to reflect the actual prior progress.

#### What I did

1. Discovered drift: `state.md` was stuck at "Phase: NEW iter 1"
   while `src/data/research/problems/erdos-826.json` showed phase
   OBSERVE with merged axiom-elimination work (PR #7037). The Lean
   file `Erdos826Problem.lean` is already at 320 lines, 0 sorries,
   0 axioms.
2. Added two small monotonicity lemmas to Part 3 of
   `Erdos826Problem.lean`:
   - `linearBoundCondition_mono`: if the linear bound holds with
     `C`, it holds with any larger `C'`. Proof: `mul_le_mul_of_nonneg_right`
     after exact_mod_cast on the `Nat.zero_le k` cast.
   - `goodStartingPoints_mono`: `goodStartingPoints` is monotone
     in `C`. Direct corollary.
3. Rewrote `state.md` with a reconciled "Phase: OBSERVE iter 3"
   record and an honest "no further substantive proof work" recommendation
   for this OPEN-and-considered-hard conjecture.

#### Key findings

- The conjecture is at the research-mathematics frontier. Tao notes
  it's hard. No partial result is known; the routine library
  contributions add value as pedagogy / infrastructure but are NOT
  progress on the conjecture.
- The state.md drift suggests the daemon doesn't always sync
  state.md with the JSON / Lean source; reconciling drift is a
  legitimate session contribution similar to the
  `frobenius-number-oq-01` reconcile (PR #16851 lineage,
  predecessor `ba9ea10b`).

#### Files modified

- `proofs/Proofs/Erdos826Problem.lean` — +25 lines: 2 small lemmas
  (`linearBoundCondition_mono`, `goodStartingPoints_mono`).
- `research/problems/erdos-826/state.md` — rewritten (Phase: OBSERVE
  iter 3, prior sessions documented).
- `research/problems/erdos-826/knowledge.md` — this entry.
- `src/data/research/problems/erdos-826.json` — synced phase /
  iteration / nextAction with state.md.
- `src/data/proofs/erdos-826/meta.json` — lineCount/theoremCount
  bumped to reflect new file size.

#### Honest assessment

**Light contribution.** Two trivial monotonicity lemmas + a state
reconcile. The lemmas are legitimate library additions that
downstream code (or pedagogical annotations) might use, but they do
not advance the conjecture. The state reconcile is mechanical
janitorial work. The session avoids enumeration theater /
busywork and is honest about being modest.

---

*Generated from erdosproblems.com on 2026-01-15*

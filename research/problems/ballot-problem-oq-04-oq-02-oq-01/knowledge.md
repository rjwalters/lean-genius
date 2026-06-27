# ballot-problem-oq-04-oq-02-oq-01 — Non-Crossing Partitions are Counted by Catalan

**Goal:** `nonCrossingCount n = catalan n`, where `nonCrossingCount n` (from
`ballot-problem-oq-04-oq-02`) is `Fintype.card {P : Finpartition (univ : Finset (Fin n)) // IsNonCrossingFp P}`.

This is **openQuestion[2]** of the sibling entry `ballot-problem-oq-04-oq-02`:
> "Establish the Catalan recurrence directly on the Finpartition model — decompose by the
> block containing the last index (or by first return) to obtain
> `nonCrossingCount (n+1) = ∑ nonCrossingCount i · nonCrossingCount (n−i)`, matching Mathlib's
> catalan recurrence without constructing the full bijection."

## Summary of state

The open counting statement has been **reduced to one combinatorial recurrence**. Everything
except that recurrence is proved with 0 sorry.

## Session 2026-06-26 (Session 1) — Structural reduction

**Mode:** FRESH
**Outcome:** progress (reduction + base case proved; recurrence isolated as 1 sorry)

### What I did
- Triaged the available pool. Found three Seeker "gallery-gap" candidates were already
  proved in the gallery/Mathlib (composite Wilson converse → `WilsonsTheoremOQ01`/`OQ05OQ01`;
  Basel π²/8 → `BaselProblemOQ09.lean:116`; X³−2 irreducibility →
  `AngleTrisectionOQ02OQ01OQ02.lean:128`) and that Jordan–Hölder for modules is already in
  Mathlib (`JordanHolderModule.instJordanHolderLattice`). Selected this candidate as the
  genuine, substantive gap building on the deepest existing infrastructure.
- Created `proofs/Proofs/BallotProblemOQ04OQ02OQ01.lean`:
  - `nonCrossingCount_zero : nonCrossingCount 0 = 1` (0 sorry).
  - `nonCrossingCount_recurrence` — STATED to match Mathlib's `catalan_succ'`
    (`∑ ij ∈ antidiagonal n, …`); body is the single outstanding `sorry`.
  - `nonCrossingCount_eq_catalan : nonCrossingCount n = catalan n` — proved by
    `Nat.strong_induction_on`, rewriting each antidiagonal factor by the IH (0 sorry beyond
    its dependence on the recurrence).
- Created the gallery entry data and research problem JSON.

### Key findings
- Mathlib's `catalan` is *defined* by the antidiagonal convolution, and `catalan_succ'`
  exposes it; so `nonCrossingCount = catalan` is a 4-line strong induction once the same
  recurrence is known for `nonCrossingCount`. The whole problem collapses to the recurrence.
- The recurrence must be proved combinatorially and independently (assuming the goal would be
  circular).
- Mathlib has **no** non-crossing partition theory and **no** Finpartition block-gap
  decomposition lemma — both would need to be built for the recurrence.

### Files modified
- `proofs/Proofs/BallotProblemOQ04OQ02OQ01.lean` (new, 1 sorry)
- `src/data/research/problems/ballot-problem-oq-04-oq-02-oq-01.json` (new)
- `src/data/proofs/ballot-problem-oq-04-oq-02-oq-01/` (new gallery entry)

### Next steps
- Prove `nonCrossingCount_recurrence` via the first-return block decomposition: in a
  non-crossing Finpartition of `Fin (n+1)`, the block of `0` splits the remaining indices into
  intervals each carrying an independent non-crossing partition; assemble the `Equiv` to
  `Σ ij ∈ antidiagonal n, (nc of Fin i) × (nc of Fin j)` and take `Fintype.card`.
- Or build the explicit Dyck↔partition bijection (sibling `ballot-problem-oq-04-oq-01`) and
  transport `DyckWord.card_dyckWord_semilength_eq_catalan`.
- Retry Aristotle on the recurrence sorry — the MCP endpoint returned "Resource not found"
  this session (service unavailable), so the async submission did not register.

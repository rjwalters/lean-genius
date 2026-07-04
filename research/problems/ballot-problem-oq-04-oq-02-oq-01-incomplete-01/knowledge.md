# Knowledge: Non-crossing partitions counted by Catalan — recurrence reduction (1 sorry)

**Problem id**: `ballot-problem-oq-04-oq-02-oq-01-incomplete-01`
**Gallery entry / Lean file**: `ballot-problem-oq-04-oq-02-oq-01` →
`proofs/Proofs/BallotProblemOQ04OQ02OQ01.lean`
**Goal**: discharge the single remaining `sorry`, `nonempty_firstReturnEquiv`.

## Summary

`BallotProblemOQ04OQ02OQ01.lean` reduces the conjecture `nonCrossingCount n = catalan n` (from the
Finpartition model in `BallotProblemOQ04OQ02.lean`) to **one** combinatorial fact and proves
everything else:

- `nonCrossingCount_zero : nonCrossingCount 0 = 1` — proved.
- `nonCrossingCount_recurrence_of_equiv` — the **counting half**: *given* a first-return bijection
  it derives the Catalan convolution
  `nonCrossingCount (n+1) = ∑_{(i,j)∈antidiagonal n} nonCrossingCount i * nonCrossingCount j`
  by pure cardinality arithmetic (`Fintype.card_congr ∘ card_sigma ∘ card_prod`). Proved, 0 sorry.
- `nonCrossingCount_eq_catalan` — strong induction against `catalan_succ'`. Proved (modulo the
  sorry, via `nonCrossingCount_recurrence`).
- `nonCrossingCount_eq_catalan_of_le_three` — **unconditional** for `n ≤ 3` (kernel `decide`).

The **sole open obligation** is the existence of the bijection

```
nonempty_firstReturnEquiv (n) :
  Nonempty ( {P : Finpartition (Fin (n+1)) // IsNonCrossingFp P}
             ≃ Σ (i,j) ∈ antidiagonal n,
                 {P : Finpartition (Fin i) // IsNonCrossingFp P}
               × {P : Finpartition (Fin j) // IsNonCrossingFp P} )
```

This is the classical "first-return" Catalan decomposition of a non-crossing partition of a
linearly ordered set. It is *known* mathematics; the difficulty is purely one of formalization,
because **Mathlib contains no theory of non-crossing partitions whatsoever**.

## Infrastructure assessment

**Needed**: a restriction operation taking a non-crossing `Finpartition (Fin (n+1))` and the block
of a distinguished point, and returning the induced non-crossing partitions on the two
sub-intervals it cuts out; plus the inverse gluing operation; plus proofs that both preserve
`IsNonCrossingFp` and are mutually inverse.

**Mathlib gaps** (confirmed by search of `packages/mathlib`):
- No `NonCrossing`/`noncrossing` partition API at all.
- No operation restricting a `Finpartition (Fin (n+1))` to a `Finset`/interval and re-indexing it
  as a `Finpartition (Fin i)`.
- The only Catalan *combinatorial model* in Mathlib is `treesOfNumNodesEq n : Finset (Tree Unit)`
  with `treesOfNumNodesEq_card_eq_catalan`. Transporting through it (non-crossing partitions ≃
  binary trees) is an **equal-difficulty** bijection, not a shortcut. Its recursion
  (`treesOfNumNodesEq_succ`, via `pairwiseNode` over `antidiagonal`) mirrors `catalan_succ'`, so the
  antidiagonal/first-return shape is the natural one to target directly.

**Size estimate**: several hundred lines (restriction + gluing + non-crossing preservation +
inverse laws). This is a genuine build, not a Mathlib-lookup. **Decision: BUILD (multi-session) or
delegate to Aristotle** — this is exactly the "known result, needs formalization" (HARD) regime.

## Decomposition strategy (concrete sub-lemmas for `nonempty_firstReturnEquiv`)

Rather than one monolithic equiv, split the obligation into independently-attemptable pieces:

1. **`restrict` (forward map, part 1).** From `P : Finpartition (Fin (n+1))` non-crossing, and the
   block structure around a distinguished point (e.g. the block of `0`, or the last point `n`),
   produce the pair `(i, j) ∈ antidiagonal n` (the sizes of the two sub-intervals) and the two
   induced partitions `Finpartition (Fin i)`, `Finpartition (Fin j)` obtained by re-indexing the
   restriction of `P` to each interval.
2. **NC-preservation (forward).** Prove each restricted/re-indexed partition still satisfies
   `IsNonCrossingFp`. This is where the non-crossing hypothesis is genuinely used: a crossing in a
   restriction would lift to a crossing in `P`.
3. **`glue` (inverse map).** Given `(i,j) ∈ antidiagonal n` and non-crossing partitions on `Fin i`
   and `Fin j`, reassemble a non-crossing `Finpartition (Fin (n+1))` (place the distinguished block,
   embed the two sub-partitions on the complementary intervals).
4. **NC-preservation (inverse).** The glued partition is non-crossing (the distinguished block does
   not cross either sub-block by construction; cross-interval indices are separated by the block).
5. **Inverse laws.** `restrict ∘ glue = id` and `glue ∘ restrict = id`, assembled into the `Equiv`,
   then `Nonempty.intro`.

Choosing the distinguished point as the block containing `0` (equivalently, the "first return")
makes the antidiagonal split canonical: `i` = size of the initial interval closed off by `0`'s
block, `j` = the remainder.

## Rejected approach — brute-force finite verification at n = 4

**Negative finding (saves future compute).** I attempted to add an unconditional
`nonCrossingCount 4 = 14 = catalan 4` — the first case beyond the trivial `n ≤ 3` coincidence and
the point where non-crossing partitions first become a *proper* subfamily (Bell 4 = 15 > 14). The
proof `unfold nonCrossingCount; decide` (with `maxRecDepth 100000`) **stack-overflows the Lean
kernel** during the guarded Docker build:

```
info: stderr: Stack overflow detected. Aborting.
error: Lean exited with code 134
```

Cause: the `Fintype (Finpartition (Fin 4))` instance is not kernel-reducible at `n ≥ 4`. This is
precisely why the sibling file proves only the *inequality* `nonCrossingCount_four_lt` via
`Fintype.card_subtype_lt` (needing a single crossing witness) rather than the exact value.

Consequences:
- Kernel `decide` is **not** a viable route to any exact `nonCrossingCount n` for `n ≥ 4`.
- An exact finite check would require `native_decide`, which pulls in `Lean.ofReduceBool` and would
  make an otherwise foundational-axiom-only entry `axiomatized` — not worth it for a lone data
  point, and orthogonal to the general theorem.
- The only satisfying route to `nonCrossing = Catalan` for all `n` is the structural bijection
  above.

## Session log

### Session 2026-07-03 (Session 1) — ORIENT

**Mode**: FRESH · **Outcome**: progress (ORIENT; no sorry closed)

**What I did**
- Read the Finpartition non-crossing model (`BallotProblemOQ04OQ02.lean`) and the reduction file
  (`BallotProblemOQ04OQ02OQ01.lean`); confirmed the counting half is done and the lone sorry is the
  first-return bijection.
- Attempted to delegate the HARD bijection to Aristotle (`prove`/`prove_file`, async) — service
  returned `Resource not found` (unavailable this session).
- Attempted an independent unconditional win `nonCrossingCount 4 = catalan 4` by kernel `decide`;
  guarded Docker build (8 GB, 25 min) → **kernel stack overflow**. Reverted; file left clean at 1
  sorry.
- Surveyed Mathlib: no non-crossing partition API; `treesOfNumNodesEq` is the only Catalan model
  and offers no shortcut.
- Wrote the sub-lemma decomposition of the bijection (restriction → NC-preservation → gluing →
  inverse laws) as the concrete plan for the next ACT session.

**Key findings**
- The exact difficulty is fully isolated: one bijection, all cardinality arithmetic discharged.
- Brute force is dead (kernel overflow at n=4); the structural bijection is the only path.
- Mathlib gap is real and sizeable (restriction/gluing of `Finpartition (Fin ·)` must be built).

**Files modified**
- `research/problems/ballot-problem-oq-04-oq-02-oq-01-incomplete-01/{knowledge.md,state.md}`
- (gallery Lean file unchanged — the n=4 `decide` experiment was reverted)

**Next steps**
- Implement sub-lemma 1 (`restrict`) + sub-lemma 2 (forward NC-preservation).
- Re-attempt Aristotle delegation of `nonempty_firstReturnEquiv` when the service is reachable.

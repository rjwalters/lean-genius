# Knowledge: Non-crossing partitions counted by Catalan — COMPLETE (0 sorry, verified)

**Problem id**: `ballot-problem-oq-04-oq-02-oq-01-incomplete-01`
**Gallery entry / Lean file**: `ballot-problem-oq-04-oq-02-oq-01` →
`proofs/Proofs/BallotProblemOQ04OQ02OQ01.lean`
**Status (2026-07-04, s15): DONE.** `nonCrossingCount n = catalan n` fully proved — 0 sorry,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` only. The last obligation
`nonempty_firstReturnEquiv` was discharged by an equinumerosity count (see s15 log below).

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

### Session 2026-07-04 (Session 15) — ACT: bijection packaged, theorem COMPLETE

**Mode**: REVISIT · **Outcome**: **DONE** — sole `sorry` discharged, 0 sorry, verified.

**What I did**
- Discharged `nonempty_firstReturnEquiv` (the last `sorry`) and thereby proved
  `nonCrossingCount n = catalan n` in full.
- Key move: instead of building a *natural* `Equiv` between the antidiagonal-indexed `Σ`-type and
  the non-crossing partitions — which needs dependent-`HEq` transport, because the forward map's cut
  index `firstBlockMax(glue) = m` holds only *propositionally* — I proved
  `card LHS = card RHS` and applied `Fintype.equivOfCardEq`.
- Route: an intermediate type `MidNc n := Σ m : Fin (n+1), NcFp m.val × NcFp (n - m.val)` whose right
  fiber `Fin (n - m)` matches `glueFp`'s argument type **definitionally** (no cast). Maps `fwdMid`
  (cut + restrict) and `glMid` (glue). `card LhsNc = card MidNc` by `le_antisymm` of two injections:
  `fwdMid` injective via its left inverse `glMid` (= `glueFp_restrictFp_eq_self`); `glMid` injective
  by recovering the cut as an **ℕ-equality** (`firstBlockMax_glueFp_val`, so `subst` dodges `HEq`)
  then both factors (`restrictFp_glueFp_left/right`). `card MidNc = card Rhs` by a pure
  `antidiagonal ↔ range` reindexing (`Fin.sum_univ_eq_sum_range` +
  `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`) — no partition casts at all.
- Docker build **clean on the first try** (7745 jobs, no SIGBUS despite swap at 98%). Axiom audit
  `#print axioms nonCrossingCount_eq_catalan` = `[propext, Classical.choice, Quot.sound]`.
- Updated gallery `meta.json` (status → verified, badge → verified, sorries 0, counts, sections,
  narrative) and the research tracking json (status → completed).

**Key findings**
- **Equinumerosity beats a natural Equiv** when the forward map's index is *computed* (only
  propositionally equal to the target). `Fintype.equivOfCardEq` needs no explicit inverse or
  `Sigma.ext`/`HEq`; the two `card ≤` directions are clean injectivity proofs.
- **Injectivity of `glMid` dodges `HEq`**: recover the index as `m.val = m'.val : ℕ` first, then
  `subst` (via `Fin.ext`) so the dependent fibers become defeq *before* comparing the factors.
  This is the crucial trick that made the packaging tractable without cast bookkeeping.
- **Definitional-proof-irrelevance carried the round-trips**: `glMid ∘ fwdMid` matched
  `glueFp_restrictFp_eq_self` up to the `≤` proof arguments with no massaging (`exact` sufficed).
- A build succeeded despite swap at 98% — the SIGBUS in prior sessions is transient, not
  deterministic at high swap.

**Files modified**
- `proofs/Proofs/BallotProblemOQ04OQ02OQ01.lean` (+~150 lines: `NcFp`/`MidNc`, `fwdMid`/`glMid`,
  `glMid_fwdMid`, `fwdMid_injective`, `glMid_injective`, `card_midNc_eq`, `card_rhs_eq`,
  `card_lhs_eq_card_rhs`; `nonempty_firstReturnEquiv` sorry → proof; docstrings/status; axiom check)
- `src/data/proofs/ballot-problem-oq-04-oq-02-oq-01/meta.json` (verified, 0 sorry)
- `src/data/research/problems/ballot-problem-oq-04-oq-02-oq-01.json` (completed)

**Next steps**
- None for this theorem. Optional: upstream the non-crossing restriction/gluing calculus to Mathlib;
  relate to the sibling Dyck-word bijection (`ballot-problem-oq-04-oq-01`).

### Session 2026-07-04 (Session 13) — ACT: right_inv factor recovery

**Mode**: REVISIT · **Outcome**: progress (2 new verified lemmas + 2 helpers, 0 new sorry)

**What I did**
- Proved `restrictFp_glueFp_left` / `restrictFp_glueFp_right`: restricting the glued partition
  `glueFp m hm P₁ P₂` to the left window `[1,m]` (resp. right `[m+1,n]`) returns `P₁` (resp. `P₂`)
  **exactly** — the *factor half* of the `right_inv` round-trip law.
- Added reusable helpers `finpartition_eq_of_part` (Finpartition extensionality via the block
  function) and `part_glueFp_eq_iff` (`part`-equality form of `mem_part_glueFp`).
- Docker build verified (SIGBUS-135 on first attempt, clean on retry): single expected sorry
  (`nonempty_firstReturnEquiv`), 0 new sorry.

**Key findings**
- `right_inv` (`forward ∘ glue = id`) **mathematical content is now complete**: cut index via
  `firstBlockMax_glueFp_val` (s12) + both factors via the new lemmas. Only `Equiv`/`Sigma`/`Subtype`
  packaging of `firstReturnForward` remains for `right_inv`.
- Factor recovery is **unconditional** (no non-crossing hypothesis): restriction of a glue is a pure
  `glueLabel` computation; each window carries the shifted `Pᵢ` labels verbatim; dropped `0` is
  outside both windows.
- Remaining genuine content is **`left_inv`** (`glue ∘ forward = id`); infrastructure ready
  (`restrict_top_recovers_part_zero`, `part_side_of_firstBlockMax`).

**Files modified**
- `proofs/Proofs/BallotProblemOQ04OQ02OQ01.lean` (+4 declarations, still 1 sorry)
- `src/data/research/problems/ballot-problem-oq-04-oq-02-oq-01.json`

**Next steps**
- Assemble the `Equiv` (`firstReturnForward` ↔ `glueFp`), discharge `right_inv`, then attack
  `left_inv`.

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

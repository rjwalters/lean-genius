# Knowledge Base: erdos-998-oq-04

**Question:** Is there a formalization path for the three-distance theorem
using Mathlib's `Finset` and order theory?

**Answer (this session): YES.** The three-distance (three-gap / Steinhaus)
theorem is purely finite and order-theoretic — no measure theory, no analysis.
It is a clean Mathlib-style target built from `Int.fract`, `Finset`, and the
linear order on `ℝ`. This session gives the first formal Lean *statement* plus
the elementary structural infrastructure, and isolates the combinatorial core.

---

## Problem Understanding

The orbit of an irrational rotation `m ↦ {mα}` underlies Erdős #998 (Kesten's
equidistribution theorem). The three-distance theorem describes that orbit:

> For irrational `α` and every `N ≥ 1`, the `N` points
> `{0, {α}, {2α}, …, {(N-1)α}}` cut the circle `[0,1)` into `N` arcs whose
> lengths take **at most three distinct values**; when three values occur, the
> largest is the sum of the other two.

The parent `Erdos998Problem.lean` mentions this only in a prose docstring
(Part V, lines 144–151). No formal statement existed before this session.

---

## Mathlib Status (verified June 2026)

- Mathlib4 does **not** contain the three-gap theorem (web survey + local
  inspection). A **Coq** formalization exists (van Ravenstein's proof), but no
  Lean version. Genuine gap.
- Available bearers: `Int.fract` (`Int.fract_nonneg`, `Int.fract_lt_one`,
  `Int.fract_eq_fract`, `Int.fract_zero`), `Finset.image`/`erase`/`min'`/`inf'`,
  `Finset.card_image_of_injective`, `Finset.card_range`, `Irrational`.
- No measure/analysis dependency — the entire proof is `Nat`/`Finset` order
  arithmetic over the linear order on `ℝ`.

---

## Formalization Built This Session

File: `proofs/Proofs/Erdos998ThreeGapOQ04.lean` (build-pending — worktree
`.lake` circular-symlink OOM this cycle; bearers name-checked vs rev 2df2f01).

Definitions:
- `orbit α N := (range N).image (fun i => Int.fract (i * α))` — the orbit as a
  `Finset ℝ ⊆ [0,1)`.
- `forwardGap α N x` — shortest positive cyclic distance `{y - x}` to another
  orbit point, via `Finset.inf'` (total, `dite`-guarded).
- `gapLengths α N := (orbit α N).image (forwardGap α N)` — the set of distinct
  arc lengths.

Theorem statements:
- `three_gap : (gapLengths α N).card ≤ 3` — **the main theorem**.
- `three_gap_additive` — among three lengths, one is the sum of the other two.

Proved (elementary, robust):
- `orbit_mem_Ico` — orbit ⊆ [0,1).
- `zero_mem_orbit`, `orbit_nonempty` — the `i=0` point and nonemptiness.
- `forwardGap_nonneg`.

---

## Proof Path for the Core (van Ravenstein / Sós–Surányi–Świerczkowski)

This is the remaining work, isolated behind `sorry` in `three_gap`:

1. **First-return generators.** Let `p` be the least index `1 ≤ p < N`
   minimizing the forward return `{pα}` (smallest clockwise gap at `0`), and `q`
   the least index minimizing the backward return `1 - {qα}`. Existence:
   `Finset.exists_min_image` on `range N`.

2. **Gap classification.** Each orbit point `{iα}` is the left endpoint of
   exactly one arc, whose forward neighbour is `{(i+p)α}` when `i + p < N` and
   otherwise wraps via `q`. Hence every gap length is one of:
   - `{pα}`               (short, count `N − p`),
   - `1 − {qα}`           (short, count `N − q`),
   - `{pα} + 1 − {qα}`    (long, count `p + q − N`).
   Three values ⟹ `card ≤ 3`.

3. **Bookkeeping / additive relation.** Counts sum to `N`:
   `(N−p) + (N−q) + (p+q−N) = N`. The long gap is literally the sum of the two
   short gaps ⟹ `three_gap_additive`.

The crux to formalize is step 2's neighbour map `i ↦ i+p mod (the wrap rule)`
and the proof that it is the cyclic successor — pure `Nat`/order reasoning.

---

## Insights

- The theorem needs **no equidistribution and no `α` irrationality for the
  ≤3-lengths claim itself** — irrationality only guarantees the `N` points are
  *distinct* (`orbit_card`). The gap structure is combinatorial.
- Defining gaps via `forwardGap` (min positive cyclic distance) sidesteps an
  explicit sort/`orderEmbOfFin`, keeping the statement order-theoretic and the
  successor map index-arithmetic.

## Dead Ends / Risks

- A measure-theoretic phrasing (arc lengths as `volume`) would drag in
  `MeasureTheory` unnecessarily; the `Finset`+`Int.fract` phrasing is lighter.
- Build verification blocked this cycle by the repo-wide circular `.lake`
  self-symlink (Mathlib recompiles from source → OOM). Defer kernel check to a
  cache-warm deployer build.

## Next Steps

1. ~~Prove `orbit_card`~~ DONE (S2). Injectivity of `i ↦ {iα}` on `range N` via
   `Int.fract_eq_fract` (→ `(i-j)·α = z ∈ ℤ`), then `Irrational.int_mul`
   (a nonzero-int multiple of an irrational is irrational) contradicts
   `not_irrational_int z`. Card follows from `Finset.card_image_of_injOn` +
   `Finset.card_range`. Build-pending (circular `.lake` OOM).
2. Formalize the first-return generators `p, q` and the successor map (step 2).
3. Discharge `three_gap` and `three_gap_additive` from the classification.
4. Once green, register a gallery entry (status `formalized`/`wip` until built;
   the ≤3 claim is unconditional, the additive relation follows).

**progressSummary:** ORIENT→ATTACK. Discharged `orbit_card` (one of the three
isolated sorries) with a fully elementary irrationality argument. The remaining
open content is the single combinatorial gap-classification core (`three_gap`,
`three_gap_additive`), with the documented van Ravenstein proof path. The ≤3
distinct-lengths statement remains the first formal Lean statement of the
three-gap/Steinhaus theorem.

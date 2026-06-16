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

---

## Session 2026-06-15 (Session 3) — Reduce both theorems to ONE core lemma

**Mode**: REVISIT (FRESH claim of available problem) — **Outcome**: progress

### What I Did
Collapsed the two open obligations (`three_gap`, `three_gap_additive`) so they
now depend on a **single** isolated combinatorial lemma, and proved all the
surrounding finite-cardinality scaffolding.

- Added `card_le_three_of_subset_triple : s ⊆ {a,b,c} → s.card ≤ 3` — pure
  `Finset` arithmetic (`card_insert_le`/`card_singleton`/`card_le_card` + omega).
  Fully proved, no sorry.
- Introduced the core lemma `exists_gap_triple`:
  `∃ a b c, a + b = c ∧ gapLengths α N ⊆ {a, b, c}`. This is the genuine
  Sós–Surányi / van Ravenstein content (the two short gaps `{pα}`, `1−{qα}`
  and the long gap `{pα}+(1−{qα})`), the SOLE remaining sorry.
- `three_gap` now: `obtain` the triple, apply the card engine. No sorry.
- `three_gap_additive` now fully derived from `exists_gap_triple`:
  `Finset.eq_of_subset_of_card_le` forces `gapLengths = {a,b,c}` when card = 3;
  pairwise distinctness comes from collapsing any pair to a ≤2-card set
  (contradiction with card = 3); membership from `gapLengths = {a,b,c}`.
  No sorry.

### Key Findings
- The whole theorem reduces to a **single set-containment statement** plus an
  additive equation — a clean, self-contained Aristotle/Docker target. The
  "≤ 3 distinct values" and "long = short + short" claims are NOT independent:
  both fall out of `gapLengths ⊆ {a,b,c} ∧ a+b=c`.
- Distinctness need not be hypothesized: given `card = 3` and a 3-element
  superset literal, equality of finsets is forced, and the three witnesses are
  automatically distinct.

### Files Modified
- `proofs/Proofs/Erdos998ThreeGapOQ04.lean` — added `card_le_three_of_subset_triple`,
  `exists_gap_triple` (sorry), rewrote `three_gap` and `three_gap_additive` (both
  now sorry-free, depending only on `exists_gap_triple`).

### Sorry Ledger
- Before: 2 sorries (`three_gap`, `three_gap_additive`), both HARD/combinatorial.
- After: **1 sorry** (`exists_gap_triple`), the isolated classification core.

### Next Steps
1. Prove `exists_gap_triple` — define generators `p, q` via
   `Finset.exists_min_image` on `range N`, then the successor/neighbour map.
   Ideal single-lemma Aristotle target once the backend recovers (404 today).
2. Build `Proofs.Erdos998ThreeGapOQ04` when Docker ≤ 2 containers to confirm the
   new scaffolding compiles (build-blocked this cycle: 5 lean-build containers,
   Aristotle 404).

**progressSummary:** ATTACK. Net sorry count 2 → 1. Both headline theorems are
now sorry-free, resting on one precisely-stated combinatorial core
(`exists_gap_triple`). Build-pending (dual-backend blackout).

---

## Session 2026-06-16 (Session 4) — researcher-11 — re-confirm frontier + metadata repair

**Mode**: REVISIT (claimed available problem) — **Outcome**: blocked (build-gated); metadata fixed

### What I Did
- Re-read `proofs/Proofs/Erdos998ThreeGapOQ04.lean` and confirmed the exact
  frontier: **252 LOC, 9 theorems, 0 axioms, exactly 1 `sorry`** —
  `exists_gap_triple` at line 183. `three_gap`, `three_gap_additive`, and
  `card_le_three_of_subset_triple` are all sorry-free and depend only on it;
  `orbit_card` is fully proved.
- Confirmed the file is **NOT registered** in `proofs/Proofs.lean` (so it is not
  in CI and the build status is genuinely unverified).
- **Probed both backends** at session start: Aristotle MCP `prove` → `404
  Resource not found`; `docker run --rm alpine echo` → hung (exit 124). Dual
  blackout. No Lean shipped (blind-writing the cyclic-successor index arithmetic
  of `exists_gap_triple` under blackout is unsafe and forbidden).
- **Fixed a metadata-propagation gap.** This problem had a rich `knowledge.md`
  but **no `meta.json`**, so `scripts/sync-research.sh` never produced
  `src/data/research/problems/erdos-998-oq-04.json`. Because `knowledge-scores.sh`
  reads only that `src/data` store, the problem was invisible to the knowledge
  prioritizer and scored 0 — it surfaced as an EMPTY `available` stub despite
  being a MODERATE/ATTACK problem with one isolated sorry. Authored a complete
  `meta.json` (knowledge score 11) and synced it to `src/data`.

### Key Findings
- The remaining `exists_gap_triple` is **KNOWN mathematics**
  (Sós–Surányi–Świerczkowski / van Ravenstein), hence a **HARD (not OPEN)
  sorry** — the correct tool is Aristotle `prove_file`, with manual fallback only
  for the index arithmetic of the cyclic-successor map.
- The pool record (`.lean/state/candidate-pool.json`, untracked) carried
  `status=available`, `phase=null`, `notes="AVAILABLE: AVAILABLE"` — also updated
  this cycle to reflect the true ATTACK/1-sorry state.

### Files Modified
- `research/problems/erdos-998-oq-04/meta.json` (new — propagates knowledge to prioritizer)
- `src/data/research/problems/erdos-998-oq-04.json` (new — sync of the above)
- `research/problems/erdos-998-oq-04/knowledge.md` (this log)
- `.lean/state/candidate-pool.json` (untracked — pool note/phase corrected, not in PR)

### Next Steps (unchanged frontier — turnkey on backend recovery)
1. Submit `exists_gap_triple` to Aristotle `prove_file` once non-404.
2. `docker-build Proofs.Erdos998ThreeGapOQ04` to verify the scaffolding compiles.
3. Register in `proofs/Proofs.lean` and add a gallery entry.

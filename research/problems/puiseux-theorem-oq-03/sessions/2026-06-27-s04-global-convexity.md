# 2026-06-27 — S04: Global convexity (sorted edge-slope sequence)

**Researcher**: researcher-6
**Branch**: `research/puiseux-oq03-chain-convexity`
**Mode**: ACT (extend the combinatorial Newton-polygon API)
**Outcome**: edge-slope sequence of a whole polygon proved sorted — 6 new
theorems + 2 defs added to `proofs/Proofs/PuiseuxTheoremOQ03.lean`
(0 sorries, 0 axioms; verified via `lake env lean`, `#print axioms` = only
propext/Classical.choice/Quot.sound).

## What I added

The file already had `edgeSlope_mono`: convexity for **two adjacent edges
sharing a vertex**. A Newton polygon is a *chain* of such edges; its defining
structural property is that **all** edge slopes are non-decreasing along the
chain. This session lifts the pairwise statement to the whole polygon.

* `edgeSlopes : List SupportPoint → List ℚ` — the edge-slope list of a chain of
  vertices (slope of each consecutive pair), clean two-step structural recursion.
* `chain_edgeSlopes` — **global convexity, chain form**: from
  `List.IsChain (IsLowerEdge pts) vs` derive `List.IsChain (· ≤ ·) (edgeSlopes vs)`.
  Structural induction; head step is `edgeSlope_mono`, tail is the IH.
* `edgeSlopes_pairwise_le` — **global convexity, sorted form**:
  `(edgeSlopes vs).Pairwise (· ≤ ·)` — every slope ≤ every *later* slope, not
  just the next. `IsChain → Pairwise` via `isChain_iff_pairwise` (≤ on ℚ is
  transitive).
* `rootValuations_pairwise_ge` — the negated slopes (root valuations) of the
  whole polygon are `Pairwise (· ≥ ·)`: the sorted valuation list the
  Newton–Puiseux recursion consumes one dominant edge at a time. Global
  analogue of the two-edge `rootValuation_antitone`.
* Worked three-vertex example `(0,2)→(1,0)→(3,1)`: a genuine convex chain
  (`threeVertex_chain`, both segments real lower edges), edge slopes `[-2, 1/2]`
  (`threeVertex_edgeSlopes`), shown sorted by the global theorem
  (`threeVertex_sorted`).

## Why this matters

`edgeSlope_mono` was the *local* convexity certificate. `edgeSlopes_pairwise_le`
is the *global* one: it is the precise statement that the lower hull is convex
and that a polynomial's root valuations form a fully sorted list — the backbone
of any Newton–Puiseux complexity argument, where the recursion peels off the
dominant (least-slope / largest-valuation) edge in order.

## Mathlib drift (important)

The local Mathlib cache has moved well past v4.26.0's List order API:
* `List.Chain'` → **`List.IsChain`** (`Chain'` is a deprecated alias).
* `List.Sorted` was **removed** (now `SortedLE`/`SortedGE` defined via
  `Monotone l.get`); use `List.Pairwise (· ≤ ·)` directly — that *is* sortedness.
* `chain'_cons`/`chain'_singleton`/`chain'_iff_pairwise` →
  `isChain_cons_cons`/`isChain_singleton`/`isChain_iff_pairwise`
  (`isChain_iff_pairwise` needs `[Trans R R R]`, found for `≤` on ℚ).
* Added imports `Mathlib.Data.List.Chain`, `Mathlib.Data.List.Sort`.

The pre-existing theorems were unaffected (they used `List.argmin`/`mem_filter`,
which are stable). Only the new convexity layer touched the changed API.

## Scope honesty

Incremental combinatorial infrastructure, not the open question. Still blocked,
unchanged from S03:
* Newton polygon theorem (slopes = root valuations): needs a valuation API on
  `K((x))[Y]`.
* S2-B termination measure; S2-C quasi-linear complexity (no arithmetic-cost
  model in Mathlib).

## Verification

`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean Proofs/PuiseuxTheoremOQ03.lean`
exits 0, no diagnostics. Docker host is back up but single-file `env lean`
against the prebuilt olean cache is the fast channel. `#print axioms` on all
four new theorems lists only the foundational axioms.

## Files modified

- `proofs/Proofs/PuiseuxTheoremOQ03.lean` (421 → 509 lines; +6 theorems, +2 defs,
  +2 imports)
- `src/data/proofs/puiseux-theorem-oq-03/meta.json` (counts, contributions,
  headline theorem, section, conclusion)
- this session note

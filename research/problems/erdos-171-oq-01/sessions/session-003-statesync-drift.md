# Session 003 — S3 STATE-SYNC (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-1
**Mode**: REVISIT (cold re-claim of COMPLETED slug)
**Iteration**: 2 → 3
**Phase**: COMPLETED (unchanged)
**Branch**: `research/erdos-171-oq-01-iter-1778921893`

## Triage

`claim-random` returned `erdos-171-oq-01` (knowledge score 8, MODERATE+ depth-first
tier, 1406 available). The slug is genuinely COMPLETED:

- `currentState.phase == "COMPLETED"`, `status == "completed"`
- `proofs/Proofs/Erdos171Problem.lean`: 0 sorries, 2 axioms
  (`isbell_coloring`, `de_grey_graph`) — both concrete combinatorial witness
  axioms (Isbell's hexagonal-tiling 7-coloring; de Grey's 1581-vertex
  5-chromatic graph). Reducing either is a substantial dedicated effort,
  not within a single research session.

No open PRs for `erdos-171` (`gh pr list --search "erdos-171 in:title state:open" == []`).
No recent (≤30 d) STATE-SYNC or ACT for this slug. Last update was
`2026-03-28T17:58:20.619Z` (~50 days ago). The pool re-surfacing this slug
appears to be a pool freshness artifact, not a request for new work.

## Drift Inventory

Audit of `src/data/research/problems/erdos-171-oq-01.json` against actual
Lean source (`proofs/Proofs/Erdos171Problem.lean` at HEAD
`b722658794d3513d2c1d1e4fb64be4be2b34b369`, Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` = v4.26.0):

| # | Field | JSON (stale) | Actual | Fix |
|---|-------|--------------|--------|-----|
| 1 | `knowledge.progressSummary` | "...0 sorries, 3 axioms" | 2 axioms | "...0 sorries, 2 axioms" |
| 2 | `leanFiles[0].lineCount` | 303 | 302 (`wc -l`) | 302 |
| 3 | `currentState.iteration` | 2 | post-session: 3 | 3 |
| 4 | `lastUpdate` | 2026-03-28T17:58:20.619Z | 2026-05-16 | new ISO timestamp |
| 5 | `currentState.focus` | mentions "axiomatized 2/0" (correct count) | same | clarify wording to flag axiom narrative drift fixed |
| 6 | `state.md` Iteration | "1" | post-session: 3 | 3 |

The `leanFiles[0].theoremCount` (7) and `axiomCount` (2) themselves are
correct — the drift is in the `progressSummary` *narrative* text only. The
parent gallery `src/data/proofs/erdos-171/meta.json` is also consistent
(`axiomCount: 2`, `lineCount: 302`, `theoremCount: 16` counting private
helpers, `definitionCount: 5`).

## Bearer Manifest (Mathlib v4.26.0, pin `2df2f0150c…`)

Spot-checked at `gh api /repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Module | SHA at pin |
|--------|-----------|
| `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` | `06812af7a3776c0624de123c8088c1dbddb62ba7` |
| `Mathlib/Data/Fin/Basic.lean` | `dd9dff38398c574990c1f00acf5837ca3d5f4557` |

Both APIs used by `Erdos171Problem.lean` are stable at pin. No build re-run
needed — Lean file is byte-identical to last verified state (last merged
edit `2ace1c84053c…`).

## Why No Lean Edit This Session

Per role doc ("Reducing axiom counts is more valuable than adding new theorems"),
the natural ACT here would be eliminating one of the two remaining axioms.
But:

1. **Isbell coloring** elimination requires formalizing the regular
   hexagonal tiling of ℝ² with side length s < 1/2 and a fixed 7-coloring
   pattern such that adjacent hexagons (distance ≤ 1 between any two
   points in different cells) get different colors. Realistic budget:
   200–500 LOC across tiling-geometry helpers + coloring witness +
   adjacency proofs. Out of scope for a single session.

2. **de Grey graph** elimination requires encoding a 1581-vertex graph
   (or the optimized 553-vertex Exoo–Ismailescu variant) with all unit
   distances verified and 4-coloring obstruction proved. Realistic
   budget: 1000+ LOC plus likely `native_decide` reaching its limit.
   Out of scope.

3. **Infrastructure risk**: `docker info` hangs at session start;
   `df -h /` reports 7.0 Gi avail / 70% used — below the 10 Gi safety
   threshold from prior researcher memory traps. Even a small Lean edit
   that requires Docker reverification is risky right now.

Honest call: ship doc-only STATE-SYNC closing the drift inventory; pre-stage
axiom-elimination recipes (below) for a future session with Docker capacity
and dedicated budget.

## Axiom-Elimination Recipes (Pre-Staged for Future ACT)

### Recipe A — Replace `isbell_coloring` with a constructive 7-coloring

**Goal**: replace
```lean
axiom isbell_coloring : ∃ c : EuclideanSpace ℝ (Fin 2) → Fin 7, IsProperColoring c
```
with
```lean
def isbellColoring : EuclideanSpace ℝ (Fin 2) → Fin 7 := ...
theorem isbell_coloring : ∃ c : EuclideanSpace ℝ (Fin 2) → Fin 7, IsProperColoring c :=
  ⟨isbellColoring, isbellColoring_proper⟩
```

**Sketch (Stechkin / Croft variant — simpler than original Isbell)**:

- Tile ℝ² with regular hexagons of side `s` where `1/2 < s < (√3)/3 ≈ 0.577`.
  Diameter = `2s < 2·(√3)/3 ≈ 1.155`, but the minimum *between-center*
  distance for non-adjacent hexagons is `s√3 > 1`. Hence two points within
  distance 1 can be either:
  (a) in the same hexagon (diameter < 2·(√3)/3, but we need < 1 for
  same-color safety) — need `2s < 1` actually for the cleanest argument; or
  (b) in adjacent hexagons.

  Stechkin variant: use 7 colors arranged so that the cluster of 7 hexagons
  centered at the origin (1 center + 6 neighbors) all get distinct colors,
  and the pattern repeats periodically with translation vectors
  `v₁ = (3s, 0)`, `v₂ = (3s/2, (5s√3)/2)`.

- Concretely: choose `s = 0.4` (so diameter `0.8 < 1`, between-cluster
  separation `3s = 1.2 > 1`). Color hexagon at position `(p, q)` (integer
  lattice coords in the hexagonal frame) with `(p + 2q) mod 7`. Verify:
  any two points at distance 1 either share a hexagon (same color OK
  because diameter 0.8 < 1 means dist=1 impossible) or are in hexagons
  whose lattice positions differ by a small set of vectors, all of which
  give distinct `(p + 2q) mod 7` mod-classes.

- **LOC budget**: ~250–400 (helper: hexagon membership predicate;
  hexagonal-lattice integer coordinates; `dist ≤ 0.8` within hexagon;
  `(p + 2q) mod 7` injectivity over the "within distance 1" cluster).

- **Mathlib bearers needed**:
  - `Mathlib.Analysis.InnerProductSpace.EuclideanDist` (Euclidean distance)
  - `Mathlib.Data.Real.Sqrt` (`Real.sqrt 3`)
  - `Mathlib.Data.ZMod.Basic` (`ZMod 7` for the coloring image; or use
    `Fin 7` directly and `Nat.mod` arithmetic)
  - `Mathlib.Analysis.Normed.Group.Basic` (norm bounds)

- **Risk classes**:
  - K (notation): `EuclideanSpace ℝ (Fin 2)` vs `ℝ × ℝ` — keep using
    `EuclideanSpace` for consistency with existing file
  - L (Mathlib API): hexagonal-lattice helpers likely absent at v4.26.0;
    need to define ourselves (small overhead)
  - M (heartbeats): the 7-way case analysis on `(p + 2q) mod 7`
    differences likely needs `decide` or careful `Fin.cases` — set
    `maxHeartbeats 800000` if needed

### Recipe B — Weaken `de_grey_graph` to a small-finite-graph axiom

**Goal**: reduce the `< 2000` bound to something concretely encoded.

**Sketch**: Exoo–Ismailescu (2020) gave a 553-vertex variant. A practical
intermediate: state the axiom as "there exists an explicit finite set
`V : Finset (EuclideanSpace ℝ (Fin 2))` with `V.card = 553` (or `< 600`)
that is not 4-colorable", and stub the witness as a separate `def`
populated later (perhaps via Aristotle or external SAT-style verification).

**Realistic estimate**: not eliminable in pure Lean without externally
sourcing the 553 coordinate pairs (which involves √(11/3) and similar
algebraic numbers). This is a 1000+ LOC effort across coordinate
encoding, distance-1 incidence list, and non-4-colorability witness
(`native_decide` on a Fin-553 graph may itself hit elaboration limits).

**Lower-effort intermediate**: introduce a structure
```lean
structure SmallFiveChromaticGraph where
  V : Finset (EuclideanSpace ℝ (Fin 2))
  card_lt : V.card < 2000
  not_4_colorable : ∀ c : V → Fin 4, ∃ x y : V, dist x.val y.val = 1 ∧ c x = c y
axiom de_grey_graph_struct : SmallFiveChromaticGraph
def de_grey_graph := ⟨de_grey_graph_struct.V, de_grey_graph_struct.card_lt,
  de_grey_graph_struct.not_4_colorable⟩
```
This doesn't reduce axiom count (still 1 axiom for the witness) but
*does* structure-encode the assumption for later refinement. Per project
"Axiom Integrity Policy", this is a re-architecture not a reduction —
the assumption count is unchanged.

### Recipe C — Small additive helper: `proper_coloring_mono`

Pre-staged paste-ready Lean (NOT shipped this session, deferred to next
ACT with Docker capacity):

```lean
/-- If a proper k-coloring exists, then for any k' ≥ k, a proper
    k'-coloring also exists (just lift via `Fin.castLE`). -/
theorem proper_coloring_mono (k k' : ℕ) (hle : k ≤ k')
    (h : ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k, IsProperColoring c) :
    ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k', IsProperColoring c := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun x => Fin.castLE hle (c x), fun x y hdist heq => ?_⟩
  exact hc x y hdist (Fin.castLE_injective hle heq)
```

Value: small (~7 LOC), no Mathlib gap, useful for connecting to
`SimpleGraph.chromaticNumber` (which uses `ℕ∞` and a different formalism).
Risk: `Fin.castLE_injective` name at v4.26.0 needs verification (likely
exists; if not, use `Fin.ext` + `Fin.coe_castLE`).

### Recipe D — Add Aristotle companion file `Erdos171Aristotle.lean`

Targets for Aristotle (per project SORRY-CLASSIFICATION rules — no
axioms, no `def` sorries, no main conjecture):

```lean
import Mathlib
namespace Erdos171Aristotle

-- TRIVIAL: monotonicity of proper colorings in k
theorem proper_coloring_mono (k k' : ℕ) (hle : k ≤ k')
    (h : ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k,
      ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 1 → c x ≠ c y) :
    ∃ c : EuclideanSpace ℝ (Fin 2) → Fin k',
      ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 1 → c x ≠ c y := by sorry

-- TRIVIAL: equilateral triangle gives 3-clique (already proved in main file)
-- Skip — duplicating already-proved theorems is busywork.

end Erdos171Aristotle
```

Estimated impact: 1 routine sorry, Aristotle very likely to solve.
Deferred to next session (Docker capacity needed for build verify).

## ACT-Readiness Gate for S4 (Recipe A — preferred)

| Gate | Status |
|------|--------|
| Slug COMPLETED but axiom-reduction tractable? | GREEN (Recipe A is a clean construction) |
| Docker daemon healthy? | RED (currently `docker info` hangs) |
| Disk avail ≥ 10 Gi? | RED (7.0 Gi at session start) |
| Mathlib pin stable? | GREEN (v4.26.0, bearer spot-checks pass) |
| Recipe A LOC budget within session? | AMBER (250–400 LOC borderline) |
| Aristotle companion file precedent? | GREEN (Recipe D is straightforward) |
| Cross-slug regression risk? | GREEN (file is leaf, no upstream dependents) |
| Originality framing honest? | GREEN (Stechkin variant of Isbell, classical) |

Overall: 5 GREEN / 1 AMBER / 2 RED (infrastructure-only). Next session
should re-probe Docker + disk before attempting ACT.

## Files Touched This Session

- `src/data/research/problems/erdos-171-oq-01.json` (drift fix: 5 fields)
- `research/problems/erdos-171-oq-01/state.md` (iteration bump, history)
- `research/problems/erdos-171-oq-01/sessions/session-003-statesync-drift.md` (this memo)
- NO Lean file edits
- NO `meta.json` edits
- NO Docker invocations

## Handoff

Next researcher claiming this slug after a fresh Docker daemon + disk
recovery: pick Recipe A (constructive Isbell coloring) or Recipe D
(Aristotle companion file). Recipe D is the lower-risk first step; if
Aristotle solves the `proper_coloring_mono` lemma, that's a useful
infrastructure addition with zero new axioms.

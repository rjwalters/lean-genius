# Current State

**Phase**: AXIOMATIZED (Lean formalization complete; Erdős problem remains open)
**Since**: 2026-03-13 (last knowledge update); seeker-init stub left behind
**Iteration**: 3

## Current Focus

State synchronization (doc-only). Gallery
`src/data/proofs/erdos-705/meta.json` has carried
`status: "axiomatized"`, `badge: "axiom"`, `sorries: 0`,
`erdosProblemStatus: "open"` since the early 2026 build-out, and the JSON
record's `knowledge.progressSummary` reads `"COMPLETE: 3 axioms (all deep
geometric constructions), 10 theorems proved, 0 sorries. Formalization is
clean for an open problem."`. The markdown `state.md` had been left in
the seeker-init `Phase: NEW since 2026-01-14` stub. This update
reconciles the markdown.

Note: `currentState.focus` in the JSON also references "6 remaining
axioms" — this was the early-iteration count. Two of those (`chromaticNumber'`,
`girth'`) were replaced with Mathlib's `SimpleGraph.chromaticNumber` and
`SimpleGraph.girth` (per `knowledge.builtItems[0..1]`); the four geometric
axioms then collapsed to three (Chilakamarri's 47-vertex graph was dropped
from the axiom list, kept as a docstring note since O'Donnell's 56-vertex
graph already witnesses χ = 4 at girth ≥ 4). Actual current `^axiom\s`
count: **3**.

## Verified Status — Per-File Inventory

| File                      | Lines | Theorems | Defs | Axioms | Sorries |
|---------------------------|-------|----------|------|--------|---------|
| Erdos705Problem.lean      |  362  |    10    |   8  |  **3** |    0    |

Sorry count confirmed via refined regex
`grep -cE "^[[:space:]]*sorry[[:space:]]*$|:= sorry$|:= by sorry$"`.
Axiom count confirmed via `grep -cE "^axiom\s"`.

## Axiom Inventory

All three remaining axioms are deep existence claims for concrete
geometric constructions — each is a published, verified result, but
formalizing them requires building the explicit point set in `ℝ²` and
verifying the chromatic number and girth, which is beyond the current
scope.

1. **`moser_spindle_exists`** (line 121) — Moser (1961): 7 vertices, girth 3,
   χ = 4. Smallest known 4-chromatic unit-distance graph.
2. **`odonnell_graph_exists`** (line 131) — O'Donnell (1994): 56 vertices,
   girth ≥ 4, χ = 4. Triangle-free 4-chromatic UDG.
3. **`wormald_graph_exists`** (line 142) — Wormald (1979): 6448 vertices,
   girth ≥ 5, χ = 4. The strongest known construction below girth 6.

Chilakamarri (1995, 47-vertex girth-4 4-chromatic UDG) is mentioned in
the comments but not used as an axiom because O'Donnell's construction
already establishes the girth-4 lower bound that `threshold_ge_6` needs.

## Main Theorems

1. **`girth_3_chi_4`**, **`girth_4_chi_4`**, **`girth_5_chi_4`** — direct
   destructors of the three axioms, exposing them as named theorems.
2. **`threshold_ge_6`** — from `wormald_graph_exists`: any `k` satisfying
   the Erdős conjecture must be `≥ 6`. The headline lower bound.
3. **`conjecture_implies_not_negation`** /
   **`negation_implies_not_conjecture`** — formal mutual-exclusion of the
   `erdos_705_conjecture` / `erdos_705_negation` formulations.
4. **`erdos_705_conjecture_lower`** — packaged statement: if the
   conjecture holds, any witness `k` is `≥ 6`.
5. **`isKColorable_mono`** / **`hasGirthAtLeast_mono`** — monotonicity
   lemmas used to chain the construction lower bounds.
6. **`erdos_705_main`** (line 331) — the public-facing statement: the
   conjecture is a well-formed proposition whose status is currently
   open.

## Blockers

None at the formalization level. Mathematical resolution is **open**:
no 4-chromatic unit-distance graph with girth ≥ 6 is currently known,
and no proof that none exists. Vertex-count growth (7 → 47 → 6448 for
girth 3, 4, 5) suggests further constructions may be intractable.

## Forward Levers (Optional, Beyond Current Scope)

- **Discharge `moser_spindle_exists` constructively**: enumerate the 7
  Moser-spindle points in `ℝ²`, verify 11 unit-distance edges via
  `decide`, and exhibit a 4-coloring + show no 3-coloring exists. This
  is the only one of the three axioms small enough for a full
  certificate-style discharge.
- **Hadwiger–Nelson link**: add a separate gallery slug for
  `5 ≤ χ(ℝ²) ≤ 7` and cross-reference; the current file mentions de Grey
  (2018) and the hexagonal-tiling upper bound only in docstrings.
- **Strengthen `threshold_ge_6`** to `threshold_ge_(g+1)` parametric in
  any future girth-`g` 4-chromatic construction. The current proof
  hard-codes `wormald_graph_exists`; a parametric lemma would
  generalize.

## Honesty Block

- Gallery meta: `status: "axiomatized"`, `badge: "axiom"`,
  `axiomCount: 3` in JSON `leanFiles` matches Lean source.
- Per CLAUDE.md axiom-integrity policy, this problem is correctly
  marked `axiomatized` (not `verified`). The three axioms encode
  published-but-not-yet-formalized constructions, not unproven
  assumptions, but the policy requires the `axiomatized` status for any
  `axiom` declaration regardless of mathematical confidence.
- This PR touches `state.md` only. No `.lean`, `meta.json`,
  `annotations.json`, `knowledge.md`, or `index.ts` edits.

## Attempt Counts

- Total attempts: 3 (per JSON `currentState.iteration`)
- Approaches tried: 1 (axiomatize geometric constructions, prove
  threshold lower bound from Wormald)

# State: brouwer-fixed-point-oq-02-oq-01

**Title**: PPAD Formalization: Higher-Dimensional Sperner Extension (2D Sperner's Lemma + Approximate Fixed Points)
**Phase**: COMPLETED
**Last-sync**: 2026-05-13 (researcher-11 STATE-SYNC)
**Snapshot-of**: `origin/main` at branch creation time

## Goal (stated)

Bridge 2D Sperner's lemma (combinatorial) to the approximate-fixed-point theorem (analytic) on the unit triangle, via a door-counting (row-sweep parity) argument. Establish the PPAD-complexity sub-problem for higher-dimensional Brouwer formalization.

## Goal (achieved)

Both halves discharged in `proofs/Proofs/BrouwerFixedPointOQ02OQ01.lean` (1071 lines, 0 sorries, 0 axioms, builds against Mathlib v4.26.0):

- `sperner_2d` (line 637): for any `n > 0` and any Sperner-coloring of the grid triangulation, the count of fully-colored triangles is odd (hence ≥ 1).
- `approximate_fixed_point_2d` (line 922): for any continuous self-map `f` of the 2-simplex and any ε > 0, there exists a point `p` with `dist(p, f(p)) < ε`.

Gallery `meta.json` already records `status: verified`, `badge: original`, `sorries: 0`, `axiomCount: 0`. The drift between gallery (correct) and research-JSON (stale `phase: ACT`, `status: in-progress`, two non-empty `blockers`, stale `nextAction`/`focus`) is what this STATE-SYNC PR closes.

## File map (snapshot from origin/main)

| File | Lines | Sorries | Axioms | Notes |
|------|-------|---------|--------|-------|
| `proofs/Proofs/BrouwerFixedPointOQ02OQ01.lean` | 1071 | 0 | 0 | Top-level: 6 theorems, 15 def/structure/inductive |

### Top-level theorems (in build order)

| # | Theorem | Line | Role |
|---|---------|------|------|
| 1 | `bottom_transitions_odd` | 184 | 1D Sperner: parity of `{0,1}`-transitions on the bottom edge is odd. |
| 2 | `hTrans_top` | 247 | Top-row `{0,1}`-door count = 0 (no `{0,1}` colors on the hypotenuse). |
| 3 | `fully_colored_one_door` | 263 | Fully-colored triangles have exactly one `{0,1}`-door (injectivity + surjectivity on `Fin 3`). |
| 4 | `abstractDoorCount_parity` | 346 | 27-case `decide`/`fin_cases`: non-FC triangles have an even `{0,1}`-door count. |
| 5 | `sperner_2d` | 637 | Main combinatorial theorem (door-counting via row-sweep parity). |
| 6 | `approximate_fixed_point_2d` | 922 | Analytic corollary: `displacementColoring` + uniform continuity. |

### Key definitions

`GridVertex`, `GridTriangle`, `TriType`, `lowerVertices`, `upperVertices`, `GridTriangle.vertices`, `Coloring`, `IsSperner`, `IsFullyColored`, `botVertex`, `bottomTransitions`, `gColor`, `hTrans`, `abstractDoorCount`, `IsDoor`, plus the `displacementColoring` machinery used in §V.

## Resolved blockers (now stale in research-JSON, cleared by this sync)

The research-JSON `currentState.blockers` array previously listed two items that have been resolved by prior sessions:

1. **"gColor/hTrans/abstractDoorCount definitions missing from file"** — restored from git history (per `knowledge.insights` line "Restored missing definitions (gColor, hTrans, hTrans_top, gColor_bot, abstractDoorCount) from git history"). The definitions are present at lines 234, 242, 247, 251 respectively.
2. **"15+ omega failures from Lean 4.26 Mathlib compat"** — fixed by `show`/`dsimp` projections through `GridVertex`, deprecated-rename updates (`range_succ` → `range_add_one`, `notMem_range_self`, `natCast_eq_zero_iff`), and `door_parity_of_not_fc decide → contradiction` substitutions (also per `knowledge.insights`).

The file now builds clean (per `meta.json.meta.assumptions`: "All 33 theorems verified with 0 sorries and 0 axioms").

## Sibling-slug scope (not within this slug)

| Sibling | Status |
|---------|--------|
| `brouwer-fixed-point-oq-02` (parent) | 0 sorries / 0 axioms in `BrouwerFixedPointOQ02.lean` (392 lines, 9 theorems). |
| `brouwer-fixed-point-oq-02-oq-02` | 0 sorries / 0 axioms in 269 lines / 15 theorems. |
| `brouwer-fixed-point-oq-02-oq-03` | 1 sorry remains in 215 lines / 5 theorems — separate slug. |
| `brouwer-fixed-point-oq-04` family (3 sub-slugs) | Mixed; this slug does not depend on or block them. |

Any further extension to higher-dimensional Sperner (`Fin (d+1)` instead of `Fin 3`, abstract simplicial complexes, …) belongs in a sibling open-question slug (likely a fresh `brouwer-fixed-point-oq-02-oq-01-oq-XX` if/when one is opened by Seeker).

## Forward levers (orthogonal to this slug)

Listed only as orientation for downstream sibling work; **not** in scope for this slug:

1. **Higher-dimensional generalization** — port `sperner_2d` to `sperner_d` for `d ≥ 3`. Requires generalizing `GridTriangle`/`TriType` to `d`-simplices and the row-sweep argument to a single induction on dimension. (Probably a fresh OQ.)
2. **PPAD reduction (Chen-Deng 2009)** — formalize the polynomial-time reduction from `END-OF-LINE` to `2D-SPERNER`. Requires a notion of computational reduction in Lean which Mathlib lacks; deferred.
3. **Brouwer from Sperner without uniform-continuity scaffolding** — the current `approximate_fixed_point_2d` uses `UniformContinuousOn`. Tightening to plain `Continuous` on a compact set is a routine refactor but not required.

## Honesty block

- All counts in the "File map" table verified at HEAD of `origin/main` (commit `4a4a3fbf09c`).
- Gallery `meta.json` `theoremCount: 33` differs from my top-level grep count of 6. This is a different counting convention (gallery counts every named proof obligation including `have :=`/`show` named blocks and section-local lemmas), not a discrepancy in the verified-status claim. Both counts agree on `sorries: 0`, `axiomCount: 0`.
- Research-JSON `leanFiles[8].lineCount: 1072` is off-by-one from `wc -l` (1071) and `meta.json.lineCount: 1071`; left untouched in this PR (mechanic territory, not state-sync).
- `knowledge.nextSteps` items reference work on Section V that is already discharged (Lean file has 0 sorries). They are preserved in `knowledge.insights` as historical context but cleared from `nextSteps`.
- No Lean files touched. No `meta.json` touched. No `annotations.json` touched. JSON-only research-state sync + new state.md file.

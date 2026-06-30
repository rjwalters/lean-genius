# Current State

**Phase**: ACT (build repair + S8/S9 lemmas landed)
**Since**: 2026-06-25T13:30:00Z (S7 ACT shipped 2026-06-25; baseline iteration tracking carried over from S1 OBSERVE on 2026-01-13)
**Iteration**: 7

## Current Focus

S7 ACT (researcher-4) **repaired a broken build**: the `origin/main` file no longer compiled against its *own* pinned Mathlib v4.26.0 due to API drift (`Set.ncard_Icc`, `div_le_div_right`, `div_lt_iff` removed; `Tendsto.congr'` arg order changed). Fixed all four and landed S8 (`density_additive_zero_singleton`) + S9 (`Sumset_singleton_left`/`_right`) from the S6 roadmap, plus two strict-bound corollaries. Remaining roadmap item — the Schnirelmann↔asymptotic bridge — is still open.

## Lean File Snapshot (HEAD = research/erdos-335-oq-01-build-repair)

- `proofs/Proofs/Erdos335Problem.lean`: 414 LOC, **40 theorems/lemmas**, 8 defs, **0 sorries**, **3 axioms**. Compiles clean (0 errors / 0 warnings) against pinned Mathlib v4.26.0 via `lake env lean`.
- Axioms (all deep / mathematically necessary):
  1. `weyl_equidistribution` — Weyl's equidistribution theorem (ABSENT from Mathlib at pinned SHA).
  2. `fractional_part_density_additive` — measure-theoretic transfer (ABSENT from Mathlib).
  3. `erdos_335_conjecture` — the OPEN problem itself (cannot be discharged).

## Merged Predecessor Sessions

| PR | Date | Contribution |
|----|------|-------------|
| #1254 | 2026-01-26 | initial gallery enrichment |
| #2244 | (early) | fix /-! docstring headers |
| #5294 | 2026-03-23 | prove density_nonneg + density_le_one + additive_sum_le_one (7→4 axioms) |
| #5405 | 2026-03-24 | add 4 derived theorems (0 sorries, 4 axioms) |
| #7253 | (early) | axiom elimination batch (10 slugs) |
| #7874 | 2026-03-29 | 12 structural theorems for density additivity |
| #8043 | (early) | prove 8 theorems, eliminate 1 sorry across 4 files |
| #8546 | 2026-03-30 | restore formal axiom declarations (4→3 axioms; unused `plunnecke_ruzsa_lower` removed) |
| #16253 | 2026-05-06 | add `density_univ_one` + `density_finite_zero` (concrete density computations) |

## Open / Active Sub-Goals (post-S6 PREP)

1. **S7 — Schnirelmann↔asymptotic bridge** (ACT): prove `schnirelmannDensity A ≤ asympDensity A` when `DensityExists A`, importing `Mathlib.Combinatorics.Schnirelmann`. ~40–80 LOC.
2. **S8 — Concrete witness `DensityAdditive {0} A`** (ACT): ~10–20 LOC, no new imports, uses only existing theorems in the file.
3. **S9 — Translation identity `Sumset {k} A = (·+k) '' A`** (ACT): ~10–20 LOC, no new imports.

See `sessions/2026-05-13-s06-prep-mathlib-bearer-audit-and-subgoal-roadmap.md` for bearer plans.

## Blockers

- **`weyl_equidistribution`** cannot be discharged at this Mathlib SHA. Needs upstream contribution.
- **`fractional_part_density_additive`** chains on Weyl + density-version Plünnecke–Ruzsa (Mann's theorem); also absent from Mathlib.
- **`erdos_335_conjecture`** is the open problem itself — not a blocker, just the goal.

## Non-Goals

- Do **not** attempt to remove any of the 3 axioms in a single session.
- Do **not** add a `plunnecke_ruzsa_lower` axiom (removed in PR #8546 as unused — re-adding violates axiom integrity policy unless an actual theorem cites it).

## Files of Interest

- `proofs/Proofs/Erdos335Problem.lean` — the 363-line formalization.
- `research/problems/erdos-335/knowledge.md` — session log.
- `src/data/research/problems/erdos-335.json` — authoritative state record (the source of truth; `state.md` and `knowledge.md` are mirrors).

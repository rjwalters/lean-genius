# Current State

**Phase**: PREP (Mathlib bearer audit + sub-goal roadmap)
**Since**: 2026-05-13T11:00:00Z (S6 PREP shipped 2026-05-13; baseline iteration tracking carried over from S1 OBSERVE on 2026-01-13)
**Iteration**: 6

## Current Focus

S6 PREP (doc-only) ships a Mathlib bearer audit at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and pins three forward sub-goals for the next researcher: (S7) Schnirelmann↔asymptotic density bridge lemma, (S8) `DensityAdditive {0} A` concrete witness, (S9) `Sumset_singleton_left` translate identity.

## Lean File Snapshot (HEAD = main 5fec075d743)

- `proofs/Proofs/Erdos335Problem.lean`: 363 LOC, **32 theorems/lemmas**, 8 defs, **0 sorries**, **3 axioms**.
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

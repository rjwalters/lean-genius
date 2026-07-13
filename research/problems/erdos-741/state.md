# Current State

**Phase**: ORIENT
**Since**: 2026-05-16T08:54:09Z
**Iteration**: 2

## Current Focus

Structural framework for both parts of Burr–Erdős #741 (density
splitting + non-splittable basis) is COMPLETE in
`proofs/Proofs/Erdos741Problem.lean`: 27 proved theorems, 8 defs,
0 axioms, 0 sorries (337 lines).

Built so far (across both pre-import branch sessions and this
state-sync):
- sumset algebra (10 lemmas): comm, mono, identity, union containment
- partition theory (3): trivial / complement / membership
- syndetic theory (5): ℕ syndetic, empty not, nonempty, mono, infinite
- density theory (4): empty=0, univ=1, mono, ≤1
- `cofinite_density_one` — proved (PR #16461, axiom→theorem)
- basis bridge (2): `basis_infinite`, `basis_has_pos_density_sumset`
- Part 1 ↔ Part 2 tension (2): `part2_gives_non_syndetic`,
  `part2_contradicts_part1_for_basis`

Both main conjectures (`ErdosProblem741_density`,
`ErdosProblem741_basis`) remain `Prop` definitions — OPEN per
erdosproblems.com.

## Active Approach

ORIENT phase: structural framework complete; the two unproved framework
gap-fillers (`density_finite` and `syndetic_has_pos_density`) are the
natural next bites before attacking the OPEN conjectures themselves.

## Blockers

None at the framework level. The OPEN conjectures (Part 1, Part 2) are
genuine Erdős open problems; not blockers for incremental progress.

## Next Action

S3 PREP/ACT: prove `density_finite` (~10 LOC, routine — bound
`ncard (A ∩ Iic n) ≤ |A|` then `K/(n+1) → 0`) and/or
`syndetic_has_pos_density` (~25 LOC, window-counting + limsup chain
mirroring `cofinite_density_one`). See
`sessions/2026-05-16-s2-statesync-research-json-leanfile-drift.md`
§"Next-action recipes" for paste-ready sketches.

## Attempt Counts

- Total attempts: 1 (initial structural build pre-import + axiom
  eliminations; this STATE-SYNC counts as the closing accountability
  pass on that attempt)
- Current approach attempts: 1
- Approaches tried: 1 (build full structural infra around OPEN cores)

## Iteration History

| Iter | Date | Phase | Outcome |
|---|---|---|---|
| 1 | pre-2026-03-13 | OBSERVE→ORIENT | Pre-import: created file with 27 theorems / 8 defs / 0 sorries; eliminated 4 axioms (7→3 in early work, then 3→0 via `cofinite_density_one` in PR #16461 / `c4e78e5f84a`). Squashed import = `2ace1c84053`. |
| 2 | 2026-05-16 | ORIENT (sync) | This STATE-SYNC: research-JSON + state.md + knowledge.md catchup post-batch-import (doc-only). No Lean delta. |

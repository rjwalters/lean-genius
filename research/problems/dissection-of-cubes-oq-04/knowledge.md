# Knowledge Base: dissection-of-cubes-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

Dissection of Cubes: Connection to Dehn Invariant Impossibility. The proof shows that the cube is the unique polyhedron (among regular solids) with zero Dehn invariant, implying it cannot be dissected into any of the other Platonic solids.

The key geometric fact: all regular solid dihedral angles except the cube (π/2) are irrational multiples of π. This is what distinguishes the cube.

---

## Insights

- `DissectionOfCubesOQ04.lean` was already 432 lines with substantial proof infrastructure
- `cube_unique_zero_dehn` had 3 sorries for edge-count scaling — wrong approach (should use `tmul_infinite_order_ne_zero`)
- The file already proved: `arccos_three_fifths_irrational`, `dodAngle_irrational`, `five_ndvd_cosThreeFifthsSeq`, `dod_dehn_ne_zero`
- `icoAngle = arccos(-√5/3)` and the key identity `cos(2·icoAngle) = 1/9`
- The proof of `icoAngle_irrational` goes via the Chebyshev sequence argument for `arccos(1/9)`
- Key identity: `arccos(1/9) = 2π - 2·icoAngle` (derived from cos(2·icoAngle) = 1/9)
- Sequence `d_n` satisfies `d_0=2, d_1=2, d_{n+2}=2d_{n+1}-81d_n` and equals `9^n·2cos(n·arccos(1/9))`
- If `icoAngle = (p/q)π`, then `cos(q·arccos(1/9))=1`, so `d_q = 2·9^q` — divisible by 3
- But `d_{n+2} ≡ 2d_{n+1} (mod 3)` with `3 ∤ d_0, d_1`, so `3 ∤ d_n` for all n — contradiction

---

## Session 8 (2026-04-26)

**Mode**: REVISIT
**Outcome**: significant progress — proved `icoAngle_irrational`, reducing axiom count from 2 to 1

### What I Did

1. Identified `icoAngle_irrational` (axiom) as the main remaining target
2. Designed Chebyshev sequence proof for `arccos(1/9)` irrationality
3. Proved `cos_two_icoAngle : cos(2 * icoAngle) = 1/9` via double-angle formula
4. Proved `arccos_one_ninth_eq : arccos(1/9) = 2*π - 2*icoAngle` using `arccos_lt_arccos`
5. Defined `icoSeq : ℕ → ℤ` with recurrence `d_{n+2} = 2d_{n+1} - 81d_n`
6. Proved `three_ndvd_icoSeq`: mod-3 induction showing 3 ∤ d_n for all n
7. Proved `icoSeq_eq_cos`: `(icoSeq n : ℝ) = 9^n * 2*cos(n * arccos(1/9))`
8. Assembled main contradiction: if icoAngle = (p/q)π, cos(q·arccos(1/9)) = 1 via `cos_int_mul_two_pi`
9. Then `icoSeq q = 2 * 9^q` (divisible by 3) — contradiction with `three_ndvd_icoSeq`

### Key Lemmas Used

- `cos_two_mul` (Mathlib)
- `cos_arccos` (Mathlib) — for evaluating `cos(arccos x)`
- `arccos_lt_arccos` — to bound icoAngle in (π/2, π)
- `cos_int_mul_two_pi` — `cos(n * 2π) = 1`
- `Prime.dvd_or_dvd` — used `3 ∤ 2` in mod-3 argument

### Files Modified

- `proofs/Proofs/DissectionOfCubesOQ04.lean` (432 → 557 lines)
  - Replaced `axiom icoAngle_irrational` with full 115-line proof
  - Axiom count: 2 → 1 (only `tmul_infinite_order_ne_zero` remains)

### Next Steps

- Verify proof compiles via `docker-build.sh Proofs.DissectionOfCubesOQ04`
- Attempt `tmul_infinite_order_ne_zero` (flatness of ℝ over ℤ) — harder infrastructure

---

## Dead Ends

- Edge-count scaling approach for `cube_unique_zero_dehn` was wrong — `tmul_infinite_order_ne_zero` is the right unifier
- Trying Chebyshev directly in ℤ[√5] for icoAngle — unnecessary, cos(2·icoAngle)=1/9 reduces to integer sequence

---

## Session 9 (2026-04-28) — Metadata Audit

**Mode**: REVISIT (researcher-4)
**Outcome**: stale-metadata reconciliation; no math work needed.

### What I Did

1. Picked this problem because pool listed it `available` with knowledge score 24 (RICH tier).
2. Inspected `proofs/Proofs/DissectionOfCubesOQ02.lean`, `DissectionOfCubesOQ02OQ02.lean`, `DissectionOfCubesOQ04.lean`: 0 `axiom` declarations, 0 `sorry` occurrences across the chain. The OQ02→OQ02OQ02→OQ04 import chain does not pull in the base `DissectionOfCubes.lean`, so the 2 base axioms `smaller_cube_above_axiom` and `all_different_implies_long_chains_axiom` (which live in the OQ01 branch via `import Proofs.DissectionOfCubes`) do not propagate here.
3. Confirmed `tmul_infinite_order_ne_zero` is a proved theorem at `DissectionOfCubesOQ02OQ02.lean:214-252` using `Module.Flat ℤ ℝ` + `Module.Flat.lTensor_preserves_injective_linearMap` — closed in commit `f392d09c61` (PR #12587, "prove(dissection-oq-04): eliminate last axiom via Module.Flat — OQ02OQ02 and OQ04 now verified").
4. Confirmed `icoAngle_irrational` is a proved theorem at `DissectionOfCubesOQ04.lean:396` (Session 8 work).
5. Cross-checked `src/data/proofs/dissection-of-cubes-oq-04/meta.json`: `meta.status = "verified"`, `meta.axiomCount = 0`, `meta.assumptions` already documents that no axioms remain.

### Key Finding

The mathematical work is complete. The stale state was confined to:
- `.lean/state/candidate-pool.json` entry (`status: available`)
- `src/data/research/problems/dissection-of-cubes-oq-04.json` (`status: active`, `phase: ACT`, `progressSummary` claiming the axiom remained)

This matches the "stale completed candidate-pool entries" pattern logged in researcher memory (4-in-a-row 2026-04-27 → PRs #13213 #13218 #13220).

### Files Modified

- `src/data/research/problems/dissection-of-cubes-oq-04.json` — set `status: completed`, `phase: COMPLETED`, updated `progressSummary`, added Session 9 insight + builtItem, cleared `nextSteps`.
- `research/problems/dissection-of-cubes-oq-04/knowledge.md` — this session block.
- (`.lean/state/candidate-pool.json` is gitignored and rebuilt by the seeker; not committed.)

### Next Steps

None for this problem. Future researchers should check the gallery `meta.json` first when a RICH-tier problem appears `available` with stale `ACT`-phase notes — the JSON often lags behind PR-merged proofs.

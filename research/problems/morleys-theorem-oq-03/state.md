# State: morleys-theorem-oq-03

**Phase**: COMPLETED
**Status**: completed (verified/original, registered, Docker build-confirmed GREEN)

## Result

`proofs/Proofs/MorleysTheoremOQ03.lean` — **0 sorries / 0 axioms**, registered in
`proofs/Proofs.lean` (`import Proofs.MorleysTheoremOQ03`), merged to `main`, and
machine-verified: `docker-build.sh Proofs.MorleysTheoremOQ03` → **Build succeeded
(7743 jobs)**, 2026-06-16 (re-confirmed; original docker-build 2026-06-15).

OQ-03 (extremal Morley): among triangles of fixed circumradius `R`, the equilateral
triangle **uniquely** maximizes the Morley side length, with max `8 R sin³(π/9)`.

All milestones DONE and compiled:

- `amgm_three` — AM–GM(3) cubed form (nlinarith + explicit SOS certificate).
- `sin_jensen_three` — 3-point Jensen for `sin` on `[0,π]` (chained 2-point concavity).
- `sin_two_eq` / `sin_jensen_three_eq` — strict equality cases of two-/three-point Jensen.
- `div_three_mem_Icc` — trisected angle in `[0,π]`.
- `morley_side_le_equilateral` — `s ≤ 8R sin³(π/9)`.
- `morley_side_equilateral` / `morley_side_max` — attainment + packaged max.
- `morley_side_eq_iff` — **strict uniqueness**: `s = 8R sin³(π/9) ↔ α=β=γ=π/3`.

## Remaining

None. The formal target (sharp bound + attainment + strict uniqueness) is fully
machine-verified. The earlier "strict uniqueness / build / registration" TODOs are
discharged (`morley_side_eq_iff` proves the iff; the file is registered and builds
green). Gallery entry `src/data/proofs/morleys-theorem-oq-03/meta.json` is accurate
(`status: verified`, `badge: original`, `axiomCount: 0`, `sorries: 0`).

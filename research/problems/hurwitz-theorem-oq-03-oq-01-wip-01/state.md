# Research State: hurwitz-theorem-oq-03-oq-01-wip-01

## Current State
**Phase**: ACT (commutative subcase landed)
**Path**: full
**Since**: 2026-07-04T15:36:57-07:00
**Iteration**: 3

## Current Focus
`hurwitz_only_if_ring_comm` now proved (0 sorries). The one remaining sorry
(`hurwitz_only_if_ring`, Step 3) is purely the non-commutative Frobenius/Clifford
content — the commutative half is now an unconditional theorem.

## Active Approach
Frobenius: split A = R*1 ⊕ ImA, positive-definite anticommutator bilinear form on ImA,
finrank ImA in {0,1,3}. Keystone lemma = anticommutator polarization (x*y+y*x in R*1).

## Attempt Count
- Total attempts: 1 (code)
- Approaches tried: 1 (commutative reduction via NormedField instance promotion)

## Result this iteration (attempt 1)
**`hurwitz_only_if_ring_comm`** — a commutative finite-dim normed division ring over ℝ
has finrank ∈ {1,2,4,8}. Proof: promote `NormedDivisionRing A` to `NormedField A` via
`letI := { inferInstance with mul_comm := hcomm }` (all other fields shared, ring data
unchanged so ambient `NormedAlgebra ℝ A` still applies), then apply `hurwitz_field_case`
(Gelfand-Mazur). Docker build verified (2715 jobs, HurwitzOnlyIf).

## Blockers
- Aristotle MCP was down earlier ("Resource not found"); recheck before submitting the
  hard sorry.
- Host swap ~98% full — but incremental single-file Docker builds (~5s) succeed; keep an
  eye on `vm.swapusage` before each build.

## Next Action
Remaining sorry is the non-commutative Frobenius Step 3 (Clifford structure on Im A) —
genuinely out of scope here. Options: (1) keystone anticommutator lemma
`x*y + y*x ∈ ℝ•1` for imaginary x,y; or (2) submit `hurwitz_only_if_ring` to Aristotle
(hint=Frobenius, context=HurwitzOnlyIf.lean) once the MCP is back.


## Session 2026-07-08 (researcher-6) — Part 7: equilateral corollaries

**Mode:** REVISIT (mature axiomatized AAA-congruence entry)
**Outcome:** progress (2 new theorems, 0 new assumptions)

### What I Did
Added two clean corollaries around the equilateral hyperbolic triangle:
- `equilateral_angle_lt_pi_third` — an equilateral triangle (all angles equal) has
  common angle `< π/3`. Direct from the angular defect `A+B+C < π` (`3θ < π`); the
  sharp hyperbolic counterpart of the Euclidean equilateral angle `π/3`.
- `equilateral_pi_four_cosh` — the equilateral triangle with all angles `π/4` has
  every side `arcosh(1+√2)`: `cosh side = cos(π/4)/(1-cos(π/4)) = 1+√2`. A concrete
  closed value off the existing `equilateral_cosh`; `π/4 < π/3` confirms admissibility
  and `1+√2 > 1` a genuine side.

### Verification
Built clean: `Proofs.LawOfCosinesOQ03OQ03` (3061 jobs), 0 sorries, 0 axiom
declarations. File now 331 lines, 22 theorems, 2 structures. Status stays
**axiomatized** (the 7 structure-encoded geometric assumptions are unchanged; the
new theorems introduce none). Key steps: `linarith` on the defect; `linear_combination
(1/2)·(√2²=2)` after `div_eq_iff`, with `√2 < 2` via `nlinarith`.

### Files Modified
- `proofs/Proofs/LawOfCosinesOQ03OQ03.lean` (Part 7, +~35 lines, verified)
- `src/data/proofs/law-of-cosines-oq-03-oq-03/meta.json` (counts + contribution)
- `src/data/research/problems/law-of-cosines-oq-03-oq-03.json` (counts + knowledge)

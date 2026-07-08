
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

## Session 2026-07-08 (researcher-7) — Part 8: equilateral monotonicity

**Mode:** REVISIT (mature axiomatized AAA-congruence entry). **Outcome:** progress
(3 new theorems, 0 new assumptions).

### What I Did
Added monotonicity of the equilateral family across the common angle, complementing the
existing `equilateral_cosh` (closed form) and `equilateral_angle_lt_pi_third` (angle < π/3):
- `one_sub_cos_C_pos (t) : 0 < 1 - cos t.C` — the inverted-second-law denominator is
  positive; `nlinarith [sin_sq_add_cos_sq, sin_C_pos, neg_one_le_cos]` (0<C<π ⟹ cos C<1).
- `equilateral_cosh_antitone_in_angle (t₁ t₂) (both equilateral) (t₁.C < t₂.C) :
  cosh t₂.c < cosh t₁.c`. From `equilateral_cosh` both sides = cos θ/(1-cos θ); clear
  denominators with `div_lt_div_iff₀ (pos) (pos)` then `nlinarith [hcos]` (cross terms cancel
  to cos C₂ < cos C₁, which is `Real.cos_lt_cos_of_nonneg_of_le_pi` on the angle order).
- `equilateral_side_antitone_in_angle` : `t₂.c < t₁.c` — side form via
  `Real.cosh_strictMonoOn.lt_iff_lt` (same pattern as `side_antitone_in_angle`).
Reading: smaller angle ⟹ larger triangle; θ ↗ π/3 shrinks to the Euclidean limit, θ ↘ 0
grows unboundedly — the hyperbolic reversal of Euclidean similarity (all equilateral = π/3).

### Verification
Host `lake env lean Proofs/LawOfCosinesOQ03OQ03.lean` EXIT 0 (no warnings);
`#print axioms equilateral_side_antitone_in_angle` = [propext, Classical.choice, Quot.sound].
File 331→373 lines, 22→25 theorems. Status stays **axiomatized** (7 structure-encoded
assumptions unchanged; new theorems add none). ★v4.26 gotcha: the positive-denominator
`a/b < c/d ↔ a*d < c*b` lemma is `div_lt_div_iff₀` (NOT `div_lt_div_iff`, which is now the
group version `div_lt_div_iff'`).

### Files Modified
- `proofs/Proofs/LawOfCosinesOQ03OQ03.lean` (Part 8, +~45 lines, verified)
- `src/data/proofs/law-of-cosines-oq-03-oq-03/meta.json` (counts + contribution)
- `src/data/research/problems/law-of-cosines-oq-03-oq-03.json` (leanFiles counts)

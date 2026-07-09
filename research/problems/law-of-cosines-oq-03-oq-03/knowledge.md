
## Session 2026-07-08 (researcher-6) — Part 8: equilateral-family monotonicity

**Mode:** REVISIT (mature axiomatized AAA-congruence entry)
**Outcome:** progress (2 new theorems, 0 new assumptions)

### What I Did
Added Part 8: monotonicity of the side along the one-parameter *equilateral family*.
- `equilateral_cosh_antitone` — for two equilateral hyperbolic triangles with common
  angles `θ₁ < θ₂`, `cosh(side₂) < cosh(side₁)`. Shows the closed form
  `θ ↦ cos θ / (1 - cos θ)` (from `equilateral_cosh`) is strictly decreasing across the
  admissible range `(0, π/3)`: side → ∞ as `θ → 0`, side → 0 as `θ → π/3` (Euclidean limit).
- `equilateral_side_antitone` — the same comparison on the sides themselves,
  `t₂.c < t₁.c`, via `cosh` injectivity on `[0, ∞)`.

Distinct from Part 4b (`side_antitone_in_angle`), which pins **two** angles and varies the
third; here all three angles move together along the equilateral family. Sharpens AAA
congruence (Part 4) into a strict order across the family — the hyperbolic counterpart of
"all Euclidean equilateral triangles are similar", except each admissible angle pins a
*unique* size.

### Verification
- **Docker build failed (exit 135, SIGBUS)** twice — line-less, at the final
  `[3061/3061]` compile step *after* successful elaboration (build #1 had surfaced a
  normal elaboration error), i.e. Docker-volume corruption, not a proof bug.
- **Host-verified** instead: `lake exe cache get` + `lake env lean
  Proofs/LawOfCosinesOQ03OQ03.lean` → exit 0, no output (0 errors, 0 sorries).
- `#print axioms` on both new theorems: `[propext, Classical.choice, Quot.sound]` only —
  no `sorryAx`, no `Lean.ofReduceBool`. Zero new assumptions.

File now 373 lines, 24 theorems. Status stays **axiomatized** (7 structure-encoded
geometric assumptions unchanged). Key steps: `div_lt_div_iff₀` (NOT `div_lt_div_iff`,
unknown in Mathlib v4.26) to clear denominators + `nlinarith [hcos]`; `1 - cos θ > 0`
via `cos θ < cos 0 = 1` from `cos_lt_cos_of_nonneg_of_le_pi`.

### Files Modified
- `proofs/Proofs/LawOfCosinesOQ03OQ03.lean` (Part 8, +~48 lines, host-verified)
- `src/data/proofs/law-of-cosines-oq-03-oq-03/meta.json` (counts + contribution + 2 mainTheorems)
- `research/problems/law-of-cosines-oq-03-oq-03/knowledge.md` (this note)

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

## Session 2026-07-08 (researcher-1) — axiom-reduction assessment (no PR)

Problem is COMPLETE (0 sorries, 20 theorems). Investigated nextStep #1 (reduce the 7
structure-encoded axioms in `HyperbolicTriangle`). Findings:

- The three second laws lawA/lawB/lawC each involve a DIFFERENT side (cosh a / cosh b /
  cosh c), so they are mutually independent — deriving "three seconds from one first law"
  requires ADDING the first law of cosines + sine rule apparatus (a large derivation, no
  net axiom saving 3→3).

- **BETTER target found: the `defect` field (A+B+C < π) is REDUNDANT** — derivable from
  the other axioms, so removing it reduces 7→6. Concrete argument (verified on paper,
  NOT yet formalized):
  1. From ha/hb/hc (sides > 0) get cosh a,b,c > 1 via `Real.one_lt_cosh` (1<cosh x ↔ x≠0).
  2. cosh_c_eq + cosh c > 1 ⟹ (cos C + cos A cos B)/(sin A sin B) > 1 ⟹ **cos C + cos(A+B)
     > 0** (rearrange, sin A sin B>0; cos(A+B)=cosAcosB−sinAsinB). Similarly cos A+cos(B+C)
     > 0 and cos B+cos(A+C) > 0 (need cosh_a_gt_one/cosh_b_gt_one — only cosh_c_gt_one
     exists; add the two analogues, trivial from one_lt_cosh).
  3. sum-to-product `Real.cos_add_cos`: each becomes 2·cos(S/2)·cos(δ/2) > 0 where
     S=A+B+C. So cos(S/2) ≠ 0 and the three cos(δ/2) share its sign.
  4. Suppose cos(S/2) < 0 (S/2 ∈ (π/2,3π/2)). Then all three cos(δ/2)<0; from the C-one,
     cos((C−A−B)/2)<0 forces A+B−C>π (since C<π, A,B>0 bound the range); symmetrically
     B+C−A>π. Add: 2B>2π ⟹ B>π, contradicting hB_lt. So cos(S/2)>0 ⟹ S/2<π/2 ⟹ **S<π**.
  5. Replace `defect` field with theorem `defect_of_laws`, rewire angle_sum_lt_pi /
     area_positive / equilateral_angle_lt_pi_third (currently use t.defect).

  Est. 60–100 lines of delicate trig (cos sign/monotonicity on intervals) + refactor.
  Genuine 7→6 structure-axiom reduction. Deferred (hard, needs fresh budget); left this
  sketch so it's a clean next win. Other nextSteps (SAS/ASA congruence, area-defect
  integral) are also substantial.

# Session: 2026-05-14 — S2-Gauss-real ACT

**Researcher**: researcher-8
**Date**: 2026-05-14 (UTC)
**Phase**: ACT mini-task (build-verified, Lean delta +45 LOC / +1 theorem)
**Predecessor**: S2d ACT Path A (researcher-4, PR #18742); S2 build-verify
(researcher-9, PR #19033 OPEN)

## Goal

Bridge S2d's `Nat`-valued explicit Gauss-circle bound
`(latticeDisc R).card ≤ (2⌈|R|⌉+1).toNat^2` to a `Real`-form analytic
bound `((latticeDisc R).card : ℝ) ≤ (2|R| + 3)²`, suitable for
downstream `ℓ¹`-majorisation / Plancherel estimates on `sphPartialSum`.
The expanded form `4|R|² + 12|R| + 9` is the natural qualitative `O(R²)`
analytic upper bound usable without the sharp π constant (which remains
deferred to S2-Gauss-sharp via boundary-lattice / two-squares analysis).

## Approach

Direct elaboration-order composition of S2d's `latticeDisc_card_le_explicit`
with the cast bridge:

1. `Int.ceil_nonneg (abs_nonneg R) : 0 ≤ ⌈|R|⌉` and `linarith` ⇒
   `hpos : 0 ≤ 2 * ⌈|R|⌉ + 1` (in ℤ).
2. `exact_mod_cast latticeDisc_card_le_explicit R` pushes the Nat ≤
   inequality through `ℝ`-cast.
3. `Int.toNat_of_nonneg hpos` (via `exact_mod_cast`) drops the `.toNat`
   wrapper since the integer is provably nonneg.
4. `Int.ceil_lt_add_one |R|` + `push_cast` + `linarith` establishes
   `(2*⌈|R|⌉+1 : ℝ) ≤ 2*|R| + 3`.
5. `pow_le_pow_left₀ h_nn_R h_lin 2` squares the linear inequality
   monotonically (using `0 ≤ (2*⌈|R|⌉+1 : ℝ)` from `exact_mod_cast hpos`).
6. `linarith` closes the goal.

## Outcome

Shipped **1 new sorry-free, axiom-free theorem** in
`proofs/Proofs/FourierSeriesOQ04OQ01.lean`:

- `latticeDisc_card_le_real (R : ℝ) : ((latticeDisc R).card : ℝ)
                       ≤ (2 * |R| + 3) ^ 2`

**Build verified**: Docker rebuild on the worktree finished `Build
completed successfully (7743 jobs)` with the single expected sorry
warning at line 148 (`sphPartialSum_L2_norm_converge`, S2a's pre-existing
L²-norm-convergence companion). No new warnings.

**File metrics**: 234 → 279 lines (+45); 7 → 8 theorems; 1 axiom (unchanged);
5 defs (unchanged); 1 sorry (unchanged).

## What was learned (insight worth saving)

The cast bridge `Nat → ℝ` for cardinality bounds with `.toNat` wrapping
requires four ordered steps:

1. `exact_mod_cast` on the original Nat bound.
2. `Int.toNat_of_nonneg` (also via `exact_mod_cast`) once the underlying
   ℤ value is shown nonneg.
3. `Int.ceil_lt_add_one` for the ceil/abs linear bound under `push_cast` +
   `linarith`.
4. `pow_le_pow_left₀ h_nn h_le 2` to square the linear inequality
   monotonically.

The `push_cast` between integer-side `2*⌈|R|⌉+1` and Real-side is
essential because `Int.ceil_lt_add_one` outputs an ℝ-shaped inequality
already, but the LHS still carries the `(... : ℝ)` ℤ→ℝ cast.

## Next steps (carryover)

Unchanged from S2d state:
- **S2e ACT (PRIORITY)** — discharge `sphPartialSum_L2_norm_converge`
  sorry via the synthesised mFourierBasis spec from PREP chain #18446 →
  #18545 → #18694 (70-95 LOC budget, 2-3 Docker iterations).
- **S2-Gauss-sharp** — extend `(latticeDisc R).card ≤ (2|R|+3)²` to
  `card ≤ ⌈π·R²⌉ + O(R)` via boundary-lattice / two-squares or
  Lebesgue-measure unit-square covering (~80-150 LOC).
- **S2b** — Bochner-Riesz a.e. convergence for δ > 1/2 in n=2 (Stein
  1958, ~300-500 LOC, separate 2-3 iterations).

## Companion PR

Researcher-9 PR #19033 (S2 build-verify, doc-only, OPEN) retires the
`(build pending)` qualifier on the verified-clean S2d baseline. This PR
(S2-Gauss-real ACT) is the first build-verified ACT delivering new Lean
content on top of that baseline.

## Files modified

- `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (234 → 279 lines, +1 theorem)
- `src/data/research/problems/fourier-series-oq-04-oq-01.json`
  (currentState bumped iter 4→5, since 2026-05-13→2026-05-14, focus
  updated; knowledge.progressSummary + builtItems + insights extended;
  leanFiles lineCount 234→279, theoremCount 7→8; lastUpdate refreshed)
- `research/problems/fourier-series-oq-04-oq-01/state.md` (new
  S2-Gauss-real section at top; S2d demoted to "Previous Iteration"
  heading; iteration header 4→5, Since date 2026-05-13→2026-05-14)
- `research/problems/fourier-series-oq-04-oq-01/sessions/2026-05-14-s2-gauss-real-act.md`
  (this file, NEW)

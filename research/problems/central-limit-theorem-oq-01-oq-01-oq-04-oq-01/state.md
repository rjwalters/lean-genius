# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1, researcher-1)
**Iteration**: 1

## Current Focus

S1 (researcher-1, 2026-05-12): survey of the partial Mathlib
formalization of the **Meerschaert-Scheffler Domain of Attraction
Theorem** for multivariate operator-stable distributions. Maps the
axiom `meerschaert_scheffler` (`CentralLimitTheoremOQ01OQ01OQ04.lean`,
line 309) against Mathlib `v4.26.0`'s weak-convergence and
characteristic-function infrastructure. Identifies three discharge
routes:

- **R1 (recommended)**: restate the M-S biconditional for the
  Gaussian sub-case `(φ = gaussCharFun d Σ, E = (1/2)·I, ν = gaussCharFun d Σ)`,
  drawing on parent's `gaussian_in_own_doa` and
  `gaussian_has_scalar_exponent`. ~80-150 Lean lines, 0 axiom delta,
  produces a *non-trivial axiom-instance theorem*.
- **R2**: scalar-exponent reduction `E = (1/α)·I` → univariate
  Gnedenko-Kolmogorov. ~150-300 Lean lines; shifts axiom location to
  the grandparent file (`central-limit-theorem-oq-01-oq-01`) without
  reducing axiom count.
- **R3**: forward direction (`(i) → (ii)`) of M-S. Blocked by missing
  Mathlib matrix-regular-variation machinery (BGT §2.10,
  Meerschaert-Scheffler 2001 §6). Deferred.

The parent file's status remains **`axiomatized`** (2 axioms, 18
theorems, ~303 lines). R1 does not eliminate any axiom; it produces a
Gaussian-specialised companion theorem that *applies* the M-S form to
a concrete proven sub-case.

## Active Approach

**S1 (this iteration)** is doc-only. Deliverables:

1. **`research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/problem.md`**
   (~280 lines): full survey, three routes, Mathlib gap map,
   reference reading list.
2. **`research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/knowledge.md`**
   (this iteration's session note + Lean skeleton for the S2 R1
   deliverable): ~210 lines.
3. **`research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01/state.md`**
   (this file): ~140 lines.
4. **`src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04-oq-01.json`**:
   research index entry with insights/builtItems/nextSteps.

No Lean changes. No sorry / axiom delta. No gallery-status change.

## Blockers

None mathematical for R1 (Gaussian specialisation). For R3,
**matrix regular variation** is the structural blocker — Mathlib's
regular-variation API (BGT §1.4 scope) is partial even in the scalar
case; the matrix extension is absent at the pin.

Practical:

- **Mathlib API exploration for S2**: `Mathlib.Analysis.NormedSpace.MatrixExponential`
  contains `Matrix.exp` but the simplification
  `Matrix.exp (Real.log t • ((1/2) • 1)) = √t • 1` may require
  hand-derivation. S2 will spend ~20 lines on this matrix-exp
  identity.
- **Docker build cost**: any S2 PR touching the new companion file
  will trigger a `Mathlib.Probability` + `Mathlib.MeasureTheory`
  rebuild (~10-15 min, cache-hit-likely).
- **Worktree `.lake` symlink**: known broken on this worktree (per
  memory entry). Any S2 PR runs `docker-build` ⇒ ≥45 min build
  window. Plan accordingly.

## Next Action

**S2 (any researcher): R1 ACT — implement
`meerschaert_scheffler_gaussian` in a new companion file.**

Concrete plan (one deliverable, ~80-150 Lean lines, 0 sorry / axiom
delta on the parent):

1. **Create `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04Meerschaert.lean`**
   (~80 lines):
   - Helper: `matrix_exp_log_smul_half_id (d : ℕ) (t : ℝ) (ht : 0 < t) :
     Matrix.exp (Real.log t • ((1/2) • 1)) = Real.sqrt t • 1` (~20
     lines via scalar-matrix exp + log/sqrt chain).
   - Main: `meerschaert_scheffler_gaussian (d : ℕ) (Σ : Matrix (Fin d)
     (Fin d) ℝ)` — the M-S characteristic-function convergence in the
     Gaussian sub-case (~60 lines using `gaussian_operator_stable`,
     `gaussian_has_scalar_exponent`, `exp_neg_div_pow`,
     `quadForm_scale_inv_sqrt`).
2. **Update `proofs/Proofs.lean`**: add the new import.
3. **Update `state.md`, `knowledge.md`, JSON** with S2 results.
4. **Commit, push, PR with label `research`** under standard
   `(build pending)` gallery convention.

After S2 completes, **S3 (optional)** will implement R2 scalar-exponent
reduction. **S4+** (full M-S formalisation) remains blocked until
Mathlib lands matrix regular variation.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| S1.1 | Pool-claim race-check: 0 open PRs, 0 orphan branches, 0 recent merges for slug | safe to claim |
| S1.2 | `claim-problem.sh claim central-limit-theorem-oq-01-oq-01-oq-04-oq-01` (tier B fresh, EMPTY knowledge) | claimed 2026-05-12T19:28Z |
| S1.3 | `git checkout -b research/central-limit-theorem-oq-01-oq-01-oq-04-oq-01-s1-observe-<ts> origin/main` | clean branch |
| S1.4 | Read parent `CentralLimitTheoremOQ01OQ01OQ04.lean` (303 lines, 18 theorems, 2 axioms) | identified `meerschaert_scheffler` at line 309 |
| S1.5 | Read parent `knowledge.md` (Session 2026-05-04 history) | recovered formalisation context |
| S1.6 | Surveyed Mathlib `Probability/CharacteristicFunction.lean`, `MeasureTheory/Measure/Portmanteau.lean`, `Analysis/NormedSpace/MatrixExponential.lean` | API map drafted |
| S1.7 | Drafted R1 / R2 / R3 routes with effort estimates and Mathlib-reachability assessments | strategy clear |
| S1.8 | Wrote problem.md (~280 lines), knowledge.md (~210 lines), state.md (this file), and JSON entry | S1 OBSERVE complete |
| S1.9 | Pre-push race re-check + commit + push + PR with label `research` | next |

## Honest Calibration

S1 produces:

- **Four new markdown / JSON files** (problem.md, knowledge.md,
  state.md, and the research JSON entry).
- **Zero Lean changes.**
- **A documented three-route discharge plan** (R1 immediate, R2
  optional, R3 blocked).

S1 does **not**:

- Discharge `meerschaert_scheffler` or any other axiom.
- Modify any Lean file.
- Change the parent's axiom count or sorry count.
- Upgrade the gallery status.

The next iteration (S2 ACT R1) is where Lean-side deliverable value
appears (a Gaussian-specialised M-S theorem in a new companion file).
The **realistic estimate** for closing this OQ in the
"non-trivial axiom-instance theorem" sense is **1 more session**
(S2 R1), with optional follow-up (S3 R2) for the scalar-exponent
reduction.

Full elimination of `meerschaert_scheffler` in its multivariate
generality is **out of scope** of this OQ (it requires matrix
regular variation, a 6-12 month Mathlib infrastructure project).

## References Captured

- Meerschaert & Scheffler (2001), *Limit Distributions for Sums of
  Independent Random Vectors*, Wiley. Chapter 8, Theorem 8.2.1.
- Hudson & Mason (1982), "Operator-stable laws".
- Sharpe (1969), "Operator-stable probability distributions on
  vector groups".
- Jurek & Mason (1993), *Operator-Limit Distributions in Probability
  Theory*.
- Bingham, Goldie & Teugels (1987), *Regular Variation*.
- Mathlib modules: `Probability/CharacteristicFunction`,
  `MeasureTheory/Measure/Portmanteau`,
  `Analysis/NormedSpace/MatrixExponential`.
- Parent file: `CentralLimitTheoremOQ01OQ01OQ04.lean`.
- Grandparent file: `CentralLimitTheoremOQ01OQ01.lean`.

# Knowledge: erdos-666-incomplete-01

## Overview

Initial knowledge for problem `erdos-666-incomplete-01`.

## Gallery Proof Summary

- Gallery: `erdos-666` — Erdős Problem #666: C₆ in Hypercube Subgraphs
- Sorries: 1, Axioms: 1
- Tags: erdos, graph-theory, hypercube, cycles, extremal-graph-theory, disproved

## Known Results

(To be populated during OBSERVE phase)

## Key References

- Gallery: `src/data/proofs/erdos-666/`
- Lean source: `proofs/Proofs/` (check namespace `Erdos666`)

## Session (researcher-2, 2026-07-08): interval refutation ε ≤ 1/4

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (4 theorems VERIFIED, 0 new axioms),
branch research/erdos666-interval-refutation-r2

**Contribution — Part IV.5: refutation on the whole interval ε ≤ 1/4.** The axiom
`chung_no_threshold : ¬ConjectureAt (1/4)` only names the single density 1/4. Added
a density-monotonicity chain that extends the refutation to every ε ≤ 1/4 without any
new axiom:
- `epsilonDense_antitone` (unseal EpsilonDenseSubgraph): ε'≤ε ⇒ (ε-dense H ⇒ ε'-dense H),
  since `ε'·Eₙ ≤ ε·Eₙ ≤ #edges` (`Eₙ = n·2ⁿ⁻¹ ≥ 0`, `mul_le_mul_of_nonneg_right` +
  `le_trans`). One-liner term proof.
- `denseForcesC6_mono` / `conjectureAt_mono`: `DenseForcesC6` and `ConjectureAt` are
  monotone in ε (ε-dense graphs are a subclass of ε'-dense ones; same threshold N).
- `chung_no_threshold_le : ε ≤ 1/4 → ¬ConjectureAt ε` — the headline: monotonicity would
  push a conjecture-at-ε up to 1/4, contradicting the axiom. So Erdős's conjecture fails
  robustly across the whole range (0, 1/4], not at an isolated point.

**File state:** 1 axiom (`chung_no_threshold`, genuinely deep — Chung's 4-partition, not
in Mathlib, NOT eliminable), 0 sorries. 326→368 lines.

**Gotcha:** a `/-- docstring -/` must come AFTER `unseal … in`, not before — a docstring
cannot attach to the `unseal` command (`unexpected token 'unseal'; expected 'lemma'`).
Match the existing `chung_c6free` order: `unseal … in` / `/-- … -/` / `theorem`.

**Remaining (unchanged):** `conder_better_bound` keeps a `True` placeholder for the
ε=1/3 density (needs Conder's 3-coloring = a new deep axiom); `GeneralizedConjecture`
(C_{2k}) open. Build: green attempt 1.

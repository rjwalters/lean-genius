# Research State: descartes-rule-of-signs-oq-01-oq-02

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-05-13T11:40:00Z
**Iteration**: 3 (S3 STATE-SYNC, 2026-05-16: doc-only JSON catchup; see sessions/2026-05-16-s3-statesync-residual-drift-catchup.md)

## Completed Work

**The OQ**: "What is the minimal infrastructure for Descartes parity — just complex
conjugate pairing, or also exact sign variation change under each root type?"

**The answer**: **Both are needed.** This is captured in `DescartesRuleOfSignsOQ01OQ02.lean`
(317 LOC, 13 theorems, 1 axiom, 0 sorries, axiomatized):

1. **Complex conjugate pairing** (proved in sibling `DescartesRuleOfSignsOQ01OQ01.lean`):
   non-real roots pair, so `Even nonreal`. Gives `degree ≡ real_roots (mod 2)`.

2. **Sign variation parity under root extraction** (axiomatized as
   `sign_variation_parity_under_positive_root`): when `p = (X - C r) * q` with `r > 0`,
   `¬Even (signVariations p + signVariations q)`. This is the *irreducible* combinatorial-
   algebraic ingredient — Mathlib only proves the *inequality* version
   (`succ_signVariations_le_X_sub_C_mul`), not the parity.

3. **Parity chain** (`parity_chain`, `descartes_parity_witness`): given the four
   structural ingredients, the existential witness `pos + 2k = sv` follows.

Resolution at small degrees: linear, quadratic, cubic, quartic each instantiate the
witness via `parity_witness` + bounded `omega`.

## Active Approach

None — slug answered.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 1 (structural infrastructure analysis)
- Iteration 3 (S3 STATE-SYNC, 2026-05-16T~18:55Z): doc-only JSON catchup absorbing predecessor #18791 (S2 COMPLETION-SYNC, T-3d) residual drift on `currentState.*` (phase/since/iteration/focus/nextAction/attemptCounts), `lastUpdate`, and `leanFiles[3].{lineCount,theoremCount}`. No research progress, no new approach, no axiom discharge.

## Blockers

None.

## Next Action

None — slug answered. The remaining axiom is the genuine hard part (the parity version
of Descartes' rule, beyond Mathlib's current inequality version), and stands as a
documented open lemma rather than a research gap.

If anyone wants to discharge the axiom: requires a coefficient-sign-sequence analysis of
`(X - C r) * q` — see Mathlib's `Polynomial.RuleOfSigns` for the inequality version and
extend the induction with a parity refinement. Estimated 200–500 LOC.

## Follow-up Open Question Candidate

`oq-01-oq-02-oq-01` (candidate): Can `sign_variation_parity_under_positive_root` be
discharged by extending Mathlib's `succ_signVariations_le_X_sub_C_mul` induction with a
parity refinement? Specifically, can `signVariations_eq_eraseLead_add_ite` be lifted to
give exact `signVariations(p) = signVariations(q) + 2k + 1`?

This is a concrete forward step rather than a vague generalization — and a natural one,
since Mathlib's current proof gets `≥ signVariations(q) + 1` and the parity version
would refine the inequality.

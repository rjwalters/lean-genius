# Current State

**Phase**: ORIENT
**Since**: 2026-07-02
**Iteration**: 1 (survey)

## Current Focus

S1 survey complete (see `knowledge.md`). Target = Marcinkiewicz–Zygmund SLLN
(`1 ≤ p < 2`, normalisation `n^{1/p}`). Verdict: **SURVEY → multi-session
BUILD**, not one-session provable, and should **not** be axiomatised (parent
chain already carries 1 + 3 axioms).

## Active Approach

None in-flight. Next concrete work item is the S2 sub-target below.

## Blockers

Two Mathlib dependencies verified **absent** and needed before MZ can be proved:
1. **Kronecker's lemma** for real series (only `PosSemidef.kronecker` matrix
   product exists — unrelated).
2. **Kolmogorov three-series / a.s.-convergence-of-independent-`L²`-series**
   criterion (only Kolmogorov's 0-1 law is in Mathlib).

## Next Action

- **S2 (tractable, ~1 session, 0-axiom):** formalise **Kronecker's lemma**
  (`aₙ ↑ ∞`, `∑ xₙ/aₙ` converges ⟹ `a_n^{-1} ∑_{i≤n} xᵢ → 0`). Standalone,
  independently useful, unblocks step 5 of the MZ decomposition.
- **S3 (multi-session):** build the Kolmogorov a.s.-convergence criterion for
  independent `L²`-bounded series (the real bottleneck, >300 LOC).
- **S4:** assemble truncation (steps 1–3 of the decomposition) + conclude MZ.

## Attempt Counts

- Total attempts: 1 (text-only survey)
- Current approach attempts: 0
- Approaches tried: 1 (literature/decomposition + Mathlib API audit)

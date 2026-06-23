# Current State

**Phase**: COMPLETED
**Since**: 2026-03-30T03:32:02Z (PR #8098 merge)
**Iteration**: 1

## Current Focus

None — problem resolved. The Cauchy condensation test fully generalises Oresme's grouping argument and is a complete biconditional characterisation of summability for nonneg antitone real sequences. Lean formalisation is verified (`status: "verified"`, `badge: "mathlib"`) via Mathlib's `summable_condensed_iff_of_nonneg`.

## Active Approach

Single-iteration completion. The mathematical content reduces to a wrapper around Mathlib:

- **Theorem 1 (`cauchy_condensation_test`)** — direct wrapper around `summable_condensed_iff_of_nonneg`, stating `Summable f ↔ Summable (fun k => 2^k * f(2^k))` under `0 ≤ f` and `f antitone on ℕ⁺`.
- **Theorem 2 (`cauchy_condensation_diverges`)** — contrapositive (`¬Summable f ↔ ¬Summable (condensed)`).
- **Theorems 3-4 (`one_div_nonneg_nat`, `one_div_antitone`)** — hypotheses for `f(n) = 1/n`.
- **Theorem 5 (`not_summable_one`)** — constant-1 series diverges (`not_summable_const_of_ne_zero one_ne_zero`).
- **Theorem 6 (`condensed_harmonic_diverges`)** — `Σ 2^k · (1/2^k) = Σ 1` diverges (one-line `convert + field_simp`).
- **Theorem 7 (`oresme_via_condensation`)** — Oresme's harmonic divergence as a corollary of Theorems 2+6.
- **Theorem 8 (`harmonic_diverges_mathlib`)** — concordance with Mathlib's direct `not_summable_one_div_natCast`.
- **Theorem 9 (`condensation_iff_summable`)** — restates the biconditional to emphasise that the test is necessary AND sufficient (not merely sufficient).

## Blockers

None. All hypotheses available in Mathlib; no axioms or sorries needed.

## Next Action

None — completed. Optional follow-up levers (not blocking):

1. **Generalise to non-monotone sequences with extra structure** (eg eventually-antitone, quasi-monotone). Not in Mathlib; would require new lemmas.
2. **Schlömilch generalisation** (`Σ φ(k) · f(φ(k))` for super-additive `φ`). Mathlib has `summable_schlomilch_iff_of_nonneg` — analogous wrapper would be ~30 LOC.
3. **p-series corollary** (`Σ 1/n^p` converges iff `p > 1`). Mathlib already proves both directions via `Real.summable_one_div_nat_rpow`; a condensation-route proof would be expository, not a new result.

These are independent research targets; none are pre-conditions for this slug being COMPLETED.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (Mathlib-wrapper)

## Built Items

- `proofs/Proofs/HarmonicDivergenceOQ04.lean` — 106 lines, 9 theorems, 0 definitions, 0 axioms, 0 sorries.
- `src/data/proofs/harmonic-divergence-oq-04/` — gallery entry; `meta.json` `status: "verified"`, `badge: "mathlib"`, `axiomCount: 0`, `sorries: 0`, `lineCount: 106`, `theoremCount: 9`.

## Mathlib Bearers (Verified)

The proof depends on the following Mathlib lemmas (no axioms introduced):

- `Mathlib.Analysis.SpecificLimits.Basic.summable_condensed_iff_of_nonneg` — the condensation test itself.
- `Mathlib.Analysis.SpecificLimits.Basic.not_summable_const_of_ne_zero` — `Σ c` diverges for `c ≠ 0`.
- `Mathlib.Analysis.SpecificLimits.Basic.not_summable_one_div_natCast` — direct harmonic divergence (concordance check).

A bearer-audit against `proofs/lake-manifest.json`-pinned Mathlib SHA should be performed before any downstream port; see the `feedback_researcher_mathlib_head_vs_lockfile_sha_drift.md` memory.

## Honesty Block

- The `cauchy_condensation_test` lemma is a direct `.symm` wrapper around Mathlib's `summable_condensed_iff_of_nonneg` — the heavy lifting is Mathlib's, not this file's. The originality of this gallery entry is in the *pedagogical framing* (Oresme as a special case) and the explicit `oresme_via_condensation` corollary, not in a new mathematical proof of the condensation test.
- `condensation_iff_summable` (Theorem 9) is a verbatim re-statement of Theorem 1 with a renamed identifier. It is retained as a named theorem only to emphasise the biconditional character in expository contexts; if the gallery ever consolidates, this can be removed without loss.
- Status `"verified"` + badge `"mathlib"` are correct per the axiom-integrity policy: 0 `axiom` declarations AND 0 structure-encoded assumptions (no `Axioms` structure here).

# Erdős #1150 - Knowledge Base

## Problem Statement

Does there exist c > 0 such that for all large n and all polynomials P of
degree n with coefficients ±1: max_{|z|=1} |P(z)| > (1+c)√n?

Equivalently: do ultraflat Littlewood polynomials NOT exist?

## Status

**Erdős Database Status**: OPEN
**Phase**: ACT (formalization enhanced with proved equivalence)

**Tractability Score**: 6/10
**Aristotle Suitable**: No (open conjecture, deep axioms)

## Tags

- erdos
- analysis
- polynomials
- harmonic-analysis

## Related Problems

- Problem #228 (flat Littlewood polynomials - SOLVED by BBMST 2019)
- Problem #230 (ultraflat unimodular polynomials - SOLVED by Kahane 1980)

## References

- [Ha74, Problem 4.31]
- [Va99, Problem 2.36]
- Balister-Bollobás-Morris-Sahasrabudhe-Tiba (2019)
- Kahane (1980)

## Sessions

### Session 1 (2026-03-11, researcher-5)

Initial formalization: definitions, conjecture statement, axiomatized known results.
208 lines, 5 axioms, 4 theorems, 1 sorry.

### Session 2 (2026-03-23, researcher-5)

**What Was Done:**
- Proved `conjecture_implies_no_ultraflat`: forward direction of equivalence
  (conjecture → no ultraflat Littlewood sequences) using Filter.Tendsto contradiction
- Replaced axiom `conjecture_equiv_no_ultraflat` with:
  - Proved theorem `conjecture_implies_no_ultraflat` (forward)
  - Axiom `no_ultraflat_implies_conjecture` (backward only)
  - Proved theorem `conjecture_equiv_no_ultraflat` (combines both)
- Updated summary theorem to include the equivalence
- 253 lines, 5 axioms, 7 theorems, 1 sorry

**Key Insights:**
- The forward direction is a clean filter contradiction: if supNorm > (1+c)√n
  eventually, then supNorm/√n can't tend to 1
- The backward direction genuinely requires countable choice / diagonal argument:
  if no c works, construct ultraflat sequence from witnesses for each 1/k
- The remaining sorry (bbmst_upper_bound_exists) requires ciSup_le for conditional
  supremum over the unit circle — technically involved but mathematically trivial

**Axiom Classification:**
1. `parseval_lower_bound` — Deep (requires Fourier analysis on unit circle)
2. `no_ultraflat_implies_conjecture` — Medium (needs diagonal argument + choice)
3. `bbmst_flat` — Deep (2019 breakthrough, probabilistic construction)
4. `kahane_unimodular_ultraflat` — Deep (1980, continuous phase optimization)
5. `rudin_shapiro_bound` — Medium (constructive but recursive bound proof)

**Next Steps:**
- Fix bbmst_upper_bound_exists sorry (needs ciSup handling for conditional supremum)
- Potentially prove no_ultraflat_implies_conjecture (diagonal argument)
- Consider whether Parseval can be proved from Mathlib integration theory

### Session 5 (2026-03-28, researcher-3)

**What Was Done:**
- **Proved `no_ultraflat_implies_conjecture`** — eliminated 1 axiom (5→4)
- Backward direction of equivalence: contrapositive diagonal extraction + squeeze
- Proof structure:
  1. by_contra: assume ¬Conjecture
  2. For each k, ¬Conjecture with c=1/(k+1) gives Frequently at atTop
  3. Filter.frequently_atTop.mp extracts witnesses with degree ≥ k
  4. choose gives sequences m(k), p(k)
  5. Degrees → ∞ via tendsto_atTop_atTop (m k ≥ k)
  6. Ratio → 1 via squeeze: parseval_ratio_ge_one ≤ ratio ≤ 1+1/(k+1)
  7. tendsto_of_tendsto_of_tendsto_of_le_of_le' closes the squeeze
- 327 lines, 4 axioms, 8 theorems, 0 sorries

**Key Insights:**
- No dependent choice needed: Filter.frequently_atTop gives ∃ m ≥ k directly
- parseval_ratio_ge_one (from session 4) was essential for the squeeze lower bound
- tendsto_one_div_add_atTop_nhds_zero_nat provides 1/(k+1) → 0 for squeeze upper bound

**Updated Axiom Classification:**
1. `parseval_lower_bound` — Deep (requires Fourier analysis on unit circle)
2. ~~`no_ultraflat_implies_conjecture`~~ — **PROVED** (session 5)
3. `bbmst_flat` — Deep (2019 breakthrough, probabilistic construction)
4. `kahane_unimodular_ultraflat` — Deep (1980, continuous phase optimization)
5. `rudin_shapiro_bound` — Medium (constructive, recursive bound proof)

**Next Steps:**
- Prove `rudin_shapiro_bound` (constructive: define Rudin-Shapiro polynomials, prove |P_k|²+|Q_k|²=2^{k+1})
- Consider whether `parseval_lower_bound` can be proved from Mathlib integration theory

---

*Updated by researcher-3 on 2026-03-28*

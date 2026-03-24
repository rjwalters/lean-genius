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

---

*Updated by researcher-5 on 2026-03-23*

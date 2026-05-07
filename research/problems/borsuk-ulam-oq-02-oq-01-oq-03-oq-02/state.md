# Current State

**Phase**: ORIENT
**Since**: 2026-05-08T01:30:00Z
**Iteration**: 3

## Current Focus

Phase-2 formalization is complete (1 axiom for the open conjecture, 0 sorries).
Iteration 3 (researcher-9) extended the lemma library with the quantitative
Bertrand-Chebyshev bound on `largestPrimeBelow` to formalize the
"factor-2-of-optimal" heuristic.

## Active Approach

Strengthen unconditional theorem coverage around the open axiom
`symBUDim_eq_largestPrime` so the boundary between proven content and the
open question is sharp. The conjecture itself requires Fadell-Husseini index
theory (not in Mathlib) so direct attack is out of scope; instead, we make
the surrounding facts increasingly precise.

## Blockers

The conjectural equality `symBUDim_eq_largestPrime` is genuinely open and
requires equivariant cohomology not currently in Mathlib (Fadell-Husseini
index for non-cyclic group actions). Direct proof is out of scope for this
file's scaffold.

## Next Action

Possible follow-ups:
1. Prove the n=4 case directly via the Klein-4 group structure (V₄ ≤ S₄)
   to confirm or refute the conjecture at the smallest non-trivial composite n.
2. Extend the explicit closed form past the even-d case (currently
   `symBUDim_even_formula` only handles d = 2k).
3. Add concrete unconditional bounds for S₆, S₇, S₈ analogous to
   `symBUDim_five_lower_unconditional`.
4. Formalize the dihedral analog (sister question OQ-02-OQ-01-OQ-03-OQ-01).

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 1 (Bertrand-derived quantitative refinement)

## Iteration 3 Builds (researcher-9, 2026-05-08)

- `n_div_two_lt_largestPrimeBelow` (axiom-free): for n ≥ 2,
  `n / 2 < largestPrimeBelow n`. Uses Mathlib's `Nat.exists_prime_lt_and_le_two_mul`.
- `largestPrimeBelow_in_bertrand_window` (axiom-free): two-sided bound
  `n/2 < largestPrimeBelow n ≤ n`.
- Updated meta.json: lineCount 187→241, theoremCount 8→10,
  substantiveTheoremCount 6→8, added Bertrand to mathlibDependencies.
- Added Bertrand bound to keyInsights, sections (Part VI), originalContributions.

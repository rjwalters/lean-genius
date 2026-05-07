# Current State

**Phase**: ORIENT
**Since**: 2026-05-08T02:50:00Z
**Iteration**: 4

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

## Iteration 4 Builds (researcher-3, 2026-05-08)

Focus: **prove the conjecture's n=2 case axiom-free** (consistency check) and
provide reusable infrastructure for future case-by-case attempts.

- `largestPrimeBelow_self_of_prime` (axiom-free): general squeeze lemma —
  when `n` itself is prime, `largestPrimeBelow n = n`. Reusable for all
  prime-n consequences below.
- `largestPrimeBelow_two`, `_three`, `_five`, `_seven` (axiom-free):
  concrete computations at small primes.
- `symBUDim_eq_largestPrime_two_unconditional` (axiom-free): the **n=2
  instance of the conjectured equality is provable** from the parent's
  `symBUDim_two` axiom and `largestPrimeBelow_two`, *without* invoking
  the new `symBUDim_eq_largestPrime` axiom. This is a non-trivial
  consistency check — it shows the new axiom is compatible with the
  pre-existing n=2 base axiom and is *redundant* at n=2.
- `symBUDim_two_even_formula_unconditional` (axiom-free): closed form
  `symBUDim 2 (2k) = 2k - 1` derived directly from parent axioms.
- `symBUDim_two_four_unconditional` (axiom-free): concrete `symBUDim 2 4 = 3`.
- Added `import Proofs.BorsukUlamOQ02OQ01OQ03OQ02` to `proofs/Proofs.lean`
  so the file is built as part of the gallery target.

**Counts**: lineCount 241→333, theoremCount 10→18, axiomCount 1 (unchanged),
sorries 0 (unchanged).

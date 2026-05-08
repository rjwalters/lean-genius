# Current State

**Phase**: ORIENT
**Since**: 2026-05-08T18:30:00Z
**Iteration**: 7

## Current Focus

Phase-2 formalization is complete (1 axiom for the open conjecture, 0 sorries).
Iteration 7 (researcher-11) added a uniform Z/2 lower bound `d − 1 ≤
symBUDim n d` valid at ALL dimensions (not just even) — strictly tighter than
`symBUDim_even_lower` at odd d. Combined with a generalized n=2 closed form,
the conjecture is now fully settled axiom-free at n=2 across all dimensions.

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
1. Prove the n=4 case directly via the Klein-4 group structure (V₄ ≤ S₄).
   The new uniform Z/2 bound `d − 1 ≤ symBUDim 4 d` is the best axiom-free
   lower bound at n=4; an improvement would have to come from V₄-specific
   non-cyclic structure. A full equivariant index calculation would either
   confirm (if V₄ ⊕ Z/3 contributes nothing extra) or refute (if it does)
   the conjecture at n=4.
2. Investigate odd-d cyclic-prime Yang-Borsuk axiom: `buDim_prime` only
   handles even d. An odd-d analog at odd primes would let
   `symBUDim_eq_largestPrime` derive a tight closed form past even d.
3. Formalize the dihedral analog (sister question OQ-02-OQ-01-OQ-03-OQ-01).

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1
- Approaches tried: 3 (Bertrand-derived quantitative refinement; structural
  fixed-point characterization; uniform Z/2 lower bound at all dimensions)

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

## Iteration 5 Builds (researcher-11, 2026-05-08)

Focus: **structural characterization** of `largestPrimeBelow` and **broaden
the unconditional lower-bound coverage** to S₆, S₇, S₈.

- `largestPrimeBelow_eq_self_iff_prime` (axiom-free): for n ≥ 2,
  `largestPrimeBelow n = n ↔ Nat.Prime n`. Forward direction uses
  `largestPrimeBelow_isPrime`; backward is `largestPrimeBelow_self_of_prime`.
  Cleaner than just having the prime → fixed-point direction.
- `largestPrimeBelow_lt_of_not_prime` (axiom-free): direct corollary —
  for composite n ≥ 2, `largestPrimeBelow n < n` (strict). Useful for
  case analyses that branch on primality.
- `symBUDim_six_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 6 (2k)`.
- `symBUDim_seven_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 7 (2k)`.
  (n=7 prime, parallels the n=5 case.)
- `symBUDim_eight_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 8 (2k)`.
  Notable: S₈ has the rich non-cyclic subgroup structure (V₄, A₄, …)
  cited in the problem statement. The cyclic-prime lower bound holds
  regardless — confirming `symBUDim_even_lower` is robust to S_n's
  composite/non-cyclic structure.

**Counts**: lineCount 333→387, theoremCount 18→23 (substantive 16→21),
axiomCount 1 (unchanged), sorries 0 (unchanged).

## Iteration 6 Builds (researcher-10, 2026-05-08)

Focus: **structural monotonicity** of `largestPrimeBelow` (S5 stretch goal)
and **further broadening of unconditional Yang-Borsuk lower bounds** through
n=12.

- `largestPrimeBelow_mono : Monotone largestPrimeBelow` (axiom-free):
  resolves S5's nextSteps[3]. Case split on n ≥ 2:
  - Positive (n ≥ 2): `largestPrimeBelow n` is itself a prime ≤ n ≤ m;
    apply `Nat.le_findGreatest` with the primality witness.
  - Negative (n < 2): `findGreatest Nat.Prime n = 0` (no prime ≤ 1);
    closed via `interval_cases` + `rfl` (n=0) + `decide` (n=1).
  Structurally aligns the new `symBUDim_eq_largestPrime` axiom with the
  parent file's `sym_has_smaller_sym n d` monotonicity in the n-variable.
- `largestPrimeBelow_eight_le_eleven` (axiom-free): concrete corollary
  pinning `largestPrimeBelow 8 ≤ 11` from monotonicity + value at 11.
- `symBUDim_nine_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 9 (2k)`.
- `symBUDim_ten_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 10 (2k)`.
- `symBUDim_eleven_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 11 (2k)`
  (n=11 prime).
- `symBUDim_twelve_lower_unconditional` (axiom-free): `2k - 1 ≤ symBUDim 12 (2k)`
  (n=12 highly composite — 2²·3, contains V₄ × Z/3, A₄, …).

All four extended bounds are direct applications of the existing
`symBUDim_even_lower`. The pattern is now uniformly demonstrated for
`n ∈ {3, …, 12}`, covering both prime cases (3, 5, 7, 11) and the full
range of composite cases including those with rich non-cyclic structure
(S₈, S₉, S₁₀, S₁₂).

**Counts**: lineCount 387→464 (+77), theoremCount 23→29 (substantive 21→27),
axiomCount 1 (unchanged), sorries 0 (unchanged).

**Build**: verified via `./proofs/scripts/docker-build.sh
Proofs.BorsukUlamOQ02OQ01OQ03OQ02` (128s for target file post Mathlib
cache; 3068 jobs total, 0 errors).

**PR**: #16890 (merged 2026-05-08T03:58:22Z).

## Iteration 7 Builds (researcher-11, 2026-05-08)

Focus: **uniform Z/2 lower bound at ALL dimensions** (including odd) and
**axiom-free closed form at n=2 generalized past even d**.

- `symBUDim_lower_z2` (axiom-free, core new theorem): for n ≥ 2 and d ≥ 1,
  `d − 1 ≤ symBUDim n d`. Routes through Z/2: parent's `symBUDim_two`
  + `buDim_two` + `symBUDim_le_of_le 2 n d`. Strictly tighter than
  `symBUDim_even_lower` at odd d (gives `d − 1 = 2k` at `d = 2k + 1`,
  whereas `symBUDim_even_lower` only delivers the floor-rounded `2k − 1`).
- `symBUDim_odd_lower_unconditional` (axiom-free corollary): for n ≥ 2,
  `2 * k ≤ symBUDim n (2 * k + 1)`. The strictly-stronger odd-d
  component of the Z/2 uniform bound.
- `symBUDim_two_general_unconditional` (axiom-free): for d ≥ 1,
  `symBUDim 2 d = d − 1`. Generalizes `symBUDim_two_even_formula_unconditional`
  past the even-d restriction. **At n=2 this fully settles the conjecture
  axiom-free across all dimensions** (combined with `largestPrimeBelow_two`,
  the conjectured equality `symBUDim 2 d = buDim (largestPrimeBelow 2) d`
  holds for all d ≥ 1 without invoking the new `symBUDim_eq_largestPrime`
  axiom).
- Concrete axiom-free instances:
  - `symBUDim_two_three_unconditional : symBUDim 2 3 = 2`
  - `symBUDim_two_five_unconditional : symBUDim 2 5 = 4`
  - `symBUDim_two_seven_unconditional : symBUDim 2 7 = 6`
  - `symBUDim_three_three_lower_unconditional : 2 ≤ symBUDim 3 3`
  - `symBUDim_four_three_lower_unconditional : 2 ≤ symBUDim 4 3` (V₄ ≤ S₄
    Klein-4 test case — Z/2 bound holds regardless of non-cyclic structure)
  - `symBUDim_three_five_lower_unconditional : 4 ≤ symBUDim 3 5`
  - `symBUDim_four_five_lower_unconditional : 4 ≤ symBUDim 4 5`

**Counts**: lineCount 530→674 (+144), theoremCount 35→45 (substantive
33→43), axiomCount 1 (unchanged), sorries 0 (unchanged).

**Build**: verified via `./proofs/scripts/docker-build.sh
Proofs.BorsukUlamOQ02OQ01OQ03OQ02` — `Build completed successfully (3068
jobs)` (clean except a pre-existing `unused variable hq` warning in
parent file `BorsukUlamOQ02OQ01.lean:111`, unrelated to S7 changes).

**Open content remaining**: the genuinely-open part of the new axiom is
now strictly `n ≥ 3` at odd `d ≥ 3` (whether S_n improves *past* the
uniform Z/2 bound `d − 1`). At `n = 2` the conjecture is fully axiom-free.

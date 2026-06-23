# Current State

**Phase**: ACT
**Since**: 2026-06-06T00:00:00Z
**Iteration**: 5

## Current Focus

S5 (researcher-1, 2026-06-06): ACT. Pin down what `WellSeparatedProducts`
implies (and does NOT imply) about the first element `a₀`, and convert
an in-file informal comment into a verified theorem.

Three new theorems:

1. `powers_of_two_not_well_separated` — counter-example formalizing the
   in-file comment that the geometric sequence `aₙ = 2^(n+1)` does NOT
   satisfy `WellSeparatedProducts`. Witness: `k = single 0 2`,
   `ℓ = single 1 1`, both yield product `4` so `|4 - 4| = 0 < 1`.
   Shows that `BeurlingPrimes` is genuinely restrictive — not just any
   geometric-style sequence works.
2. `primeSeq_zero : primeSeq 0 = 2` — proved by `Nat.nth_count`
   applied to `Nat.prime_two`, using `Nat.count Nat.Prime 2 = 0` (no
   primes are < 2). This is the first index-specific value for the
   actual-primes sequence in the file.
3. `beurling_a_zero_lower_bound_tight : ∃ bp, bp.a 0 = 2` — tightness
   of `beurling_a_zero_ge_two`. The witness is `actualPrimes`
   together with `primeSeq_zero`, establishing that `a₀ ≥ 2` cannot
   be strengthened to `a₀ ≥ 3` from the structure alone.

File grew 339 → 388 lines; theoremCount 15 → 18; 0 axioms, 0 sorries.

## Active Approach

Document the precise mathematical content of the structure axioms:
which constants are derivable, which are tight, and which are not.

- The lemma `beurling_a_zero_ge_two` establishes `a₀ ≥ 2`. The new
  tightness theorem proves this is the best possible absolute lower
  bound on `a₀` — any strengthening requires extra hypotheses.
- The counter-example (powers of 2 are not Beurling primes) gives a
  concrete, verifiable demonstration that the `WellSeparatedProducts`
  predicate is not automatic from naive constructions.

This complements Session 3 and Session 4's sharpened upper-bound chain
by mapping the *space of Beurling prime sequences*: actualPrimes
witnesses the lower envelope `a₀ = 2`; powers of 2 are excluded.

## Blockers

- The main conjecture (`erdos951_conjecture`) is OPEN and not pursued
  directly. Refining the trivial bound `⌊x⌋₊ - 1` to a sublinear
  bound (toward `π(x) ~ x/log x`) would require a density-increment
  argument that is out of scope for a single session.

## Next Action

Possible follow-ups (in increasing difficulty):

1. **Tightness of consecutive-gap bound**: show `beurling_consec_gap`
   (`aₙ₊₁ ≥ aₙ + 1`) is tight at `n = 0` for `actualPrimes`
   (`primeSeq 1 = 3 = 2 + 1`). Combined with Session 5's
   `primeSeq_zero`, this would pin down two index-specific values.

2. **Real-valued non-prime example**: construct an explicit Beurling
   prime sequence with `a₀ ≠ 2` (e.g., a transcendental). Existence
   is folklore (Beurling 1937), but a verified construction in Lean
   would map a second point in the parameter space.

3. **Integer-valued case**: For Beurling sequences with all
   `aᵢ ∈ ℕ`, prove that the sequence is uniquely determined by the
   first few elements (or by a multiplicative independence relation).

4. **Refine trivial bound by `log` factor**: Bridge from `⌊x⌋ - 1` to
   `x / (log log x)` — first genuinely sublinear bound. Requires a
   density-increment argument; multi-week project.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 1 (tightness + counter-example documentation)
- Approaches tried: 3 (axiom elimination, partial-bound theorem chain,
  parameter-space mapping)

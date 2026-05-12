# Problem: Euler's Converse — Every Even Perfect Number is Mersenne-Form

## Statement

### Plain Language
Euler (1747) proved the converse of Euclid's theorem on perfect numbers: every even
perfect number `n` must have the form `n = 2^k · (2^(k+1) - 1)` where `2^(k+1) - 1`
is a Mersenne prime. Combined with Euclid's direction, this gives a complete
characterization of even perfect numbers, leaving odd perfect numbers as a 2000-year
open problem.

This sub-slug targets the **Euler (⇒) direction specifically**, exposing the algebraic
skeleton — multiplicativity of σ on coprime factorizations + prime-power structure —
rather than invoking the Mathlib Archive's bundled proof as an opaque black box.

### Formal Statement
$$
\forall\, n \in \mathbb{N},\quad \text{Even}(n) \,\wedge\, n.\text{Perfect}
\;\Longrightarrow\;
\exists\, k \in \mathbb{N},\; \text{Prime}(2^{k+1} - 1) \,\wedge\, n = 2^k \cdot (2^{k+1} - 1).
$$

Equivalently: writing `n = 2^k · m` with `m` odd and `k ≥ 1`, the perfect equation
`σ(n) = 2n` forces `m = 2^(k+1) - 1` to be a Mersenne prime (and `m` has no proper
divisors strictly between `1` and `m`).

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - number-theory
  - perfect-numbers
  - arithmetic-functions
  - multiplicative
  - mersenne-primes
```

**Significance**: 7/10 — Classical millennia-spanning characterization; pedagogically valuable
to expose the σ-multiplicativity argument independently of the bundled proof.

**Tractability**: 6/10 — The bundled proof exists in Mathlib's Archive (≈150 lines);
decomposing it into 5–7 named sub-lemmas with explicit references is a focused refactor.

## Why This Matters

1. **Pedagogical exposition** — `Archive.Wiedijk100Theorems.PerfectNumbers` proves the
   bundled equivalence in `eq_two_pow_mul_prime_mersenne_of_even_perfect` via one dense
   block of algebra. A gallery-quality version with named intermediate lemmas
   (sigma-coprime split, prime-power identity, divisibility extraction, uniqueness step)
   makes the structure transparent.
2. **Reusable sub-lemmas** — The intermediate facts `σ(2^k) · σ(m) = 2^(k+1) · m` and
   `M_{k+1} | m` (where `M_{k+1} = 2^(k+1) - 1`) appear in many divisibility arguments;
   exposing them named is a small Mathlib API uplift.
3. **Open-problem stepping stone** — The same algebraic skeleton (sigma factorization
   + abundancy bounds) underlies all known constraints on odd perfect numbers.
   A clear formalization of the even case is a prerequisite for any future odd-case work.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `perfect-numbers` (`PerfectNumbers.lean`) | Parent — bundles both Euclid + Euler via Mathlib Archive |
| `sum-of-divisors` (`SumOfDivisors.lean`) | σ-arithmetic infrastructure (multiplicativity, prime powers) |
| `perfect-numbers-oq-03` (`PerfectNumbersOQ03.lean`) | Related sub-question (different framing) |

## Relationship to Existing Work

`PerfectNumbers.lean` line 107 contains `euler_even_perfect` which proves this statement
directly via `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`. The OQ-02
deliverable would be a *self-contained* pedagogical proof (S2+ scaffold) using the
named decomposition, NOT a re-wrapping of the bundled Archive lemma.

If the pedagogical scaffold is judged low-value (or duplicates the Archive's structure
too closely), this slug can be closed as "covered-by-parent" without further iteration.

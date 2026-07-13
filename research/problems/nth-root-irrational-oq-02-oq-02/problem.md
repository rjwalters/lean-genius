# Problem: Ergonomic k-th-root irrationality for mixed prime exponents

**Slug**: nth-root-irrational-oq-02-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Let `m ∈ ℕ`, `n ≥ 2`. If the prime factorization `m = ∏ pᵢ^{eᵢ}` has **some** exponent `eᵢ`
not divisible by `n`, then `m^{1/n}` is irrational:

$$
\big(\exists\, p \text{ prime},\ n \nmid v_p(m)\big)\ \Longrightarrow\ \sqrt[n]{m}\notin\mathbb{Q}.
$$

The specific gap: expose this ergonomically for radicands **all** of whose prime exponents are
`≥ 2` but not all divisible by `n` — e.g. `72 = 2³·3²` with `n = 2` (exponent `3` blocks it).

### Plain Language

The parent (`nth-root-irrational-oq-02`) gives a composite corollary that fires when some prime
divides the radicand to exponent *exactly* `1`. That is a convenient but narrow trigger: it
misses numbers like `72 = 2³·3²`, where every prime appears with exponent ≥ 2 yet `√72` is still
irrational (because `3` is not even). The goal is a criterion phrased on the `p`-adic valuation
`v_p(m) mod n`, so the "some exponent is not a multiple of `n`" case is directly usable.

### Why This Matters

The exponent-exactly-1 corollary is a special case of the real criterion (`n ∤ v_p(m)`). Stating
the general valuation criterion removes an artificial restriction and makes the result apply to
all the "obvious" irrational roots that the narrow corollary silently excludes. It is the honest,
complete form of the irrationality test.

## Known Results

### What's Already Proven

- Parent `nth-root-irrational-oq-02`: irrationality when a prime appears to exponent exactly 1.
- Base `nth-root-irrational`: the core `n`-th root irrationality argument.
- Mathlib `Nat.factorization`, `irrational_nrt_of_notint_nrt`, `Nat.Prime.factorization`.

### What's Still Open

- The valuation-based criterion `∃ p, n ∤ v_p(m) → Irrational (m^{1/n})`.
- An ergonomic phrasing / decision helper for concrete radicands like `72`.

### Our Goal

State and prove the `p`-adic valuation criterion, then verify it instantiates cleanly on
`72 = 2³·3²` (and similar mixed-exponent radicands) so the exponent-1 corollary becomes a
special case.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| nth-root-irrational-oq-02 | Direct parent; exponent-exactly-1 corollary | prime factorization |
| nth-root-irrational | Base result on `n`-th roots | valuation / factorization |
| factor-remainder-theorem-oq-06 | Alternative rational-root approach | rational root theorem |

## Initial Thoughts

### Potential Approaches

1. **Valuation contradiction**: if `m^{1/n} = a/b` in lowest terms then `m·bⁿ = aⁿ`, so
   `v_p(m) + n·v_p(b) = n·v_p(a)`, forcing `n ∣ v_p(m)` for every `p` — contradiction.
   - Why it might work: this is the standard clean argument and matches Mathlib valuation API.
   - Risk: reducing `Irrational` to the `∃ a b coprime` normal form tidily.

2. **Reduce to Mathlib `irrational_nrt_of_notint_nrt`**: show `m^{1/n}` is not an integer
   because integrality would force all `v_p(m)` divisible by `n`.
   - Why it might work: reuses the analytic core already in Mathlib.
   - Risk: converting the "not an integer" hypothesis from the valuation condition.

### Key Difficulties

- Manipulating `Nat.factorization` under `m·bⁿ = aⁿ` and extracting a single blocking prime.
- Choosing a criterion phrasing that is genuinely ergonomic (a `Decidable` helper on concretes).

### What Would a Proof Need?

- Key lemma 1: `v_p(m·bⁿ) = v_p(m) + n·v_p(b)` and `v_p(aⁿ) = n·v_p(a)`.
- Key lemma 2: existence of `p` with `n ∤ v_p(m)` contradicts the equality mod `n`.
- Technical requirements: `Nat.factorization` additivity, `Nat.factorization_pow`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The valuation argument is standard and the parent already handles the exponent-1 slice.
- Mathlib's `Nat.factorization` API supports additivity/`pow` cleanly.
- Similar irrationality-via-valuation proofs exist in Mathlib.

**Estimated Effort**:
- Exploration: hours
- If tractable: 2–4 days

## References

### Mathlib
- `Mathlib.Data.Nat.Factorization.Basic` — `Nat.factorization`, additivity, `factorization_pow`.
- `Mathlib.Data.Real.Irrational` — `irrational_nrt_of_notint_nrt`.
- `Mathlib.RingTheory.UniqueFactorizationDomain` — valuation infrastructure.

## Metadata

```yaml
tags:
  - number-theory
  - irrationality
  - generalization
  - prime-factorization
related_proofs:
  - nth-root-irrational-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10

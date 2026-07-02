# Problem: q-Binomial (Gaussian Binomial) Analogues of the Extended Binomial Identities

**Slug**: combinations-formula-oq-01-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- open question of the parent combinations-formula-oq-01 -->

## Problem Statement

### Formal Statement

$$
\binom{n}{k}_q = \frac{[n]_q!}{[k]_q!\,[n-k]_q!},\quad [m]_q! = \prod_{i=1}^m \frac{1-q^i}{1-q},
$$
$$
\text{q-Pascal: } \binom{n}{k}_q = \binom{n-1}{k-1}_q + q^k \binom{n-1}{k}_q,\qquad
\text{q-Vandermonde and the } q \to 1 \text{ limit recovering the classical identities.}
$$

### Plain Language

The parent entry collects extended binomial-coefficient identities (Pascal, Vandermonde, hockey-stick). This problem asks for the q-analogue: replace ordinary factorials by q-factorials to get Gaussian binomial coefficients, and prove the q-analogues of those identities — q-Pascal recurrences, the q-Vandermonde (Chu–Vandermonde) identity, and that each classical identity is recovered in the q → 1 limit.

### Why This Matters

Gaussian binomial coefficients count subspaces of vector spaces over finite fields and underlie q-series, quantum groups, and combinatorial statistics (inversions/major index). Formalizing the core q-identities and the q → 1 degeneration provides a reusable q-analogue toolkit and connects the gallery's combinatorics entries to Mathlib's `Nat`/polynomial q-binomial support.

## Known Results

### What's Already Proven

- Classical Pascal, Chu–Vandermonde, and hockey-stick identities — parent `combinations-formula-oq-01` and its siblings (`-oq-02` is the terminating Chu–Vandermonde, `-oq-04` is the LGV lemma).
- Mathlib has Gaussian binomial / q-factorial infrastructure to build on.

### What's Still Open (in the gallery)

- The q-Pascal recurrences (both forms).
- The q-Vandermonde identity.
- The q → 1 limit statements tying q-identities back to the classical ones.

### Our Goal

Define (or reuse) Gaussian binomial coefficients, prove the two q-Pascal recurrences and q-Vandermonde, and prove that specializing q = 1 recovers the classical identities already in the gallery.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| combinations-formula-oq-01 | Direct parent; classical identities being q-deformed | Pascal, Vandermonde, hockey-stick |
| combinations-formula-oq-01-oq-02 | Sibling: terminating Chu–Vandermonde (classical target of the q-version) | ₂F₁ summation |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Recurrence-first (recommended)**: define `qBinom n k` via the q-Pascal recurrence (or reuse Mathlib's), prove both recurrences by induction, then derive q-Vandermonde by induction on one argument. Get the q → 1 limit by evaluating the polynomial identity at q = 1 (`Polynomial.eval 1`), where `[m]_q → m`.
   - Why it might work: recurrences are induction-friendly and avoid division; working in `ℤ[q]` (polynomials) sidesteps field-of-fractions issues.
   - Risk: matching whichever convention Mathlib uses (`q^k` vs `q^{n-k}` factor placement).

2. **Approach B — Closed form over a field**: work in `ℚ(q)` with q-factorials directly.
   - Why it might work: mirrors the classical proofs closely.
   - Risk: division/nonvanishing side conditions.

### Key Difficulties

- Convention matching with Mathlib's Gaussian binomial definition.
- q → 1 specialization done as a polynomial evaluation rather than a real limit.

### What Would a Proof Need?

- Key lemma 1: both q-Pascal recurrences.
- Key lemma 2: q-Vandermonde by induction.
- Key lemma 3: `eval 1` degeneration to the classical identities.
- Technical requirements: `Polynomial`, Mathlib q-binomial API, induction.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- q-Pascal and q-Vandermonde are standard induction proofs; polynomial framing avoids analysis.
- Mathlib already provides Gaussian binomial scaffolding, so much is reuse.
- Among the strongest tractable targets in this batch.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days

## References

### Mathlib
- Gaussian binomial / q-factorial definitions (search `qBinomial`, `Nat.qFactorial`).
- `Mathlib.Algebra.Polynomial.Eval` — q → 1 specialization via `eval 1`.

## Metadata

```yaml
tags:
  - combinatorics
  - binomial-coefficients
  - q-analogue
  - gaussian-binomial
  - vandermonde
related_proofs:
  - combinations-formula-oq-01
  - combinations-formula-oq-01-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

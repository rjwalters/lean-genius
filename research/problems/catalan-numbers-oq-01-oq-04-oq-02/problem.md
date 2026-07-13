# Problem: Strict log-concavity of Catalan-derived sequences via the surplus method

**Slug**: catalan-numbers-oq-01-oq-04-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

For a derived sequence $a_n$ built from the Catalan numbers $C_n = \frac{1}{n+1}\binom{2n}{n}$ — for instance $a_n = C_n/(n+1)$ (the Catalan number divided by $n+1$) or a row/diagonal of the Catalan triangle — establish **strict** log-concavity:

$$
a_n^2 > a_{n-1}\,a_{n+1}, \qquad n \ge 1.
$$

### Plain Language

The parent proof shows the Catalan numbers themselves are log-concave using a "surplus" argument that compares $C_n^2$ with $C_{n-1}C_{n+1}$. This problem asks to apply the same method to sequences *derived* from the Catalan numbers and show the inequality is strict.

### Why This Matters

Log-concavity is a fundamental structural property (implies unimodality, real-rootedness heuristics, and total positivity connections). Showing the surplus method transfers to derived Catalan sequences broadens a verified technique and produces reusable inequalities.

## Known Results

### What's Already Proven

- Log-concavity of $C_n$ itself — parent proof `catalan-numbers-oq-01-oq-04` (verified) via the surplus method.
- The ratio recurrence $C_{n+1}/C_n = \frac{2(2n+1)}{n+2}$ — standard, gives $C_n$ in closed multiplicative form.
- $C_n = \binom{2n}{n} - \binom{2n}{n+1}$ and $C_n = \frac{1}{n+1}\binom{2n}{n}$.

### What's Still Open

- Strict log-concavity for the specific derived sequence(s) in this repo.
- Which derived sequence is cleanest to formalize first ($C_n/(n+1)$ vs a Catalan-triangle row).

### Our Goal

Pick one concrete derived sequence (recommended: $a_n = C_n/(n+1)$) and prove strict log-concavity $a_n^2 > a_{n-1}a_{n+1}$ for $n \ge 1$, reusing the surplus/ratio-comparison structure of the parent proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| catalan-numbers-oq-01-oq-04 | Parent: log-concavity of C_n by the surplus method | ratio comparison, induction |
| catalan-numbers-oq-01 | Catalan definitions and basic identities | binomial identities |

## Initial Thoughts

### Potential Approaches

1. **Ratio comparison**: Reduce $a_n^2 > a_{n-1}a_{n+1}$ to $\frac{a_n}{a_{n-1}} > \frac{a_{n+1}}{a_n}$ and show the ratio is strictly decreasing using the closed multiplicative form of $C_n$.
   - Why it might work: the $C_n$ ratio is a simple rational function of $n$; dividing by $(n+1)$ keeps it rational.
   - Risk: strictness bookkeeping and positivity of denominators.

2. **Direct surplus**: Mirror the parent's surplus quantity $a_n^2 - a_{n-1}a_{n+1}$ and show it is positive by `positivity`/`nlinarith` after clearing denominators.
   - Why it might work: fully algebraic once the closed form is substituted.
   - Risk: high-degree polynomial in $n$; may need `nlinarith` hints.

### Key Difficulties

- Handling the $1/(n+1)$ (and $1/(n+2)$) denominators cleanly — work over ℚ and `field_simp`.
- Proving strict (`<`) rather than weak (`≤`) inequality throughout.

### What Would a Proof Need?

- Key lemma 1: closed multiplicative form / ratio recurrence for $C_n$.
- Key lemma 2: monotonicity of the derived ratio $a_{n+1}/a_n$.
- Technical requirements: positivity of $C_n$, `field_simp`, `nlinarith`/`positivity`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Parent proof already formalizes the harder base case ($C_n$ log-concavity).
- Derived case is an algebraic transfer; no new theory needed.
- `nlinarith`/`positivity` handle polynomial-in-$n$ inequalities well.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Papers
- Stanley, *Enumerative Combinatorics* Vol. 2, Catalan addendum — log-concavity and unimodality.

### Online Resources
- OEIS A000108 — Catalan numbers; A009766 — Catalan triangle.

### Mathlib
- `Mathlib.Combinatorics.Catalan` — Catalan number definitions and recurrences.
- `nlinarith`, `positivity`, `field_simp` — inequality tactics.

## Metadata

```yaml
tags:
  - combinatorics
  - catalan-numbers
  - log-concavity
  - inequalities
related_proofs:
  - catalan-numbers-oq-01-oq-04
  - catalan-numbers-oq-01
difficulty: low
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 5/10
**Tractability**: 7/10

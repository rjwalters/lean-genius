# Problem: Nearest-Integer Characterization of the Subfactorial

**Slug**: derangements-convergence-oq-02-oq-01
**Created**: 2026-07-05T01:43:16-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $D(n)$ be the number of derangements of $n$ elements (the subfactorial
$!n$). Then $D(n)$ is exactly the nearest integer to $n!/e$:

$$
D(n) \;=\; \left\lfloor \frac{n!}{e} + \frac12 \right\rfloor
\qquad (n \ge 1),
$$

equivalently $\bigl| D(n) - n!/e \bigr| < \tfrac12$ for all $n \ge 1$.
This is obtained by upgrading the **sign law**

$$
\frac{D(n)}{n!} - e^{-1} \;=\; \sum_{j > n} \frac{(-1)^j}{j!}
\;=\; (-1)^{n}\,\varepsilon_n, \qquad 0 \le \varepsilon_n < \frac{1}{(n+1)!},
$$

so the signed error has sign $(-1)^n$ and magnitude $< 1/(n+1)!$. Multiplying
by $n!$ gives $|D(n) - n!/e| < n!/(n+1)! = 1/(n+1) \le \tfrac12$ for $n \ge 1$,
which forces $D(n) = \operatorname{round}(n!/e)$.

### Plain Language

The classic formula $D(n) = n!\sum_{k=0}^n (-1)^k/k!$ makes $D(n)/n!$ a partial
sum of the alternating series for $e^{-1}$. The truncation error is bounded by
the first omitted term, so $D(n)$ never differs from $n!/e$ by as much as $1/2$.
Hence the subfactorial is simply the closest integer to $n!/e$.

### Why This Matters

The "round$(n!/e)$" identity is the cleanest closed form for derangements and
is the standard textbook statement. Formalizing it turns the qualitative
convergence result ($D(n)/n! \to e^{-1}$) into a sharp, all-$n$, integer-valued
characterization, and exercises the alternating-series remainder API against
Mathlib's `Nat.derangements` / `numDerangements`.

## Known Results

### What's Already Proven

- `Nat.numDerangements` with the recurrence and the summation identity
  $D(n) = \sum_{k=0}^n (-1)^k n!/k!$ (Mathlib
  `Mathlib.Combinatorics.Derangements.Finite` / `...Exponential`).
- The convergence $D(n)/n! \to e^{-1}$ (parent gallery proof
  **derangements-convergence**, status: verified, badge: original, 0 axioms).
- Alternating series remainder bounds
  (`Mathlib.Analysis.SpecificLimits`, `alternating` lemmas).

### What's Still Open

- The explicit nearest-integer / rounding statement $D(n) = \operatorname{round}(n!/e)$.
- The precise $(-1)^n$ sign law with magnitude bound $< 1/(n+1)!$ as a
  standalone lemma.

### Our Goal

Prove $|D(n) - n!/e| < 1/2$ for $n \ge 1$ (from the alternating-tail bound),
and package it as a rounding identity. Optionally state the exact sign
$(-1)^n$ of the error.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| derangements-convergence | Direct parent; supplies $D(n)/n! \to e^{-1}$ | series limit |
| e-transcendental | Uses the $\sum 1/k!$ series for $e$ | exp series bounds |

## Initial Thoughts

### Potential Approaches

1. **Alternating-series remainder** (Approach A)
   - Write $D(n)/n! - e^{-1} = -\sum_{j>n}(-1)^{j-1}/j!$ and bound the tail by
     its first term $1/(n+1)!$.
   - Why it might work: Mathlib has alternating-series remainder lemmas; the
     tail bound is immediate.
   - Risk: connecting `Real.exp (-1)` to $\sum (-1)^k/k!$ in the right form.

2. **Direct rounding argument** (Approach B)
   - Combine $|D(n) - n!/e| < 1/(n+1) \le 1/2$ with the definition of
     `round` (`round_eq`, `abs_sub_round`).
   - Risk: casting between `ℕ`, `ℤ`, and `ℝ` when applying `round`.

### Key Difficulties

- Relating `Real.exp (-1)` to the alternating factorial series with the
  correct remainder sign.
- Real/nat casts around `round`.

### What Would a Proof Need?

- Key lemma 1: `numDerangements` summation identity (in Mathlib).
- Key lemma 2: alternating tail bound $|\sum_{j>n}(-1)^j/j!| < 1/(n+1)!$.
- Key lemma 3: `round` characterization from a $<1/2$ distance bound.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Mathlib already carries `numDerangements` and its exponential series link,
  plus alternating-series remainder machinery.
- The mathematics is a short, standard estimate; the work is Lean plumbing
  (series identity + tail bound + `round`).
- Parent proof is fully verified, so the series-limit groundwork exists.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–3 days
- If hard (cast/remainder friction): up to a week

## References

### Mathlib
- `Mathlib.Combinatorics.Derangements.Exponential` — $D(n)/n! \to e^{-1}$.
- `Mathlib.Combinatorics.Derangements.Finite` — `numDerangements` recurrence/sum.
- `Mathlib.Analysis.SpecificLimits.Basic` — alternating-series remainder.
- `Mathlib.Algebra.Order.Round` — `round`, `abs_sub_round`.

## Metadata

```yaml
tags:
  - combinatorics
  - derangements
  - analysis
related_proofs:
  - derangements-convergence
  - e-transcendental
difficulty: medium
source: gallery-gap
created: 2026-07-05T01:43:16-07:00
```

**Significance**: 6/10
**Tractability**: 7/10

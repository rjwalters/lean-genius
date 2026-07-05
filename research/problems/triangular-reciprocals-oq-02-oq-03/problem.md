# Problem: Alternating Gap-k Reciprocal Series (Catalan-type)

**Slug**: triangular-reciprocals-oq-02-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For an integer $k \ge 1$, evaluate the alternating gap-$k$ reciprocal series in closed form:

$$
\sum_{n=1}^{\infty} \frac{(-1)^{n+1}}{n(n+k)}
\;=\; \frac{1}{k}\Big(\text{a rational-linear combination of }\ln 2\text{ and finite alternating harmonic sums}\Big),
$$

obtained from the partial fraction $\frac{1}{n(n+k)} = \frac{1}{k}\left(\frac1n - \frac1{n+k}\right)$.

### Plain Language

The parent proved the *non-alternating* gap-$k$ telescoping identity
$\sum 1/(n(n+k)) = H_k/k$. This child inserts alternating signs. After partial
fractions the two pieces are alternating-harmonic tails, which resum to $\ln 2$ plus
an explicit finite correction. The result is a "Catalan-type" closed form (Catalan's
constant arises in the $1/(n(2n+1))$ analogue; here we get the $\ln 2$ family).

### Why This Matters

Completes the alternating branch of the triangular-reciprocals family, exhibiting how
sign changes convert a harmonic closed form ($H_k/k$) into a $\log$-based one. Good
exercise in conditionally convergent series and Mathlib's `Real.log` / alternating-series API.

## Known Results

### What's Already Proven

- Parent `triangular-reciprocals-oq-02`: $\sum_{n\ge1} 1/(n(n+k)) = H_k/k$ (gap-$k$ telescoping).
- Mathlib: alternating harmonic series $\sum (-1)^{n+1}/n = \ln 2$.
- Sibling alternating-series entries (Boole/Leibniz) for two-sided remainder bounds.

### What's Still Open (in this child)

- The exact closed form of $\sum (-1)^{n+1}/(n(n+k))$ for general $k$.
- Its identification with $\frac1k$ times a $\ln 2$ + finite-alternating-harmonic combination.

### Our Goal

Prove the closed form for general integer $k \ge 1$ via partial fractions + the
alternating harmonic series value $\ln 2$, handling the index shift $n \mapsto n+k$
that offsets the alternating tail by a finite (sign-adjusted) alternating harmonic sum.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| triangular-reciprocals-oq-02 | parent: non-alternating gap-k identity | telescoping, partial fractions |
| alternating-series-boole-oq-01 | alternating series / $\ln 2$ machinery | remainder bounds |
| geometric-series | resummation of shifted tails | HasSum manipulation |

## Initial Thoughts

### Potential Approaches

1. **Partial fractions + alternating harmonic value**: write the summand as
   $\frac1k\left(\frac{(-1)^{n+1}}n - \frac{(-1)^{n+1}}{n+k}\right)$. The first tail is $\ln 2$;
   the second is $\ln 2$ shifted by $k$, whose finite discrepancy is a signed finite
   alternating harmonic sum. Combine.
   - Why it might work: both pieces have known Mathlib `HasSum`/`tendsto` limits.
   - Risk: alignment of the alternating sign after the shift $n\to n+k$ (parity of $k$ flips sign).

2. **Abel summation / integral $\int_0^1 \frac{x^{?}}{1+x}$ representation**.
   - Why it might work: an integral form linearizes the alternation.
   - Risk: heavier analysis; prefer approach 1.

### Key Difficulties

- Conditional convergence: must use `HasSum` on the recombined (absolutely convergent) form
  $\frac{k}{n(n+k)}$ rather than term-by-term rearrangement of two conditional series.
- Sign bookkeeping under the $k$-shift.

### What Would a Proof Need?

- Alternating harmonic series limit $\sum (-1)^{n+1}/n = \ln 2$ (Mathlib).
- Partial-fraction identity and a shifted-tail lemma $\sum_{n} (-1)^{n+1}/(n+k)$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Same telescoping family the researchers have shipped repeatedly (oq-04-oq-01, oq-02-oq-04).
- The one new ingredient is the alternating harmonic value, which Mathlib provides.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Real.log_two` and alternating harmonic series lemmas — the $\ln 2$ value.
- `Finset.sum` partial-fraction manipulation; `HasSum` shift lemmas.

## Metadata

```yaml
tags:
  - analysis
  - series
  - telescoping
  - alternating-series
related_proofs:
  - triangular-reciprocals-oq-02
  - alternating-series-boole-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 7/10

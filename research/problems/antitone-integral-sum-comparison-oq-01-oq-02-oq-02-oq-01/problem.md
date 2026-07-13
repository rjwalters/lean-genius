# Problem: Identify generalizedEuler (fun x => 1/x) with the Euler–Mascheroni constant

**Slug**: antitone-integral-sum-comparison-oq-01-oq-02-oq-02-oq-01
**Created**: 2026-07-05T02:32:00-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent proof establishes, for an antitone nonneg summand $f$, that the
*generalized Euler constant*

$$
\gamma_f \;=\; \lim_{n\to\infty}\left(\sum_{k=1}^{n} f(k) \;-\; \int_1^{\,n} f(x)\,dx\right)
$$

exists. Specialize to $f(x) = 1/x$ and prove

$$
\gamma_{1/x} \;=\; \gamma \qquad\text{(the Euler–Mascheroni constant),}
$$

closing the loop with the classical constant via $\int_1^{\,1+n} \tfrac{1}{x}\,dx = \log(1+n)$.

### Plain Language

The parent theorem shows an abstract "gap constant" between a partial sum and its
integral converges for any antitone summand. This problem pins down the single most
important instance: when the summand is $1/x$, that abstract gap constant is exactly
the Euler–Mascheroni constant $\gamma \approx 0.5772$. The remaining work is an
*identification* — matching the abstractly-constructed limit to the concrete constant
(either Mathlib's `Real.eulerMascheroniConstant`, if present in the pinned toolchain,
or the standard definition $\gamma = \lim_n (H_n - \log n)$ with $H_n$ the harmonic number).

### Why This Matters

It converts a general existence result into a recognizable classical statement, and it
is the canonical worked example that makes the parent's abstract framework concrete and
citable. Bridging a bespoke construction to a named constant is exactly the kind of
"connect to the wider library" step that raises a formalization from an isolated lemma
to a reusable result.

## Known Results

### What's Already Proven

- Parent proof `antitone-integral-sum-comparison-oq-01-oq-02-oq-02` — existence of
  `generalizedEuler f` for antitone nonneg `f` (verified, 0 axioms).
- Classical: $H_n - \log n \to \gamma$; equivalently $\sum_{k=1}^n 1/k - \int_1^n dx/x \to \gamma$.

### What's Still Open

- The explicit identification `generalizedEuler (fun x => 1/x) = γ` is not yet formalized.
- Whether the pinned Mathlib exposes `Real.eulerMascheroniConstant` (or an equivalent
  `Real.eulerMascheroni…` / harmonic-limit lemma) must be confirmed as the OBSERVE step.

### Our Goal

Prove the single identity above. Scope is deliberately narrow: reuse the parent's
existence/limit machinery and reconcile the integral normalization ($\int_1^n$ vs
$\int_1^{1+n}$, giving $\log n$ vs $\log(1+n)$, which differ by $\log(1+1/n)\to 0$).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| antitone-integral-sum-comparison-oq-01-oq-02-oq-02 | Direct parent; supplies `generalizedEuler` and its convergence | integral test, monotone convergence, Riemann sums |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Reduce to the harmonic-log limit.**
   Rewrite `generalizedEuler (1/x)` as `lim (∑_{k=1}^n 1/k − ∫₁ⁿ dx/x) = lim (H_n − log n)`
   and identify with the target constant (Mathlib lemma if available, else the classical def).
   - Why it might work: the integral is elementary (`log n`), so the sum-minus-integral collapses to `H_n − log n`.
   - Risk: aligning the parent's exact index/endpoint conventions with the classical `H_n − log n`.

2. **Approach B — Definitional unfolding.**
   If Mathlib defines `eulerMascheroniConstant` as precisely this limit, the identity may be
   near-`rfl` after unfolding both sides to the same `Filter.Tendsto` witness.
   - Why it might work: minimal reconciliation if conventions match.
   - Risk: convention mismatch (open vs closed interval, `Nat` vs `Real` indexing) forces a `Tendsto` congruence argument.

### Key Difficulties

- Endpoint/normalization bookkeeping ($\int_1^n$ vs $\int_1^{1+n}$; $\log n$ vs $\log(1+n)$).
- Confirming the exact Mathlib name/shape of the Euler–Mascheroni constant in the pinned version.

### What Would a Proof Need?

- Key lemma 1: `∫₁ⁿ dx/x = log n` (Mathlib `integral_one_div` / `integral_inv`).
- Key lemma 2: uniqueness of limits to transport the parent's `Tendsto` to the classical one.
- Technical requirement: a `Tendsto` congruence bridging the two normalizations.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The heavy lifting (existence of the limit) is already done in the verified parent.
- The remaining step is an identification against a well-known elementary integral.
- Mathlib has strong support for `log`, `integral_inv`, harmonic sums, and `Tendsto` uniqueness.
- Main risk is bookkeeping, not deep mathematics.

**Estimated Effort**:
- Exploration: hours (locate the Mathlib constant / harmonic-limit lemma)
- If tractable: 1–3 days
- If hard: bounded — worst case is a hand-rolled `H_n − log n → γ` proof

## References

### Mathlib
- `Real.log`, `integral_inv` / `integral_one_div` — the elementary integral $\int_1^n dx/x = \log n$.
- `Real.eulerMascheroniConstant` (confirm availability in pinned toolchain) — the target constant.
- `Filter.Tendsto.unique` — transport between limit witnesses.

## Metadata

```yaml
tags:
  - analysis
  - euler-mascheroni
  - integral-test
  - generalized-euler-constant
  - convergence
related_proofs:
  - antitone-integral-sum-comparison-oq-01-oq-02-oq-02
difficulty: medium
source: gallery-gap
created: 2026-07-05T02:32:00-07:00
```

**Significance**: 5/10
**Tractability**: 7/10

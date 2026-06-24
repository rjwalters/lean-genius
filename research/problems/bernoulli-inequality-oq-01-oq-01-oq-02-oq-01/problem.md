# Problem: Magnitude-bounded power band |x| ≤ B ⟹ −Bⁿ ≤ xⁿ ≤ Bⁿ

**Slug**: bernoulli-inequality-oq-01-oq-01-oq-02-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For real $x$ and $B \ge 0$ with $|x| \le B$, and $n \in \mathbb{N}$,
$$
-B^{n} \;\le\; x^{n} \;\le\; B^{n}.
$$
Moreover characterize, for a line $x \mapsto c\,x$ (or affine family), exactly when it eventually escapes the $n$-dependent band $B^{n}$, with the threshold governed by the trichotomy $B < 1$, $B = 1$, $B > 1$.

### Plain Language

The parent "line-escapes-a-bounded-power lemma" pins a power $x^n$ inside a fixed band when the base is bounded. This leaf makes the band **base-dependent**: if $|x| \le B$ then $x^n$ lies in $[-B^n, B^n]$. The interesting part is the qualitative behavior as $n$ grows: the band $B^n$ shrinks ($B<1$), is constant ($B=1$), or grows ($B>1$), and this controls whether a competing linear term can "escape" the band.

### Why This Matters

A small, reusable building block for asymptotic/Archimedean arguments: bounding monomials by a bounded base and reasoning about which terms dominate as the exponent grows. Useful in convergence proofs and inequality libraries.

## Known Results

### What's Already Proven

- Parent `bernoulli-inequality-oq-01-oq-01-oq-02` — the line-escapes-a-bounded-power lemma (fixed band).
- Mathlib: `pow_le_pow_left`, `abs_pow`, `pow_le_one`, `one_le_pow`, `pow_lt_one`, monotonicity of `n ↦ B^n` for $B$ in the three regimes.

### What's Still Open

- The two-sided $-B^n \le x^n \le B^n$ form as a named lemma.
- The escape characterization tied to the $B<1 / =1 / >1$ trichotomy.

### Our Goal

Prove the two-sided band bound and state/prove the trichotomy governing band growth, in clean axiom-free Lean.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bernoulli-inequality-oq-01-oq-01-oq-02 | Parent: fixed-band escape lemma | bounded-power bounds |
| bernoulli-inequality-oq-01-oq-01 | Bernoulli inequality core | induction on exponent |

## Initial Thoughts

### Potential Approaches

1. **Approach A — `abs_pow` + `pow_le_pow_left`**: From $|x| \le B$ get $|x^n| = |x|^n \le B^n$, which unfolds to the two-sided bound.
   - Why it might work: direct, uses standard Mathlib monotonicity.
   - Risk: minimal; mostly `simp`/`gcongr` bookkeeping.

2. **Approach B — induction on $n$**: Prove the band bound by induction, then derive the trichotomy from `pow` monotonicity lemmas.
   - Why it might work: keeps the escape analysis self-contained.
   - Risk: the escape statement needs a careful eventual-behavior formulation (`Filter.Eventually` / `Tendsto`).

### Key Difficulties

- Formulating the "escape" characterization crisply (eventual vs. pointwise).
- Handling $B = 0$ / degenerate cases.

### What Would a Proof Need?

- Key lemma 1: $|x| \le B \Rightarrow |x|^n \le B^n$.
- Key lemma 2: monotone behavior of $n \mapsto B^n$ in each regime.
- Technical requirements: possibly `Filter.atTop` for the eventual escape statement.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The core two-sided bound is a short Mathlib derivation.
- The trichotomy uses standard `pow` monotonicity lemmas.
- The only design choice is how to phrase the escape characterization.

**Estimated Effort**:
- Exploration: 1–2 hours
- If tractable: 1 day
- If hard: unknown (only if the escape statement is over-engineered)

## References

### Mathlib
- `Mathlib.Algebra.Order.Monoid.Lemmas` / `Mathlib.Algebra.GroupPower.Order` — `pow_le_pow_left`, `abs_pow`, `pow_le_one`, `one_le_pow`.

## Metadata

```yaml
tags:
  - analysis
  - inequality
  - bounded-power
  - archimedean
related_proofs:
  - bernoulli-inequality-oq-01-oq-01-oq-02
  - bernoulli-inequality-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```

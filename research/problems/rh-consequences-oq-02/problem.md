# Problem: Prime Gap Bound Conditional on the Riemann Hypothesis

**Slug**: rh-consequences-oq-02
**Created**: 2026-07-04T19:56:31-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\mathsf{RH} \;\Longrightarrow\; p_{n+1} - p_n = O\!\left(\sqrt{p_n}\,\log p_n\right)
$$

where $p_n$ is the $n$-th prime. Equivalently, assuming the Riemann Hypothesis,
every interval $[x, x + C\sqrt{x}\log x]$ contains a prime for $x$ large.

### Plain Language

Consecutive primes cannot be too far apart if the Riemann Hypothesis holds. The
best unconditional gap bounds are much weaker (e.g. $O(p_n^{0.525})$), but under
RH the classical Cramér bound gives a gap of order $\sqrt{p_n}\log p_n$. We want
to formalize this conditional implication in Lean 4: from an RH hypothesis on the
zeros of $\zeta$, derive the explicit gap bound.

### Why This Matters

This is one of the flagship *consequences* of RH and extends the parent gallery
entry `rh-consequences`, which packages RH-conditional results. Formalizing the
prime-gap consequence exercises the "error term in the prime counting function"
mechanism: RH controls $|\psi(x) - x| = O(\sqrt{x}\log^2 x)$, and the gap bound
falls out. It is a clean, self-contained conditional theorem — no need to prove
RH itself, only to use it as a hypothesis.

## Known Results

### What's Already Proven

- Under RH, $\psi(x) = x + O(\sqrt{x}\log^2 x)$ (von Koch 1901) — the explicit
  error term for the Chebyshev function.
- Cramér (1919): RH $\Rightarrow p_{n+1} - p_n = O(\sqrt{p_n}\log p_n)$.
- Parent entry `rh-consequences` — the RH-conditional scaffolding this builds on.

### What's Still Open

- Unconditionally, the gap is only known to be $O(p_n^{0.525})$ (Baker–Harman–Pintz).
- Cramér's *conjecture* $p_{n+1}-p_n = O(\log^2 p_n)$ is far beyond RH and stays open.

### Our Goal

Formalize the implication: given RH stated as "all nontrivial zeros of $\zeta$
have real part $1/2$" (or, more usefully for the argument, the von Koch error
bound as a hypothesis), derive $p_{n+1} - p_n = O(\sqrt{p_n}\log p_n)$. The
cleanest scope takes the von Koch explicit error bound as the RH input and proves
the gap bound from it, so the formalization is genuinely about the gap deduction.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| rh-consequences | Parent: RH-conditional results container | Conditional theorems, zeta zeros |
| prime-number-theorem | Chebyshev $\psi$, prime counting asymptotics | Explicit error terms |

## Initial Thoughts

### Potential Approaches

1. **Via the explicit von Koch bound**: Take $|\psi(x) - x| \le C\sqrt{x}\log^2 x$
   as the RH input. Then $\psi(x + h) - \psi(x) \ge h - 2C\sqrt{x}\log^2 x > 0$
   for $h = C'\sqrt{x}\log x$ once $x$ is large, forcing a prime in the interval.
   - Why it might work: the deduction is short, elementary real analysis.
   - Risk: getting the log powers and constants to line up in Lean's `Asymptotics`.

2. **Directly from zero location**: Derive the error term from the explicit
   formula inside Lean.
   - Why it might work: fully self-contained from RH.
   - Risk: the explicit formula for $\psi$ is not in Mathlib; very heavy.

### Key Difficulties

- Mathlib has limited analytic number theory around $\psi(x)$ and no explicit
  formula, so approach 1 (von Koch bound as hypothesis) is far more realistic.
- Bookkeeping with `Asymptotics.IsBigO` and `Filter.atTop` for the log factors.

### What Would a Proof Need?

- Key lemma 1: An RH-hypothesis form of $|\psi(x) - x| = O(\sqrt{x}\log^2 x)$.
- Key lemma 2: $\psi(x+h) - \psi(x) > 0 \Rightarrow$ a prime lies in $(x, x+h]$.
- Technical requirements: real-analysis growth comparisons and `IsBigO` algebra.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The deductive step from von Koch's bound is genuinely short.
- The obstacle is the missing analytic-number-theory layer in Mathlib; scoping
  the RH input as the von Koch error bound (hypothesis) keeps the work bounded.
- The result will legitimately carry an `axiom`/hypothesis for the RH error bound,
  so `status: axiomatized` is expected.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks
- If hard: unknown (building the explicit formula in Lean)

## References

### Papers
- von Koch, "Sur la distribution des nombres premiers", *Acta Math.* 24 (1901) — explicit error term under RH.
- Cramér, "Some theorems concerning prime numbers", *Ark. Mat. Astr. Fys.* (1919) — the gap bound.

### Online Resources
- Wikipedia, "Prime gap" — statement of the RH-conditional bound and context.

### Mathlib
- `Mathlib.NumberTheory.*` — Chebyshev functions, `Nat.Prime`, prime-counting scaffolding.
- `Mathlib.Analysis.Asymptotics.Asymptotics` — `IsBigO` for the error-term algebra.

## Metadata

```yaml
tags:
  - number-theory
  - riemann-hypothesis
  - prime-gaps
  - analytic-number-theory
related_proofs:
  - rh-consequences
  - prime-number-theorem
difficulty: high
source: proof-suggestion
created: 2026-07-04T19:56:31-07:00
```

**Significance**: 7/10
**Tractability**: 4/10

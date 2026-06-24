# Problem: Catenary Arc Length via the arsinh Substitution

**Slug**: arsinh-log-formula-oq-01-oq-01-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\int_0^b \sqrt{1 + t^2}\,\mathrm{d}t \;=\; \tfrac{1}{2}\Bigl(b\sqrt{1+b^2} + \operatorname{arsinh} b\Bigr),
\qquad b \ge 0,
$$

equivalently, with $\operatorname{arsinh} b = \log\bigl(b + \sqrt{1+b^2}\bigr)$,

$$
\int_0^b \sqrt{1 + t^2}\,\mathrm{d}t \;=\; \tfrac{1}{2}\,b\sqrt{1+b^2} + \tfrac{1}{2}\log\bigl(b + \sqrt{1+b^2}\bigr).
$$

### Plain Language

The graph of the hyperbolic cosine (a hanging chain, or *catenary*) has an arc length that, after the standard reduction, is governed by the integral of $\sqrt{1+t^2}$. This problem asks for a fully machine-checked closed form for that integral on $[0,b]$. The natural route is the substitution $t = \sinh u$, under which $\sqrt{1+t^2} = \cosh u$ and the integrand becomes $\cosh^2 u = \tfrac12(1+\cosh 2u)$, integrating to the stated half-sum of an algebraic term and an $\operatorname{arsinh}$ term.

### Why This Matters

This is the canonical "capstone" application of the parent entry's antiderivative of $1/\sqrt{1+x^2}$: it closes the loop from the derivative side (arsinh as an antiderivative) to the dual integral $\int\sqrt{1+x^2}$ that appears in every arc-length and surface-area computation involving hyperbolic geometry. It also exercises Mathlib's `Real.arsinh`/`Real.sinh`/`Real.cosh` API together with the fundamental theorem of calculus, providing a reusable lemma for catenary, parabola, and conic arc-length entries.

## Known Results

### What's Already Proven

- Parent `arsinh-log-formula-oq-01-oq-01` (verified): the antiderivative identity for $1/\sqrt{1+x^2}$ and the logarithmic form $\operatorname{arsinh} x = \log(x+\sqrt{1+x^2})$.
- Mathlib: `Real.arsinh`, `Real.sinh`, `Real.cosh`, `Real.cosh_sq`, `Real.sinh_arsinh`, `Real.cosh_arsinh`, and `Real.arsinh` differentiability lemmas.
- Mathlib: `intervalIntegral.integral_eq_sub_of_hasDerivAt` (FTC-2) for evaluating the integral once an antiderivative is exhibited.

### What's Still Open

- A Lean statement and proof of $\int_0^b \sqrt{1+t^2}\,\mathrm{d}t = \tfrac12(b\sqrt{1+b^2} + \operatorname{arsinh} b)$.
- The bridge to the literal catenary arc length $\int_0^b \cosh u\,\mathrm{d}u$ form, if desired as a corollary.

### Our Goal

Define the antiderivative $F(x) = \tfrac12\bigl(x\sqrt{1+x^2} + \operatorname{arsinh} x\bigr)$, prove $F'(x) = \sqrt{1+x^2}$ by differentiation (product rule plus the known derivative of arsinh), and conclude via FTC-2 that the definite integral equals $F(b) - F(0) = F(b)$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| arsinh-log-formula-oq-01-oq-01 | Direct parent; arsinh antiderivative and log form | hyperbolic calculus, FTC |
| arsinh-log-formula-oq-01 | Root entry; defining identity for arsinh | inverse hyperbolic functions |

## Initial Thoughts

### Potential Approaches

1. **Exhibit the antiderivative and apply FTC-2.** Set $F(x) = \tfrac12(x\sqrt{1+x^2} + \operatorname{arsinh} x)$, show `HasDerivAt F (sqrt (1+x^2)) x` via the product/chain rules, then `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
   - Why it might work: every ingredient (derivative of arsinh, derivative of $x\sqrt{1+x^2}$) is in Mathlib; the algebra $F'=\sqrt{1+x^2}$ reduces to a `field_simp`/`ring` identity after clearing $\sqrt{1+x^2}>0$.
   - Risk: managing the $\sqrt{1+x^2}$ denominators and the positivity side-goals; `Real.sqrt` derivative bookkeeping.

2. **Substitution $t = \sinh u$ directly.** Change variables to reduce to $\int_0^{\operatorname{arsinh} b}\cosh^2 u\,\mathrm{d}u$ and use $\cosh^2 = \tfrac12(1+\cosh 2u)$.
   - Why it might work: mirrors the textbook derivation closely.
   - Risk: Mathlib's change-of-variables (`intervalIntegral.integral_comp_smul_deriv` and friends) is more bookkeeping-heavy than the direct antiderivative route.

# Problem: Continuous (Integral) Chebyshev Sum Inequality for Monotone Functions

**Slug**: chebyshev-sum-inequality-oq-01-oq-03
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

If $f, g : [a,b] \to \mathbb{R}$ are both monotone in the same direction (both nondecreasing or both nonincreasing), then

$$
\frac{1}{b-a}\int_a^b f(x)g(x)\,\mathrm{d}x
\;\ge\;
\left(\frac{1}{b-a}\int_a^b f(x)\,\mathrm{d}x\right)\!\left(\frac{1}{b-a}\int_a^b g(x)\,\mathrm{d}x\right),
$$

with the inequality reversed when $f$ and $g$ are oppositely monotone. This is the integral analogue of the discrete Chebyshev sum inequality proved in the parent entry.

### Plain Language

Chebyshev's sum inequality says that if two sequences are sorted the same way, the average of their termwise products is at least the product of their averages (and at most, if sorted oppositely). This problem asks for the continuous version: replace sequences by similarly-monotone functions on an interval and sums by integrals. The averaged form makes the statement scale-free. The standard proof multiplies out the manifestly nonnegative double integral $\iint (f(x)-f(y))(g(x)-g(y))\,\mathrm{d}x\,\mathrm{d}y \ge 0$.

### Why This Matters

The integral Chebyshev inequality is a workhorse in analysis and probability (it is the "same-monotonicity correlation" inequality, a cousin of the FKG and Chebyshev's correlation inequalities, and underlies rearrangement bounds). Extending the gallery's discrete result to the continuous setting gives a reusable lemma for moment inequalities, variance bounds, and expectation-of-product estimates over continuous distributions.

## Known Results

### What's Already Proven

- Parent `chebyshev-sum-inequality-oq-01` (verified): the discrete (averaged) Chebyshev sum inequality for similarly/oppositely ordered finite sequences.
- Mathlib: `MeasureTheory.integral`, `intervalIntegral`, monotonicity-of-integral lemmas, and the Tonelli/Fubini machinery (`MeasureTheory.integral_integral_swap`) needed for the double-integral identity.
- Classical: the $\iint (f(x)-f(y))(g(x)-g(y)) \ge 0$ proof and its expansion into four integrals.

### What's Still Open

- A Lean statement and proof of the integral Chebyshev inequality for monotone $f, g$ on $[a,b]$, plus the reversed form for opposite monotonicity.
- Integrability hypotheses packaged cleanly (e.g. `IntervalIntegrable` for monotone-hence-bounded functions).

### Our Goal

Prove $(b-a)\int_a^b fg \ge \bigl(\int_a^b f\bigr)\bigl(\int_a^b g\bigr)$ from the nonnegativity of $\iint_{[a,b]^2}(f(x)-f(y))(g(x)-g(y))\,\mathrm{d}x\,\mathrm{d}y$, expanded via Fubini into the four single integrals.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chebyshev-sum-inequality-oq-01 | Direct parent; discrete Chebyshev sum inequality | rearrangement, ordered sequences |
| chebyshev-sum-inequality-oq-01 (root family) | Averaged forms and ordering hypotheses | monotone sequences |

## Initial Thoughts

### Potential Approaches

1. **Nonnegative double integral via Fubini.** Show the integrand $(f(x)-f(y))(g(x)-g(y))$ is pointwise $\ge 0$ for similarly monotone $f,g$, integrate over $[a,b]^2$, and expand with `integral_integral_swap` into $2(b-a)\int fg - 2(\int f)(\int g)$.
   - Why it might work: the pointwise sign is immediate from same-direction monotonicity; Fubini expansion is mechanical.
   - Risk: integrability/measurability side-goals and the product-measure bookkeeping in Mathlib's Fubini.

2. **Discretize and pass to the limit.** Apply the parent's discrete inequality to Riemann sums and take the limit.
   - Why it might work: directly reuses the parent result.
   - Risk: limit interchange and uniform integrability arguments are heavier than the direct double-integral route.

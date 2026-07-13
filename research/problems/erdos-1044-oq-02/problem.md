# Problem: Exact Value of Λ(zⁿ − 1) as a Function of n

**Slug**: erdos-1044-oq-02
**Created**: 2026-07-09T17:03:07-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\Lambda(z^n - 1) \;=\; \max_{C}\ \operatorname{length}(\partial C), \qquad
C \text{ a connected component of } \{z \in \mathbb{C} : |z^n - 1| < 1\}.
$$

The open question is: give a **closed-form expression for the function** $n \mapsto \Lambda(z^n - 1)$ for all $n \ge 1$. It is known that

$$
\Lambda(z^n - 1) \longrightarrow 2 \quad \text{as } n \to \infty, \qquad \text{and} \qquad \Lambda(z^n - 1) > 2 \ \ \text{for every } n,
$$

but no exact formula is known. The conjecture is that the exact value is expressible through **complete elliptic integrals** of a modulus depending on $n$.

### Plain Language

The polynomial $z^n - 1$ has its $n$ roots equally spaced on the unit circle (the $n$th roots of unity). The region where $|z^n - 1| < 1$ breaks into $n$ identical "petals," one around each root. We want the length of the boundary of one petal (equivalently of the largest component), written as an explicit function of $n$. We already know this length shrinks toward $2$ as $n$ grows, but we do not have a formula that produces the exact length for each fixed $n$ — and there is evidence the honest answer requires elliptic integrals rather than elementary functions.

### Why This Matters

Erdős Problem #1044 (parent proof `erdos-1044`, resolved by Quanyu Tang) establishes that $\inf_f \Lambda(f) = 2$ over all polynomials with roots in the closed unit disk, using the family $z^n - 1$ to approach the infimum. That result is *asymptotic*: it tells us the limit but not the rate or the exact per-$n$ values. Pinning down $\Lambda(z^n - 1)$ exactly would (i) quantify how fast the infimum is approached, (ii) give the first exact metric formula for a natural family of polynomial lemniscates, and (iii) test Tang's conjecture that $z^n - 1$ is the per-degree minimizer of $\Lambda$. Lemniscate boundary lengths connect to potential theory, transfinite diameter, and the classical study of polynomial level sets initiated by Erdős, Herzog and Piranian (1958).

## Known Results

### What's Already Proven

- **Asymptotic value** $\Lambda(z^n - 1) \to 2$ and the strict bound $\Lambda(f) > 2$ for all $f$ — Tang's theorem, formalized in the parent proof `erdos-1044` (`Proofs/Erdos1044Problem.lean`, axioms `maxBoundaryLength`, `tang_infimum_eq_two`).
- **Degree-1 baseline** $\Lambda(z - z_0) = 2\pi$ for $|z_0| \le 1$ (the sublevel set is a unit disk), recorded in the parent proof's source (Part IV).
- **Structure of the sublevel set**: $\{|z^n - 1| < 1\}$ has $n$-fold rotational symmetry and consists of $n$ congruent petals; the maximizing component is any single petal, so $\Lambda(z^n - 1)$ equals the perimeter of one petal.
- **Arc-length integral representation**: on the boundary $|z^n - 1| = 1$ the length is $\oint |dz|$ over one petal, an elementary curvilinear integral that can be reduced by the substitution $w = z^n$ to an integral over the circle $|w - 1| = 1$ pulled back through the $n$-fold cover.

### What's Still Open

- No closed-form for $\Lambda(z^n - 1)$ as a function of $n$ is known; the value for general $n$ has not been reduced to named special functions.
- Whether the exact value genuinely requires **elliptic integrals** (as conjectured) or admits an elementary/hypergeometric closed form is unresolved.
- The precise **rate** of convergence $\Lambda(z^n - 1) - 2 \sim c\,n^{-\alpha}$ (constant $c$ and exponent $\alpha$) is not rigorously established.

### Our Goal

Derive and, where possible, formalize an exact expression for $\Lambda(z^n - 1)$: reduce the petal perimeter to an explicit arc-length integral via $w = z^n$, evaluate that integral in closed form (aiming at a complete elliptic integral of a modulus depending on $n$), and confirm the resulting formula reproduces the known limit $2$ and the degree-1 value $2\pi$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1044 | Parent problem: defines $\Lambda$, proves $\inf \Lambda = 2$ using $z^n - 1$; this open question asks for the exact per-$n$ value | Complex analysis, potential theory, lemniscate geometry, axiomatized boundary-length function |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Change of variables $w = z^n$**: The map $z \mapsto w = z^n$ sends one petal of $\{|z^n - 1| < 1\}$ near $z = 1$ to the disk $\{|w - 1| < 1\}$, an $n$-to-1 cover branched at the origin. Parametrize $w - 1 = e^{i\theta}$ on the boundary and pull back to $z = (1 + e^{i\theta})^{1/n}$; then $\Lambda(z^n - 1) = \oint |dz|$ over the appropriate $\theta$-range. Expanding $|dz|^2 = |z'(\theta)|^2 d\theta^2$ yields an integrand of the form $\frac{1}{n}\,|1 + e^{i\theta}|^{1/n - 1}\,d\theta$, whose exact integral is the target.
   - Why it might work: reduces a 2D geometric quantity to a single explicit 1D integral with an algebraic integrand — exactly the shape that produces elliptic integrals after a Weierstrass/half-angle substitution.
   - Risk: the branch structure near $z = 0$ (where petals meet for the connected-component definition) must be handled carefully; also the integrand's $1/n$ exponent makes closed-form evaluation delicate.

2. **Approach B — Asymptotic expansion first, then guess the exact form**: Compute $\Lambda(z^n - 1)$ numerically for many $n$, fit $\Lambda(z^n-1) = 2 + c\,n^{-\alpha} + \dots$, then compare against candidate elliptic-integral formulas $4\,E(k_n)$ / $2\pi\,{}_2F_1(\cdot)$ to identify the modulus $k_n$.
   - Why it might work: high-precision numerics plus the inverse-symbolic approach (comparing to $K$, $E$, AGM values) frequently reveals the exact special function; the known limit $2$ and value $2\pi$ at $n=1$ strongly constrain candidates.
   - Risk: numerics can match multiple closed forms; without the exact integral (Approach A) a fit is suggestive, not a proof.

### Key Difficulties

- The integrand carries a fractional exponent $1/n$, so a *single* uniform closed form over all $n$ (rather than a case analysis) is hard to obtain.
- Distinguishing "genuinely elliptic" from "hypergeometric that happens to reduce" requires either an exact evaluation or a rigorous transcendence/period argument.
- The parent proof axiomatizes $\Lambda$ (`maxBoundaryLength`), so any Lean formalization of an exact value must first give a *computable* arc-length definition consistent with that axiom.

### What Would a Proof Need?

- Key lemma 1: the maximal component of $\{|z^n-1|<1\}$ is a single petal, and its perimeter equals the explicit $\theta$-integral from Approach A.
- Key lemma 2: evaluation of that integral as a complete elliptic integral $E(k_n)$ (or hypergeometric ${}_2F_1$) with an identified modulus $k_n$, plus verification that $k_n \to$ (limit giving $\Lambda \to 2$) and $n=1$ gives $2\pi$.
- Technical requirements: rigorous handling of the branch point at $z=0$, Mathlib support for arc length of a parametrized curve and for elliptic integrals / special functions.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The core reduction (Approach A) is classical and mechanical, so obtaining *an* exact integral is quite feasible; but proving it equals a *named* special function in closed form, uniformly in $n$, is genuinely hard and may be why the problem remains open.
- Similar exact-perimeter problems (ellipse perimeter, lemniscate arc length of Bernoulli's $|z^2-1|=c$) are precisely the historical origin of elliptic integrals, which supports the conjecture but also signals the difficulty.
- Mathlib currently has strong support for complex analysis and integration but limited support for elliptic integrals, so a full formal proof of the exact value is out of immediate reach; a formalized *integral representation* (Approach A up to Lemma 1) is more attainable.

**Estimated Effort**:
- Exploration: 3-5 days (derive the integral, run high-precision numerics, identify candidate special function).
- If tractable: 2-4 weeks to a rigorous closed form for special cases (small $n$) or an asymptotic expansion with error bounds.
- If hard: unknown — a uniform exact formula in named special functions may require new special-function identities.

## References

### Papers
- P. Erdős, F. Herzog, G. Piranian, "Metric properties of polynomials", J. Analyse Math. 6 (1958), 125-148 — origin of the study of polynomial lemniscate lengths and root distributions.
- Q. Tang, resolution of Erdős Problem #1044 (see erdosproblems.com/1044) — proves $\inf_f \Lambda(f) = 2$ using the $z^n - 1$ family; the parent of this question.

### Online Resources
- https://erdosproblems.com/1044 — official statement, status ("solved"), and references for Erdős Problem #1044.
- https://dlmf.nist.gov/19 — DLMF chapter on elliptic integrals ($K$, $E$, and Legendre/Weierstrass forms) for identifying the conjectured closed form.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — the complex exponential / unit circle, for parametrizing the boundary and the roots of unity.
- `Mathlib.Analysis.Calculus.ParametricIntegral` and `Mathlib.MeasureTheory.Integral.IntervalIntegral` — arc-length as a parametric interval integral of $|z'(\theta)|$.
- `Mathlib.Analysis.SpecialFunctions.Pow.Complex` — complex powers $(1 + e^{i\theta})^{1/n}$ arising from the change of variables $w = z^n$.

## Metadata

```yaml
tags:
  - complex-analysis
  - polynomials
  - level-sets
  - boundary-length
  - erdos
related_proofs:
  - erdos-1044
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:03:07-07:00
```

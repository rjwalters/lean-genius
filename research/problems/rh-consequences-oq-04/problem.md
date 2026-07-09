# Problem: Hadamard Product Factorization of the Riemann Zeta Function via the Completed Zeta ξ

**Slug**: rh-consequences-oq-04
**Created**: 2026-07-09T15:23:00-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $\xi(s) = \tfrac{1}{2} s(s-1)\,\pi^{-s/2}\,\Gamma(s/2)\,\zeta(s)$ be the completed Riemann zeta function (Riemann's ξ; up to the elementary prefactors this is Mathlib's `completedRiemannZeta` $\Lambda(s)$, related by $\xi(s) = \tfrac{1}{2}s(s-1)\Lambda(s)$). Then $\xi$ is an **entire function of order 1** and finite type, and by the Hadamard factorization theorem it admits the product representation

$$
\xi(s) \;=\; e^{A + Bs}\ \prod_{\rho}\left(1 - \frac{s}{\rho}\right) e^{s/\rho},
$$

where the product ranges over the non-trivial zeros $\rho$ of $\zeta$ (equivalently, all zeros of $\xi$), $A = \log \xi(0) = -\log 2$, and $B = -\sum_{\rho} \operatorname{Re}(1/\rho) = \tfrac{1}{2}\log(4\pi) - 1 - \tfrac{\gamma}{2}$. Because $\xi$ has order exactly 1, the canonical (genus-1) product with the convergence factors $e^{s/\rho}$ converges, and equivalently $\sum_{\rho} |\rho|^{-1-\varepsilon} < \infty$ for every $\varepsilon > 0$ while $\sum_{\rho} |\rho|^{-1} = \infty$.

### Plain Language

The Riemann zeta function $\zeta(s)$ can be "packaged" into a symmetric completed function $\xi(s)$ whose only zeros are exactly the non-trivial zeros of $\zeta$ (the ones RH is about). This $\xi$ is an entire function — no poles, defined everywhere — and it grows no faster than roughly $e^{|s|\log|s|}$, which makes it an *order-1* entire function. A classical theorem of Hadamard says any entire function of finite order can be written as an exponential factor times an explicit infinite product over its zeros. Applying this to $\xi$ expresses $\xi(s)$ (hence essentially $\zeta(s)$) as a product running over its non-trivial zeros $\rho$, each contributing a factor $(1 - s/\rho)e^{s/\rho}$. This is the analytic bridge that turns statements about the *location of zeros* into statements about *prime counting*.

### Why This Matters

The Hadamard product is the engine behind almost every deep result about the distribution of primes. It is the identity from which the **explicit formula** (von Mangoldt's formula relating $\psi(x)$ to a sum over zeros $\rho$) is derived: taking the logarithmic derivative of the product turns $\zeta'/\zeta$ into a sum over $\rho$, and Perron's formula then converts that into the prime-counting error term. Every RH-conditional prime bound in the parent gallery proof — $\psi(x) = x + O(\sqrt{x}\log^2 x)$, the $O(\sqrt{x})$ Mertens bound, the $O(\sqrt{x}\log x)$ error in $\pi(x)$ — ultimately rests on the convergence properties of this product. It also pins down the density of zeros (Riemann–von Mangoldt $N(T) \sim (T/2\pi)\log(T/2\pi e)$) via Jensen's formula applied to the order-1 factorization. Formalizing the order-1 Hadamard product would let several axioms in `rh-consequences` be *derived* rather than assumed.

## Known Results

### What's Already Proven

- Functional equation of the completed zeta: $\Lambda(s) = \Lambda(1-s)$ — Mathlib `completedRiemannZeta_one_sub`, re-exported as `xi_functional_equation` in the parent proof `rh-consequences`.
- Analytic continuation and the pole structure of $\zeta$ (simple pole at $s=1$, residue 1) — Mathlib `Mathlib.NumberTheory.LSeries.RiemannZeta`, `riemannZeta_residue_one`.
- Non-vanishing of $\zeta$ for $\operatorname{Re}(s) \ge 1$ and the Euler product for $\operatorname{Re}(s) > 1$ — `riemannZeta_ne_zero_of_one_le_re`, `riemannZeta_eulerProduct_tprod` (both used in `rh-consequences`).
- The Riemann–von Mangoldt zero-counting asymptotic and the Hadamard-product zero structure are *stated* but axiomatized in the parent proof (`riemann_von_mangoldt_formula`, `hadamard_product_exists`; see Parts 30–31 "Hadamard Product, Zero Structure").
- Classical mathematics: Hadamard's factorization theorem for entire functions of finite order, and Jensen's formula, are standard textbook results (Titchmarsh, Edwards).

### What's Still Open

- No formalization of the general Hadamard factorization theorem for entire functions of finite order exists in current Mathlib (Weierstrass canonical products with genus-$p$ convergence factors are not yet available).
- The specific order-1 growth estimate for $\xi$ — i.e. $\log|\xi(s)| = O(|s|\log|s|)$ — is not formalized.
- Convergence of $\sum_\rho |\rho|^{-1-\varepsilon}$ (the order-1 exponent-of-convergence bound) is not formalized.
- The evaluation of the constants $A = -\log 2$ and $B$ in terms of the Euler–Mascheroni constant is not formalized.

### Our Goal

Formalize the statement and proof that **$\xi(s) = \tfrac{1}{2}s(s-1)\Lambda(s)$ is an entire function of order at most 1**, and derive from a (formalized or carefully axiomatized) Hadamard factorization theorem the product representation $\xi(s) = e^{A+Bs}\prod_\rho (1-s/\rho)e^{s/\rho}$. Concretely: (1) prove $\xi$ is entire (removing the trivial-zero poles of $\Gamma(s/2)$ and the pole of $\zeta$ at $s=1$); (2) establish the order-1 growth bound; (3) state the Hadamard product and prove convergence of the canonical genus-1 product from the order bound. Formalizing (1)–(2) is the realistic first milestone; (3) may initially remain a well-motivated axiom until Weierstrass products land in Mathlib.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| rh-consequences | Parent proof; already states `hadamard_product_exists` and the ξ functional equation as axioms/theorems — this problem discharges the Hadamard axiom | Completed zeta ξ, functional equation, Selberg class, explicit formula |
| riemann-hypothesis | ξ has exactly the non-trivial zeros of ζ; RH is a statement about the zeros appearing in this very product | Mathlib `RiemannHypothesis`, critical line, ζ zero structure |
| prime-number-theorem | The explicit formula derived from the Hadamard product yields the PNT error term via the logarithmic derivative $\zeta'/\zeta$ | Zero-free region, Perron's formula, contour integration |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Entirety and order bound first, product axiomatized**: Prove $\xi$ is entire by cancelling the $\Gamma(s/2)$ poles (at $s=0,-2,-4,\dots$) against the trivial zeros of $\zeta$ and the pole of $\zeta$ at $s=1$ against the factor $(s-1)$, using Mathlib's `completedRiemannZeta` (which already absorbs $\pi^{-s/2}\Gamma(s/2)\zeta(s)$ and is entire away from $s\in\{0,1\}$). Then bound $|\xi(s)|$ via Stirling for $\Gamma$ and the convexity/Phragmén–Lindelöf bounds for $\zeta$ in the critical strip to get order $\le 1$. State the Hadamard product itself as a clean interface lemma.
   - Why it might work: Mathlib already has `completedRiemannZeta`, its analytic continuation, the functional equation, and a Stirling/`Gamma` asymptotic API; entirety reduces to pole/zero bookkeeping that Mathlib supports.
   - Risk: The order-1 growth bound needs uniform estimates on $\zeta$ in the critical strip (Phragmén–Lindelöf), which may not be directly available and could be the hardest analytic piece.

2. **Approach B — Build the general Hadamard/Weierstrass machinery**: Formalize Weierstrass canonical products $E_p(z)$ and the Hadamard factorization theorem for entire functions of finite order (Jensen's formula → counting zeros → convergence of $\sum |\rho|^{-\rho_{\text{ord}}-\varepsilon}$ → genus-$p$ product), then instantiate at $p=1$ for $\xi$.
   - Why it might work: It is the mathematically correct, reusable path and would benefit all of analytic number theory in Mathlib; Jensen's formula and Blaschke-type product convergence are within reach of Mathlib's complex analysis.
   - Risk: Substantial infrastructure (canonical products, genus, order/type, exponent of convergence) — a multi-week to multi-month effort; high chance of scope blow-up.

### Key Difficulties

- Establishing the uniform order-1 growth bound $\log|\xi(s)| = O(|s|\log|s|)$ requires Stirling asymptotics for $\Gamma$ together with polynomial-in-$t$ bounds on $\zeta(\sigma+it)$ across the critical strip (Phragmén–Lindelöf), which is delicate to formalize.
- Convergence of the canonical product needs the exponent-of-convergence estimate $\sum_\rho |\rho|^{-1-\varepsilon} < \infty$, which in turn depends on the zero-counting bound $N(T) = O(T\log T)$ — itself currently axiomatized in the parent proof.
- Bridging Mathlib's `completedRiemannZeta` $\Lambda$ (which is $\pi^{-s/2}\Gamma(s/2)\zeta(s)$ with its own pole conventions) to the symmetric entire $\xi = \tfrac12 s(s-1)\Lambda$ requires careful handling of the removable singularities at $s=0$ and $s=1$.

### What Would a Proof Need?

- Key lemma 1: $\xi(s) := \tfrac12 s(s-1)\,\Lambda(s)$ extends to an entire function (removable singularities at $s=0,1$), with $\xi(0)=\xi(1)=\tfrac12$ and $\xi(s)=\xi(1-s)$.
- Key lemma 2: Growth bound $|\xi(s)| \le \exp(C|s|\log|s|)$ for $|s|$ large, giving order $\rho_{\mathrm{ord}}(\xi) \le 1$; combined with a lower bound, order exactly 1.
- Key lemma 3: Exponent of convergence: $\sum_\rho |\rho|^{-1-\varepsilon} < \infty$ for all $\varepsilon>0$ (from $N(T)=O(T\log T)$), and $\sum_\rho |\rho|^{-1} = \infty$.
- Key lemma 4 (Hadamard interface): an entire function of order $\le 1$ with these zeros equals $e^{A+Bs}\prod_\rho (1-s/\rho)e^{s/\rho}$; identify $A,B$ via $\xi(0)$ and $\xi'(0)/\xi(0)$.
- Technical requirements: Stirling for `Complex.Gamma`, Phragmén–Lindelöf convexity bounds for $\zeta$, Jensen's formula, and (for the full result) Weierstrass canonical products.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full order-1 Hadamard factorization requires complex-analysis infrastructure (Weierstrass canonical products, Hadamard's theorem, exponent of convergence) that is **not yet in Mathlib**, so a complete formalization is a large undertaking.
- The realistic milestone — proving $\xi$ is entire and bounding its order — is more tractable because Mathlib already provides `completedRiemannZeta`, its functional equation, analytic continuation, and a `Complex.Gamma` API with Stirling-type asymptotics; this reduces much of the work to pole/zero bookkeeping plus one hard growth estimate.
- Comparable formalizations (the PrimeNumberTheoremAnd project's contour-integral and zero-free-region work) show these estimates are achievable but labor-intensive; the parent proof already isolates the relevant axioms, giving a clear target interface.
- Mathlib modules available: `Mathlib.NumberTheory.LSeries.RiemannZeta`, `Mathlib.NumberTheory.LSeries.HurwitzZetaEven` (completed even Hurwitz/Riemann zeta), `Mathlib.Analysis.SpecialFunctions.Gamma.*`, and `Mathlib.Analysis.Analytic.*`.

**Estimated Effort**:
- Exploration: 2–4 days to map the Mathlib `completedRiemannZeta` and `Gamma` APIs and pin down the exact growth-bound statement.
- If tractable (entirety + order bound, product as interface axiom): 2–4 weeks.
- If hard (full Hadamard/Weierstrass machinery): unknown, plausibly multi-month.

## References

### Papers
- Bernhard Riemann, "Über die Anzahl der Primzahlen unter einer gegebenen Grösse", 1859 — introduces ξ and its product/zero structure.
- Jacques Hadamard, "Étude sur les propriétés des fonctions entières et en particulier d'une fonction considérée par Riemann", Journal de Mathématiques Pures et Appliquées, 1893 — the factorization theorem for entire functions of finite order, applied to ξ.
- E. C. Titchmarsh (rev. D. R. Heath-Brown), "The Theory of the Riemann Zeta-Function", 2nd ed., 1986 — Chapter 2 develops the order of ξ and the Hadamard product with the constants A, B.
- Harold M. Edwards, "Riemann's Zeta Function", 1974 — Chapter 1–2 give a detailed derivation of the product and the explicit formula from it.

### Online Resources
- The PrimeNumberTheoremAnd formalization project (Lean 4 / Mathlib) — https://github.com/AlexKontorovich/PrimeNumberTheoremAnd — contour-integration and zero-free-region infrastructure relevant to ξ growth bounds.

### Mathlib
- `Mathlib.NumberTheory.LSeries.RiemannZeta` — `completedRiemannZeta` (Λ), analytic continuation, functional equation `completedRiemannZeta_one_sub`, pole/residue data.
- `Mathlib.NumberTheory.LSeries.HurwitzZetaEven` — the even completed Hurwitz zeta construction underlying `completedRiemannZeta`.
- `Mathlib.Analysis.SpecialFunctions.Gamma.Basic` / `.Beta` / Stirling lemmas — `Complex.Gamma`, its poles, and asymptotic bounds needed for the order estimate.
- `Mathlib.Analysis.Analytic.Basic` and `Mathlib.Analysis.SpecialFunctions.Complex.*` — entireness, `tprod` infinite products, and complex-analytic tools for the canonical product.

## Metadata

```yaml
tags:
  - number-theory
  - analytic-number-theory
  - riemann-hypothesis
  - complex-analysis
  - entire-functions
related_proofs:
  - rh-consequences
  - riemann-hypothesis
  - prime-number-theorem
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:23:00-07:00
```

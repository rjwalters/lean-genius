# Problem: Infinitely Divisible Distributions in Lean

**Slug**: central-limit-theorem-oq-03-oq-02
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

A probability measure $P$ on $\mathbb{R}$ is **infinitely divisible** if for every $n \geq 1$ there exists a probability measure $Q_n$ such that:
$$P = Q_n^{*n} \quad \text{(n-fold convolution of } Q_n \text{ with itself)}$$

The **Lévy-Khintchine theorem** characterizes all infinitely divisible distributions: $P$ is infinitely divisible if and only if its characteristic function $\hat{P}(t) = \int e^{itx} dP(x)$ has the form:
$$\log \hat{P}(t) = i\mu t - \frac{\sigma^2 t^2}{2} + \int_{\mathbb{R}} \left(e^{itx} - 1 - itx \cdot \mathbf{1}_{|x| \leq 1}\right) d\nu(x)$$
where $\mu \in \mathbb{R}$, $\sigma \geq 0$, and $\nu$ is a Lévy measure (a Borel measure with $\nu(\{0\}) = 0$ and $\int \min(1, x^2) d\nu(x) < \infty$).

### Plain Language

A distribution is infinitely divisible if it can be split into arbitrarily many identical independent pieces. The Gaussian, Poisson, Cauchy, and Gamma distributions are all infinitely divisible. The Lévy-Khintchine theorem gives a complete classification via a triple $(μ, σ², ν)$.

The goal is to formalize the class of infinitely divisible distributions within the convolution monoid framework of `central-limit-theorem-oq-03`, and prove key properties — ideally the Lévy-Khintchine characterization or at minimum:
1. Closure under convolution
2. Gaussian and Poisson are infinitely divisible
3. The class is closed under weak limits
4. A counterexample (Bernoulli(1/2) is not infinitely divisible)

### Why This Matters

Infinitely divisible distributions are the building blocks of Lévy processes (continuous-time processes with stationary independent increments). The Lévy-Khintchine theorem is foundational to modern probability theory and connects:
- The CLT (Gaussian is the archetype)
- Poisson processes
- Stable distributions
- Mathematical finance (option pricing, jump processes)

Within the gallery, this extends `central-limit-theorem-oq-03` which already formalizes the convolution monoid structure and has the CLT as a fixed-point result. Infinitely divisible distributions are the "divisible elements" of that monoid.

## Known Results

### What's Already Proven

- `central-limit-theorem-oq-03`: Commutative monoid structure of `ProbMeasure` under convolution, `convPow_add`, Cramér's theorem (Gaussian is prime/indecomposable), CLT as convergence
- Mathlib: `IsProbabilityMeasure`, `MeasureTheory.Measure.dirac`, `MeasureTheory.Measure.MeasureSpace`
- The parent has 14 axioms including `convolution`, `convolution_assoc`, etc.

### What's Still Open

- No Lean formalization of `InfinitelyDivisible` predicate exists in Mathlib (as of Mathlib 4.26.0)
- Lévy-Khintchine representation is not formalized
- Characteristic functions for probability measures have limited Mathlib support

### Our Goal

Minimum viable: Define `InfinitelyDivisible` as a predicate on `ProbMeasure`, prove closure under convolution, and exhibit both a positive example (Gaussian) and a negative example.

Stretch goal: Formalize the Lévy-Khintchine triple and prove the easy direction (any distribution with a Lévy-Khintchine triple is infinitely divisible).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `central-limit-theorem-oq-03` | Parent — convolution monoid, `convPow_add`, Cramér | Monoid algebra, axiomatized CLT |
| `central-limit-theorem` | Base CLT formalization | Probability, measure theory |
| `central-limit-theorem-oq-04` | CLT extensions | Characteristic functions |
| `central-limit-theorem-oq-01-oq-02` | Stable distributions | Stable laws |

## Initial Thoughts

### Potential Approaches

1. **Definitional approach** (most tractable): Define `InfinitelyDivisible P` as `∀ n : ℕ, n > 0 → ∃ Q : ProbMeasure ℝ, convPow Q n = P`, prove it's closed under convolution, prove Dirac measure is infinitely divisible, sketch Gaussian.
   - Why it might work: Uses existing `convPow` from parent proof; purely algebraic
   - Risk: `convPow` is axiomatized in parent — need to use it consistently

2. **Characteristic function route**: Define infinitely divisible via `∀ n, ∃ Q, charFun Q = (charFun P) ^ (1/n)`, use `charFun_convPow` axiom from parent.
   - Why it might work: Connects to parent's `charFun` machinery
   - Risk: Nth roots of complex-valued functions are delicate

3. **Examples-first**: Prove Poisson(λ) = convPow(Poisson(λ/n), n) directly, proving at least one positive instance.
   - Why it might work: Concrete, avoids abstract machinery
   - Risk: Requires Poisson distribution definition in Lean

### Key Difficulties

- Convolution infrastructure in parent is axiomatized (not definition-based), limiting what can be proved purely formally
- Characteristic functions for measure-theoretic probability are complex to set up
- Nth roots of characteristic functions require complex analysis

### What Would a Proof Need?

- Key lemma 1: `InfinitelyDivisible_mul`: If P and Q are infinitely divisible, so is P * Q (convolution)
- Key lemma 2: `infinitelyDivisible_dirac`: `dirac 0` is infinitely divisible (trivially: Q = dirac 0)
- Key lemma 3: `infinitelyDivisible_gaussian`: Gaussian(μ, σ²) is infinitely divisible
- Technical: The Poisson distribution needs to be in scope, or an abstract existence proof via characteristic functions

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The definition is straightforward given parent's `convPow` axiom
- Proving basic closure properties doesn't require the full Lévy-Khintchine theorem
- The Lévy-Khintchine representation itself is hard — not realistic for a single research cycle
- The parent's axiomatized convolution might limit what can be formally derived
- Partial result (definition + examples) is achievable; full classification is a moonshot

**Estimated Effort**:
- Exploration (OBSERVE/ORIENT): 1 day
- Minimal viable result: 2-3 days
- Lévy-Khintchine: Multiple weeks, likely requires extending Mathlib

## References

### Papers
- Lévy, P. (1925) — *Calcul des probabilités* — original infinite divisibility concept
- Khintchine, A.Ya. (1937) — *Degenerate Distributions and the Law of Large Numbers* — Lévy-Khintchine formula
- Sato, K.-I. (1999) — *Lévy Processes and Infinitely Divisible Distributions* — standard reference

### Mathlib
- `Mathlib.MeasureTheory.Measure.MeasureSpace` — probability measures
- `Mathlib.MeasureTheory.Measure.Dirac` — Dirac delta
- `Mathlib.Analysis.Fourier.FourierTransform` — characteristic functions (if available)
- `Proofs/CentralLimitTheoremOQ03.lean` — parent proof with convolution monoid

## Metadata

```yaml
tags:
  - probability
  - infinitely-divisible
  - levy-processes
  - convolution
  - characteristic-functions
related_proofs:
  - central-limit-theorem-oq-03
  - central-limit-theorem
  - central-limit-theorem-oq-01-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 6/10

# Problem: de Moivre-Laplace CLT via Moment Generating Function

**Slug**: binomial-theorem-oq-03-oq-01
**Created**: 2026-04-22T14:37:37+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

**OQ-01 of binomial-theorem-oq-03**: Can the de Moivre-Laplace CLT be proved
using the algebraic MGF approach?

$$\text{Bin}(n,p) \xrightarrow{d} \mathcal{N}(np,\, np(1-p))$$

Formally: for $X_n \sim \text{Bin}(n,p)$,
$$\frac{X_n - np}{\sqrt{np(1-p)}} \xrightarrow{d} \mathcal{N}(0,1)$$

The MGF approach: $M_{X_n}(t) = (1-p+pe^{t/\sqrt{np(1-p)}})^n \to e^{t^2/2}$
as $n \to \infty$, which is the MGF of $\mathcal{N}(0,1)$.

### Plain Language

The parent entry `binomial-theorem-oq-03` proves that the binomial distribution
Bin(n,p) has mean np and variance np(1-p) using purely algebraic manipulation
of the generating function $(p + (1-p))^n = 1$. The open question is: can the
same algebraic approach, via the moment generating function, yield a proof of
the de Moivre-Laplace theorem — that normalized binomials converge to Gaussian?

The MGF of Bin(n,p) is $(1-p+pe^t)^n$. After standardization (shift by np,
scale by $\sqrt{np(1-p)}$), the MGF becomes $(1-p+pe^{t/\sqrt{n p(1-p)}})^n$.
The key limit: $(1 + t^2/(2n) + O(t^3/n^{3/2}))^n \to e^{t^2/2}$, which is
the MGF of N(0,1). MGF convergence implies distributional convergence.

### Why This Matters

- Connects the algebraic binomial-distribution theory to CLT formalization
- Mathlib has substantial probability theory (ProbabilityTheory.*)
- Formalizing the de Moivre-Laplace special case provides stepping stone
  toward the general CLT
- No duplicate in gallery — new mathematical content for the project

## Known Results

### What's Already Proven in the Gallery

- **binomial-theorem-oq-03** (verified, 0 sorries): Bin(n,p) has mean np,
  variance np(1-p), Vandermonde convolution, Poisson limit theorem.
  File: `Proofs/BinomialTheoremOQ03.lean`
- The limit $(1+x/n)^n \to e^x$ is proved in that file (used for Poisson limit)
- Mathlib: `MeasureTheory.ProbabilityMeasure`, `ProbabilityTheory.variance`

### Mathlib Resources

- `Mathlib.Probability.Distributions.Binomial` — binomial random variables
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv` — `Real.exp` derivatives
- `Mathlib.MeasureTheory.Function.L2Space` — L2 convergence
- `Mathlib.Topology.Algebra.InfiniteSum` — series/summation
- `Mathlib.Analysis.MeanInequalities` — moment bounds

### What's Still Open

- A full formalization of the de Moivre-Laplace theorem in Lean 4
- Connection from MGF convergence to distributional convergence in Mathlib

### Our Goal

Formalize either:
1. **(Preferred)** The MGF proof: show $M_{X_n}(t) \to e^{t^2/2}$
2. **(Alternative)** A direct characteristic function proof using
   Mathlib's Fourier analysis

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `binomial-theorem-oq-03` | Parent: Bin(n,p) statistics algebraically | Generating functions |
| `central-limit-theorem-oq-03-oq-02` | Related CLT formalization work | Probability theory |
| `birthday-problem-oq-03-oq-01-oq-02-oq-01` | Probability/Poisson approximation | Approx methods |

## Initial Thoughts

### Potential Approaches

1. **MGF Convergence** (recommended):
   - Compute MGF of standardized Bin(n,p): $(1-p+pe^{t/\sqrt{npq}})^n$
   - Expand $pe^{t/\sqrt{npq}} = p(1 + t/\sqrt{npq} + t^2/(2npq) + O(n^{-3/2}))$
   - Show $\log MGF(t) \to t^2/2$ as $n \to \infty$
   - Apply continuity theorem for MGFs
   - Risk: Mathlib's MGF convergence → distributional convergence may be limited

2. **Characteristic Function (Fourier)** approach:
   - Use `MeasureTheory.Fourier` and Levy's continuity theorem
   - Characteristic function of Bin(n,p): $(1-p+pe^{it})^n$
   - After standardization: pointwise convergence to $e^{-t^2/2}$
   - Risk: Levy's theorem may not be in Mathlib yet

3. **Stirling's Approximation** (classical):
   - Directly bound $\binom{n}{k}p^k(1-p)^{n-k}$ for $k \approx np + x\sqrt{npq}$
   - Use $\log \binom{n}{k} \approx n H(\hat{p})$ (entropy approximation)
   - Risk: Tedious but elementary; Stirling's formula is in Mathlib

### Key Difficulties

- Distributional convergence infrastructure in Mathlib (weak convergence)
- MGF → distribution equivalence theorem in Lean 4
- Controlling error terms in the Taylor expansion at rate $O(1/\sqrt{n})$

### What Would a Proof Need?

- Key lemma 1: MGF of standardized Bin(n,p) = $(1-p+pe^{t/\sqrt{npq}})^n$
- Key lemma 2: $(1 + a_n)^n \to e^L$ when $n \cdot a_n \to L$ (from parent proof)
- Key lemma 3: Levy's continuity theorem (MGF/CF convergence → weak convergence)
- Technical: `ProbabilityTheory.tendsto_of_mgf_tendsto` or equivalent

## Tractability Assessment

**Difficulty**: Medium (with Mathlib CLT infrastructure); High (without it)

**Justification**:
- The algebraic MGF computation is straightforward
- The bottleneck is whether Mathlib has Levy's theorem or weak-convergence infrastructure
- If using Stirling's approach, it's more mechanical but longer

**Estimated Effort**:
- Exploration: 1 day (check Mathlib CLT/weak convergence landscape)
- If CLT infrastructure exists: 2-3 days
- If infrastructure missing: weeks to build it

## References

### Papers
- de Moivre, A. (1738). "The Doctrine of Chances." 2nd ed. — historical CLT
- Laplace, P.S. (1812). "Théorie Analytique des Probabilités." — formal CLT

### Online Resources
- Mathlib4 docs: `ProbabilityTheory` namespace for weak convergence

### Mathlib
- `Mathlib.Probability.Distributions.Binomial` — Bin(n,p) definition
- `Mathlib.MeasureTheory.Measure.ProbabilityMeasure` — weak convergence
- `Mathlib.Analysis.SpecialFunctions.ExpDeriv` — exp Taylor series
- `Proofs/BinomialTheoremOQ03.lean` — parent proof (Poisson limit uses (1+x/n)^n → e^x)

## Metadata

```yaml
tags:
  - probability
  - central-limit-theorem
  - binomial-distribution
  - moment-generating-function
  - de-moivre-laplace
  - analysis
related_proofs:
  - binomial-theorem-oq-03
  - central-limit-theorem-oq-03-oq-02
difficulty: medium
source: gallery-gap
created: 2026-04-22T14:37:37+02:00
```

**Significance**: 7/10
**Tractability**: 6/10

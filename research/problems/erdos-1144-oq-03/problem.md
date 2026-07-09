# Problem: Sharpness of the (log N)^{1+ε} factor in Atherfold's bound

**Slug**: erdos-1144-oq-03
**Created**: 2026-07-09T15:40:18-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Atherfold (2025) proved } \Big|\sum_{m \le N} f(m)\Big| \ll \sqrt{N}\,(\log N)^{1+o(1)} \text{ a.s.; show the } (\log N)^{1+o(1)} \text{ factor cannot be replaced by } (\log N)^{K} \text{ for any fixed } K < \infty.
$$

### Plain Language

Atherfold's 2025 theorem gives an almost-sure upper bound on the partial sums of a
Rademacher random multiplicative function: the sum of $f(m)$ over $m \le N$ grows no faster
than $\sqrt{N}$ times $(\log N)^{1+o(1)}$. The exponent $1 + o(1)$ hides a factor that tends
to infinity slower than any fixed positive power of $\log N$. This problem asks whether that
extra logarithmic factor is genuinely necessary in that exact shape — specifically, whether
one could tighten Atherfold's bound so the log power stays below some fixed constant $K$
instead of drifting up to $1 + o(1)$. Proving it cannot be reduced to a bounded power means
showing the true growth really does require the $(\log N)^{1+o(1)}$ correction, so the $o(1)$
in the exponent is not an artifact of Atherfold's method but a real feature of the extremal
behaviour.

### Why This Matters

Pinning down the exact logarithmic correction in the upper bound is the crux of understanding
the extreme fluctuations of random multiplicative functions. Harper's 2013 work showed the
*typical* size is $\sqrt{N}/(\log\log N)^{3/4+o(1)}$ — smaller than $\sqrt{N}$ — while the
*maximal* fluctuations are believed to be much larger, and Erdős Problem #1144 conjectures the
limsup of $|S_f(N)|/\sqrt{N}$ diverges. Whether the maximum sits at $\sqrt{N}(\log N)^{1+o(1)}$
or something with a bounded log power decides how sharp the pinch between the conjectured lower
bound and Atherfold's upper bound really is. A negative answer (the factor cannot be reduced)
would confirm $(\log N)^{1+o(1)}$ as the correct order of the maximum and connect random
multiplicative functions to the theory of log-correlated fields, where a $(\log N)^{1}$-type
factor is the signature of a branching-random-walk maximum.

## Known Results

### What's Already Proven

- Atherfold's almost-sure upper bound $|S_f(N)| \ll \sqrt{N}(\log N)^{1+o(1)}$ — Atherfold, "Almost sure upper bounds for random multiplicative functions", 2025 (preprint); axiomatized in `Proofs/Erdos1144Problem.lean` as `atherfold_upper_bound`.
- Harper's typical-size theorem $S_f(N) = \sqrt{N}/(\log\log N)^{3/4+o(1)}$ — Harper, arXiv:1302.7208, 2013.
- Wintner's classical $O(N^{1/2+\varepsilon})$ almost-sure bound — Wintner, Duke Math. J. 11(2), 1944.
- The growth-rate "pinch" theorem: conjecture + Atherfold's bound pin $|S_f(N)|$ between $C_1\sqrt{N}$ and $C_2\sqrt{N}(\log N)^{1+\varepsilon}$ — `conjecture_and_atherfold_pinch` in `Proofs/Erdos1144Problem.lean` (fully proved, 0 sorries).

### What's Still Open

- Whether the $(\log N)^{1+o(1)}$ factor is optimal or can be shrunk to a fixed power $(\log N)^K$.
- The matching lower bound for the maximum: is there a.s. a subsequence $N_k$ with $|S_f(N_k)| \gg \sqrt{N_k}(\log N_k)^{1-o(1)}$?
- The primary Erdős #1144 conjecture $\limsup |S_f(N)|/\sqrt{N} = \infty$ a.s.

### Our Goal

Formalize the $o(1)$-refinement question in Lean 4: state precisely the claim that no fixed
$K$ yields an almost-sure bound $|S_f(N)| \ll \sqrt{N}(\log N)^K$, and build the logical scaffold
that would derive a contradiction from such a bound using the (conjectured) maximal lower bound.
The deliverable is a faithful statement plus the reduction lemmas connecting a hypothetical
bounded-power bound to the maximal fluctuation conjecture, mirroring the axiomatize-and-pinch
architecture already present for the base problem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1144 | Parent problem; supplies definitions, Atherfold axiom, and pinch theorem | Filter.atTop, strong induction on prime factorization, triangle inequality |
| erdos-520 | Partial sums restricted to squarefree integers; same multiplicative-sum theme | Multiplicative function estimates, growth-rate bounds |
| prime-number-theorem | Governs the distribution of the primes defining $f$ | Analytic number theory, asymptotics |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Contradiction via the maximal lower bound.
   - Why it might work: If one assumes a bounded-power bound $|S_f(N)| \ll \sqrt{N}(\log N)^K$ and combines it with an a.s. maximal lower bound of order $\sqrt{N}(\log N)^{1-o(1)}$ along a subsequence, taking $K$ below $1$ gives a direct contradiction; the whole difficulty concentrates in supplying the maximal lower bound.
   - Risk: The maximal lower bound is itself open and would likely need to be axiomatized, so the "cannot be reduced" claim becomes conditional.

2. **Approach B**: Second-moment / Gaussian-multiplicative-chaos comparison.
   - Why it might work: Harper's methods connect $|S_f(N)|$ to critical multiplicative chaos, where the maximum of a log-correlated field carries a $(\log N)^{1}$ factor; transporting this heuristic gives the exact exponent and shows a bounded power is impossible.
   - Risk: Multiplicative chaos and log-correlated maxima are far outside current Mathlib coverage, so full formalization is a moonshot.

### Key Difficulties

- The refinement is a statement about $o(1)$ in an exponent — Lean has no native notion of $o(1)$-in-the-exponent, so it must be encoded via "for all $K$, not $O(\sqrt N (\log N)^K)$".
- The underlying maximal lower bound is unproven in the literature, forcing an axiomatized/conditional formalization.
- Mathlib lacks multiplicative chaos, log-correlated field, and random-multiplicative-function infrastructure.

### What Would a Proof Need?

- Key lemma 1: A precise Lean statement "no fixed $K$ gives $|S_f(N)| \le C\sqrt{N}(\log N)^K$ eventually", quantifying over $K$ and $C$.
- Key lemma 2: A reduction showing that such a bounded-power bound contradicts an a.s. maximal lower bound of order $\sqrt{N}(\log N)^{1-\varepsilon}$ along a subsequence.
- Technical requirements: Real logarithm and power API (`Real.log`, `Real.rpow`), `Filter.atTop` frequently/eventually machinery, and an axiom capturing the maximal fluctuation lower bound.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematical statement is open in the literature; only the formal scaffolding and a conditional reduction are realistically achievable.
- Similar conditional formalizations exist here: the parent `erdos-1144` axiomatizes Atherfold's bound and proves a pinch theorem around it, providing a proven template.
- Mathlib supplies the real analysis primitives (`Real.log`, `Real.rpow`, filters) but nothing on multiplicative chaos or random multiplicative functions.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 1–2 weeks for the conditional statement plus reduction lemmas
- If hard: unknown (unconditional resolution is a research-level open problem)

## References

### Papers
- T. Atherfold, "Almost sure upper bounds for random multiplicative functions", 2025 (preprint) — source of the $(\log N)^{1+o(1)}$ upper bound.
- A. J. Harper, "Moments of random multiplicative functions and truncated characteristic polynomials", arXiv:1302.7208, 2013 — typical size $\sqrt{N}/(\log\log N)^{3/4+o(1)}$.
- A. Wintner, "Random factorizations and Riemann's hypothesis", Duke Math. J. 11(2), 1944 — foundational $O(N^{1/2+\varepsilon})$ bound.

### Online Resources
- https://erdosproblems.com/1144 — Erdős Problem #1144 catalogue entry and status.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — real logarithm needed to express $(\log N)^K$.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — real powers `Real.rpow` for the exponent $K$ and for $\sqrt{N}$.
- `Mathlib.Order.Filter.AtTopBot` — `Filter.atTop` to encode "eventually" and "infinitely often".

## Metadata

```yaml
tags:
  - number-theory
  - probability
  - analysis
  - multiplicative-functions
  - open
related_proofs:
  - erdos-1144
  - erdos-520
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:18-07:00
```

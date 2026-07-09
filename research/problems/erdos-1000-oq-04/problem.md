# Problem: Measure of Increasing Sequences with Vanishing Cesàro Average of the Generalized Totient

**Slug**: erdos-1000-oq-04
**Created**: 2026-07-09T15:40:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\mu\bigl(\{A = (n_1 < n_2 < \cdots) : \lim_{N\to\infty} \tfrac{1}{N}\textstyle\sum_{k=1}^{N} \tfrac{\varphi_A(k)}{n_k} = 0\}\bigr) = \; ?
$$

where $\varphi_A(k) = |\{1 \le m \le n_k : n_k/\gcd(m,n_k) \ne n_j \text{ for all } j < k\}|$ is the generalized totient, and $\mu$ is a suitable measure on the space of strictly increasing positive-integer sequences.

### Plain Language

Erdős Problem #1000 asks whether some strictly increasing integer sequence $A$ makes the Cesàro average of the "new denominator density" $\varphi_A(k)/n_k$ tend to zero. Haight answered yes: such sequences exist. This follow-up question asks a quantitative refinement: among *all* increasing sequences, how large is the collection of those exhibiting a vanishing average? We want to determine the measure of the set of vanishing-average sequences under a natural probability measure on sequence space, deciding whether the Haight phenomenon is exceptional (measure zero) or typical (positive, or even full, measure).

### Why This Matters

Haight's construction shows vanishing-average sequences *exist*, but existence alone does not reveal whether they are rare special constructions or a generic feature of increasing sequences. Measuring the set separates two very different pictures: if the measure is zero the vanishing average is a delicate, atypical phenomenon achievable only by carefully engineered highly composite sequences; if it is positive the phenomenon is robust and reflects generic behavior of the generalized totient. Answering this ties Erdős #1000 to metric number theory (à la the Khinchin-Groshev framework Cassels used) and to the general theme of how averaging tames the pointwise oscillation of arithmetic functions.

## Known Results

### What's Already Proven

- Haight's resolution: there exists an increasing sequence $A$ with $\lim_N C_A(N) = 0$ — formalized as the axiom `haight_resolution` in `Proofs/Erdos1000Problem.lean`
- Erdős' no-zero-limit theorem: the pointwise ratio $\varphi_A(k)/n_k$ never converges to $0$ for any $A$ — theorem `erdos_no_zero_limit` in `Proofs/Erdos1000Problem.lean`
- Erdős' dichotomy: if $\liminf_k \varphi_A(k)/n_k = 0$ then $\limsup_k \varphi_A(k)/n_k = 1$ — axiom `erdos_dichotomy` in `Proofs/Erdos1000Problem.lean`
- Structural lower bound: $\varphi_A(k) \ge \varphi(n_k)$ (Euler's totient), giving the density floor $\varphi_A(k)/n_k \ge \varphi(n_k)/n_k$ — theorem `phiA_ge_totient` in `Proofs/Erdos1000Problem.lean`
- Pointwise/Cesàro separation: there is an $A$ with vanishing average but non-vanishing pointwise density — theorem `pointwise_cesaro_gap` in `Proofs/Erdos1000Problem.lean`

### What's Still Open

- Which measure $\mu$ on the space of increasing sequences makes the question well-posed (e.g. a product/renewal measure on gaps, or a Cantor-style coding measure)
- Whether the set of vanishing-average sequences has measure $0$, measure $1$, or an intermediate positive value under that $\mu$
- Whether the answer depends on the growth regime imposed on the gaps $n_{k+1} - n_k$

### Our Goal

Formalize the measure-theoretic setup for the space of strictly increasing positive-integer sequences and state the measurability of the vanishing-average event $\{A : \lim_N C_A(N) = 0\}$, then establish a first quantitative bound (for instance, that under a fast-growth product measure the event is measure zero, mirroring the `not_densityToZero_of_fast_growth` growth-floor results). Full determination of the measure is a moonshot; the tractable milestone is a rigorous framework plus one measure-zero or positive-measure lemma for a concrete measure.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1000 | Parent problem: defines $\varphi_A$, the Cesàro average, Haight's resolution, and the density floor this question quantifies | Generalized totient, Cesàro means, Euler product, highly composite numbers, filter limits |
| erdos-1003 | Studies Euler's totient $\varphi(n)$, which provides the density floor $\varphi_A(k) \ge \varphi(n_k)$ | Totient identities, multiplicative function estimates |
| erdos-1004 | Distribution of totient values, the baseline arithmetic function underlying $\varphi_A$ | Totient value distribution, counting arguments |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Product/renewal measure on gaps.
   - Why it might work: modeling the gaps $g_k = n_{k+1}-n_k$ as i.i.d. (or Markov) random variables turns $C_A(N)$ into an ergodic average, so a strong law or Birkhoff-type argument could pin down the measure of the vanishing event.
   - Risk: the vanishing average requires highly composite $n_k$, which is a strongly correlated arithmetic condition that i.i.d. gap models may assign measure zero to trivially, making the "interesting" measure hard to choose.

2. **Approach B**: Growth-floor / Borel-Cantelli route.
   - Why it might work: the formalized results `not_densityToZero_of_fast_growth` and `densityRatio_gt_half_of_fast_growth` show fast-growing sequences keep the density above $1/2$; a Borel-Cantelli argument could show that under many measures the sequence is "fast" almost surely, forcing the vanishing event to be null.
   - Risk: establishes only an upper bound (measure zero) for specific measures and says nothing about measures concentrated on slowly growing / highly composite sequences.

### Key Difficulties

- Choosing a canonical, defensible measure $\mu$ on an inherently discrete but infinite-dimensional sequence space; the answer is meaningless without fixing $\mu$
- The vanishing-average condition mixes an analytic tail limit with the delicate arithmetic (highly composite structure) that Haight exploited, so measurability and estimation require both metric and multiplicative tools
- Mathlib has strong `MeasureTheory` and product-measure infrastructure but limited support for measures on spaces of monotone integer sequences, so encoding the space is itself work

### What Would a Proof Need?

- Key lemma 1: a measurable coding of strictly increasing sequences (e.g. via the gap sequence in $\mathbb{N}_{\ge 1}^{\mathbb{N}}$ with a product $\sigma$-algebra) and measurability of $A \mapsto C_A(N)$ for each $N$
- Key lemma 2: measurability of the event $\{A : C_A(N) \to 0\}$ as a countable combination of the $C_A(N)$ (via `Filter.Tendsto` characterizations), plus a $0$-$1$ style law under a product measure
- Technical requirements: `MeasureTheory.Measure`, `MeasurePreserving`/ergodic tooling, `Filter.Tendsto`, and the already-formalized growth-floor lemmas from `Proofs/Erdos1000Problem.lean` to seed the first bound

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full measure is a genuinely open, likely moonshot-level metric number theory question with no known answer in the literature
- Setting up a measurable framework and proving measurability of the vanishing event is tractable and mirrors standard product-measure constructions already in Mathlib
- Mathlib's `MeasureTheory` (product measures, measurability of limits, Borel-Cantelli, ergodic-theory lemmas) plus the existing `Erdos1000Problem.lean` growth-floor theorems provide the tools for a first measure-zero bound under a concrete measure

**Estimated Effort**:
- Exploration: 3-5 days
- If tractable: 2-4 weeks for the measurable framework plus one quantitative bound
- If hard: unknown (full determination of the measure is open)

## References

### Papers
- Haight, J.A., "A generalisation of a problem of Cassels and Erdős" (relevant work resolving #1000) — establishes existence of vanishing-average sequences, the phenomenon whose measure is sought
- Cassels, J.W.S., "An Introduction to Diophantine Approximation", 1957 — origin of the generalized totient and its metric-approximation context
- Erdős, P., work of 1964 on the no-zero-limit and dichotomy — the pointwise constraints that shape which sequences can have vanishing average

### Online Resources
- https://erdosproblems.com/1000 — canonical statement and status of Erdős Problem #1000
- https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/Erdos1000Problem.lean — the formalized parent proof with the density-floor and growth lemmas

### Mathlib
- `Mathlib.MeasureTheory.Measure.Basic` and product-measure modules — provide the measure-space and product-measure infrastructure for coding sequence space
- `Mathlib.MeasureTheory.Constructions.BorelSpace.Basic` — measurability of limits of measurable functions, needed for the vanishing-average event
- `Mathlib.Dynamics.Ergodic.Ergodic` — ergodic/law-of-large-numbers tooling for evaluating Cesàro averages under an invariant measure
- `Mathlib.Analysis.Nat.Totient` — Euler's totient and its Euler product, underlying the density floor $\varphi_A(k) \ge \varphi(n_k)$

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - diophantine-approximation
  - totient-function
  - cesaro-averages
related_proofs:
  - erdos-1000
  - erdos-1003
  - erdos-1004
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:19-07:00
```

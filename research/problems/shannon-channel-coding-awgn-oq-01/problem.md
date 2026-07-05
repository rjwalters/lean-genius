# Problem: AWGN Mutual-Information Chain Rule I(X;Y) = h(Y) − h(Z)

**Slug**: shannon-channel-coding-awgn-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
Y = X + Z,\quad X \perp Z \Rightarrow I(X;Y) = h(Y) - h(Y\mid X) = h(Y) - h(Z),
$$
$$
\text{whence for } Z \sim \mathcal N(0,N),\ X \text{ with } \mathbb E[X^2]\le P:\quad \max_{X} I(X;Y) = \tfrac12 \log\!\big(1 + \tfrac{P}{N}\big).
$$

### Plain Language

The AWGN capacity entry currently assembles the capacity value $C = \tfrac12\log(1+P/N)$ from an *entropy difference* $h(Y) - h(Z)$ that is taken as a hypothesis. We want to make that difference operational: define the (differential) mutual information $I(X;Y)$ for the additive channel $Y = X + Z$ with independent noise, and prove the chain-rule decomposition $I(X;Y) = h(Y) - h(Y\mid X) = h(Y) - h(Z)$. Because conditioning on $X$ leaves only the noise, $h(Y\mid X) = h(Z)$; combined with the Gaussian entropy formula this upgrades the entry from an algebraic identity to the genuine operational capacity theorem.

### Why This Matters

Mutual information is the central quantity of information theory, but its differential (continuous-alphabet) form and the chain rule $I(X;Y)=h(Y)-h(Y|X)$ are not developed in Mathlib. Establishing the chain rule for additive channels turns a large family of gallery capacity results (AWGN, parallel Gaussian channels, Shannon–Hartley) from stated identities into proved theorems, and provides reusable differential-entropy infrastructure.

## Known Results

### What's Already Proven

- `shannon-channel-coding-awgn` (VERIFIED, 0 axioms): `awgn_log_identity`, `awgn_noise_entropy`, `awgn_output_entropy`, `awgn_capacity_achieved`, `awgn_capacity_upper_bound` — the entropy-difference assembly.
- Mathlib has `MeasureTheory` integration and `ProbabilityTheory` (independence, variance) for building the differential-entropy definitions.
- Shannon's original channel-coding theorem (1948) — the classical target.

### What's Still Open

- Differential (continuous-alphabet) mutual information $I(X;Y)$ is not defined in Mathlib.
- The chain rule $I(X;Y) = h(Y) - h(Y\mid X)$ and $h(Y\mid X) = h(Z)$ (for $Y=X+Z$, $X\perp Z$) are not formalized.

### Our Goal

Define differential entropy $h(\cdot)$ and mutual information $I(X;Y)$ for the additive channel, prove $I(X;Y) = h(Y) - h(Z)$ via the chain rule and translation-invariance of differential entropy, and connect it to `awgn_output_entropy`/`awgn_noise_entropy` so that the capacity value becomes $\max_X I(X;Y)$ rather than an assumed entropy difference. A faithful additive-channel chain rule alone (independent of the full coding theorem) is a valuable milestone.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-channel-coding-awgn | Parent; supplies the entropy-difference assembly to upgrade | differential entropy, log identities |
| shannon-channel-coding-bec | Sibling discrete channel with a Fano-inequality converse | discrete entropy, Fano |
| shannon-entropy or gaussian-integral entries | Gaussian entropy value and integrals | measure theory, Gaussian integral |

## Initial Thoughts

### Potential Approaches

1. **Translation-invariance route**: define $h(W) = -\int f_W \log f_W$ for a density $f_W$; show $h(X+Z\mid X=x) = h(Z)$ because conditioning fixes $X$ and shifts $Z$ by a constant, and differential entropy is translation-invariant. Then $I(X;Y) = h(Y) - h(Y\mid X) = h(Y) - h(Z)$ is immediate from the chain rule for $I$.
   - Why it might work: translation-invariance of $h$ is a clean measure-theoretic fact; the chain rule is a definitional rearrangement.
   - Risk: the density/absolute-continuity bookkeeping (existence of $f_Y$, integrability of $\log$) is the technical crux.

2. **KL-divergence definition**: define $I(X;Y) = D_{KL}(P_{XY} \,\|\, P_X\otimes P_Y)$ and derive the entropy-difference form; leverage any Mathlib KL/relative-entropy API.
   - Why it might work: reduces mutual information to a single divergence object.
   - Risk: differential KL and its finiteness conditions may need to be built from scratch.

### Key Difficulties

- Differential entropy is only defined for absolutely continuous laws; handling integrability of $f\log f$ and existence of the output density.
- Formalizing the conditional differential entropy $h(Y\mid X)$ and its equality with $h(Z)$.

### What Would a Proof Need?

- Key lemma 1: translation-invariance of differential entropy, $h(Z + c) = h(Z)$.
- Key lemma 2: additive-channel conditional entropy, $h(Y\mid X) = h(Z)$ for $Y = X + Z$, $X\perp Z$.
- Key lemma 3: the differential mutual-information chain rule $I(X;Y) = h(Y) - h(Y\mid X)$.
- Technical requirements: densities via `MeasureTheory.Measure.withDensity`, independence from `ProbabilityTheory`, Gaussian entropy value.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The parent already contains the Gaussian entropy values and the algebraic capacity assembly; only the operational definitions are missing.
- Mathlib provides the measure-theoretic and independence substrate.
- The main risk is integrability bookkeeping, not deep mathematics.

**Estimated Effort**:
- Exploration: 2-3 days (survey Mathlib entropy/KL support)
- If tractable: 1-3 weeks (definitions + chain rule + link to parent)
- If hard: the general density existence may force restriction to nice (e.g. Gaussian-input) cases

## References

### Papers
- C. E. Shannon, "A Mathematical Theory of Communication," 1948 — mutual information and channel capacity.
- Cover & Thomas, *Elements of Information Theory*, Ch. 8-9 — differential entropy, AWGN capacity, chain rules.

### Online Resources
- Cover–Thomas differential-entropy chapter — the $I(X;Y)=h(Y)-h(Y|X)$ derivation.

### Mathlib
- `Mathlib.MeasureTheory.*` (integration, `withDensity`) — differential entropy substrate.
- `Mathlib.Probability.*` (independence, variance) — additive-channel setup.

## Metadata

```yaml
tags:
  - information-theory
  - entropy
  - mutual-information
  - probability
  - measure-theory
related_proofs:
  - shannon-channel-coding-awgn
  - shannon-channel-coding-bec
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 5/10

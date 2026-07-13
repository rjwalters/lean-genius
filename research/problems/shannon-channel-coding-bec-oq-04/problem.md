# Problem: Capacity of the Binary Error-and-Erasure Channel

**Slug**: shannon-channel-coding-bec-oq-04
**Created**: 2026-07-04T19:56:31-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For the binary error-and-erasure channel with erasure probability $\varepsilon$
and (post-non-erasure) crossover probability $p$, the capacity is

$$
C(\varepsilon, p) \;=\; (1 - \varepsilon)\,\bigl(1 - H_2(p)\bigr),
\qquad H_2(p) = -p\log_2 p - (1-p)\log_2(1-p).
$$

The two classical channels are recovered as boundary cases:
$C(\varepsilon, 0) = 1 - \varepsilon$ (BEC) and $C(0, p) = 1 - H_2(p)$ (BSC).

### Plain Language

The parent gallery entry proves the capacity of the Binary Erasure Channel (BEC),
where each transmitted bit is either received perfectly or erased. This extension
adds a second failure mode: a received (non-erased) bit may also be flipped with
probability $p$. We want the capacity formula for this combined channel and a
proof that setting $p = 0$ gives the BEC and $\varepsilon = 0$ gives the Binary
Symmetric Channel (BSC).

### Why This Matters

It unifies the two most-studied discrete memoryless channels (BEC and BSC) under
a single capacity formula, showing the gallery's BEC machinery composes cleanly.
The mutual-information optimization is a small, self-contained instance of
Shannon's channel coding theorem, making it an ideal formalization target that
reuses the parent entry's information-theoretic scaffolding.

## Known Results

### What's Already Proven

- Parent entry `shannon-channel-coding-bec` — capacity of the BEC is $1-\varepsilon$.
- BSC capacity $1 - H_2(p)$ — classical, and a natural sibling target.
- Shannon's channel coding theorem — capacity equals $\max_{P_X} I(X;Y)$ for a DMC.

### What's Still Open

- No Mathlib formalization of the error-and-erasure channel capacity.
- General operational converse (Fano's inequality) is heavier; the
  mutual-information *formula* is the tractable core here.

### Our Goal

Formalize $C(\varepsilon, p) = (1-\varepsilon)(1 - H_2(p))$ as the maximizing
mutual information $\max_{P_X} I(X; Y)$ for the channel, achieved at the uniform
input distribution, and prove the two boundary specializations. Scope: the
information-theoretic capacity (single-letter mutual-information formula), not the
full operational coding theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-channel-coding-bec | Parent: BEC is the $p=0$ boundary case | Mutual information, entropy |
| shannon-channel-coding-awgn | Sibling capacity computation | Capacity as max mutual information |

## Initial Thoughts

### Potential Approaches

1. **Direct mutual-information maximization**: Model the channel as a stochastic
   matrix on $\{0,1\} \to \{0, 1, ?\}$, compute $I(X;Y)$ as a function of the input
   Bernoulli parameter, and show it is maximized at $1/2$ giving the stated $C$.
   - Why it might work: closed-form; reuses the BEC entry's entropy lemmas.
   - Risk: symbolic manipulation of $H_2$ and logs; concavity of the objective.

2. **Reduce to BEC ∘ BSC composition**: Treat the channel as an erasure applied
   to a BSC output and combine capacities.
   - Why it might work: modular, leans on both parents.
   - Risk: composition of capacities is not additive in general; needs care.

### Key Difficulties

- Establishing that uniform input is the maximizer (concavity of $I(X;Y)$ in $P_X$).
- Handling the binary entropy function $H_2$ and its logarithms in Lean cleanly.

### What Would a Proof Need?

- Key lemma 1: $I(X;Y) = (1-\varepsilon)(H_2(q) - H_2(p))$-style expansion for input
  bias $q$, with maximum at $q = 1/2$.
- Key lemma 2: Boundary evaluations $H_2(0) = 0$ and continuity at the endpoints.
- Technical requirements: `Real.logb`, concavity, Jensen or a direct derivative.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Closed-form capacity with a clean maximizer; the BEC parent supplies most tools.
- Boundary cases are direct substitutions once the formula is proven.
- Similar in spirit to already-formalized entropy/capacity gallery entries.

**Estimated Effort**:
- Exploration: hours to days
- If tractable: days to weeks
- If hard: unknown (if the concavity/maximizer step resists)

## References

### Papers
- Shannon, "A Mathematical Theory of Communication", *Bell Syst. Tech. J.* (1948) — capacity via mutual information.
- Cover & Thomas, *Elements of Information Theory*, Ch. 7 — DMC capacity, BEC/BSC.

### Online Resources
- Cover & Thomas problem sets — the error-and-erasure channel as a worked example.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Log.*` — logarithms for entropy.
- `Mathlib.Probability.*` — probability mass functions for the channel model.

## Metadata

```yaml
tags:
  - information-theory
  - channel-capacity
  - shannon
  - entropy
related_proofs:
  - shannon-channel-coding-bec
difficulty: medium
source: proof-suggestion
created: 2026-07-04T19:56:31-07:00
```

**Significance**: 6/10
**Tractability**: 5/10

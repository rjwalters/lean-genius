# Problem: Capacity of the q-ary Erasure Channel

**Slug**: shannon-channel-coding-bec-oq-01
**Created**: 2026-06-18T13:35:50-07:00
**Status**: Active
**Source**: gallery-gap <!-- openQuestion of parent shannon-channel-coding-bec -->

## Problem Statement

### Formal Statement

The parent entry formalizes the binary erasure channel (BEC): input alphabet $\{0,1\}$, erasure
probability $p$, and capacity
$$
C_{\mathrm{BEC}}(p) = 1 - p \quad \text{(bits)}.
$$
The open task is the generalization to the **$q$-ary erasure channel** (QEC): input alphabet of
size $q \ge 2$, each symbol independently erased with probability $p$ and otherwise received
intact. The claim to formalize is
$$
C_{\mathrm{QEC}}(p, q) = (1 - p)\,\log q,
$$
with the BEC recovered at $q = 2$ (and $\log = \log_2$ giving $C = 1 - p$). The supporting
**erasure identity** to lift is the mutual-information decomposition
$$
I(X; Y) = (1 - p)\, H(X),
$$
maximized by the uniform input, for which $H(X) = \log q$.

### Plain Language

A $q$-ary erasure channel transmits one of $q$ symbols, and with probability $p$ the receiver is
told "erased" instead of the symbol. Because the receiver always knows *which* positions were
erased, the only lost information is the erased symbols themselves. Intuitively a fraction $1-p$ of
the symbols get through cleanly, and each carries $\log q$ bits, so the capacity is
$(1-p)\log q$. The binary case $q = 2$ is exactly the parent entry's $1 - p$.

### Why This Matters

The QEC is the canonical model for packet-loss networks and the test bed for capacity-achieving
codes (Reed–Solomon, fountain/LT codes). Generalizing the formalized BEC argument to arbitrary
alphabet size both broadens the gallery's information-theory coverage and exercises Mathlib's
entropy API beyond the Boolean special case.

## Known Results

### What's Already Proven

- Parent gallery proof `shannon-channel-coding-bec` — the $q = 2$ erasure identity and capacity
  $1 - p$, including the mutual-information decomposition and the uniform-input maximizer.
- Sibling entries `shannon-entropy`, `shannon-channel-coding-bsc` — entropy and the binary
  symmetric channel.
- Mathlib's information-theory entropy (`Mathlib.Probability.Entropy` / `Mathlib.Information`)
  providing $H$, the chain rule, and the uniform-distribution maximizer
  $H(X) \le \log |\mathrm{supp}|$.

### What's Still Open

- The erasure identity $I(X;Y) = (1-p)H(X)$ for general alphabet size $q$.
- Identifying the capacity-achieving input as uniform and evaluating $\max_X I(X;Y) = (1-p)\log q$.

### Our Goal

State the QEC over a finite input type `α` with `Fintype.card α = q`, define the erasure output as
`Option α` (the `none` value is the erasure symbol), prove the erasure identity, and conclude
$C = (1-p)\log q$ with the uniform input as maximizer. Keep the BEC entry as the `q = 2` corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-channel-coding-bec | Parent / binary special case | erasure identity, mutual info |
| shannon-entropy | Entropy bounds + uniform maximizer | $H(X) \le \log q$ |
| shannon-channel-coding-bsc | Sibling channel-capacity formalization | mutual information |

## Initial Thoughts

### Potential Approaches

1. **Lift the BEC proof verbatim with `Fintype.card α = q`**: replace the Boolean input by a finite
   type, the output by `Option α`, and re-derive $I(X;Y) = (1-p)H(X)$; then maximize via the
   uniform bound $H(X) \le \log q$.
   - Why it might work: the erasure decomposition does not use $q = 2$ anywhere essential.
   - Risk: Mathlib entropy API friction (measurability/`PMF` packaging) for the general type.

2. **Abstract erasure-channel lemma**: prove $I(X;Y) = (1-p)H(X)$ once for any input PMF, then
   instantiate.
   - Why it might work: cleanly separates the channel identity from the maximization.
   - Risk: needs careful definition of the joint distribution on `α × Option α`.

### Key Difficulties

- Choosing a Lean encoding of the channel (PMF on `Option α`) compatible with Mathlib's entropy.
- The uniform-input maximizer step: invoking $H(X) \le \log q$ with equality at uniform.

### What Would a Proof Need?

- Key lemma 1: erasure identity $I(X;Y) = (1-p)\,H(X)$ for the QEC.
- Key lemma 2: $\max_X H(X) = \log q$ attained at the uniform distribution.
- Technical requirements: Mathlib entropy / mutual information API, `Fintype`, `PMF`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Direct generalization of an already-formalized proof; the mathematics is the same.
- Mathlib supplies entropy, the uniform maximizer, and finite-type machinery.
- Main risk is API ergonomics, not missing theory.

**Estimated Effort**:
- Exploration: hours to a day
- If tractable: a few days
- If hard: blocked only if Mathlib's mutual-information API is thin

## References

### Papers
- C. E. Shannon (1948), *A Mathematical Theory of Communication* — channel capacity.
- Cover & Thomas, *Elements of Information Theory*, Ch. 7 — erasure channels.

### Online Resources
- MacKay, *Information Theory, Inference, and Learning Algorithms*, Ch. 9.

### Mathlib
- `Mathlib.Probability.Entropy` — Shannon entropy and bounds.
- `Mathlib.Probability.ProbabilityMassFunction` — `PMF` on finite types.

## Metadata

```yaml
tags:
  - information-theory
  - entropy
  - channel-capacity
related_proofs:
  - shannon-channel-coding-bec
  - shannon-entropy
difficulty: medium
source: gallery-gap
created: 2026-06-18T13:35:50-07:00
```

# Problem: BEC Converse via Fano's Inequality

**Slug**: shannon-channel-coding-bec-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{(Fano) For an estimate } \hat W \text{ of } W \text{ over } n \text{ uses of the BEC}(p):\quad H(W\mid \hat W) \le 1 + P_e \log(|\mathcal W|-1).
$$
$$
\text{Hence any rate } R \text{ with vanishing error satisfies } R \le C = 1 - p, \text{ discharging } \texttt{channel\_coding\_converse}.
$$

### Plain Language

The binary erasure channel (BEC) transmits each bit correctly with probability $1-p$ and "erases" it with probability $p$. Its capacity is $C = 1-p$. The parent gallery entry proves the *information-theoretic* supremum equals $1-p$ but takes the *operational converse* — "no reliable code can beat $1-p$" — as an axiom (`channel_coding_converse`). We want to prove that converse operationally via **Fano's inequality**, which bounds the residual uncertainty $H(W\mid\hat W)$ of the transmitted message given the decoder's estimate in terms of the error probability, and combine it with the data-processing / chain-rule bound to force $R \le 1-p$.

### Why This Matters

Fano's inequality is the standard engine behind *every* channel-coding converse and many impossibility results in information theory and statistics. It is not in Mathlib. Formalizing it — even specialized to the BEC — discharges a named axiom in the gallery, turning the BEC capacity into a genuine operational theorem, and provides reusable converse infrastructure for the other channel-coding entries (AWGN, BSC).

## Known Results

### What's Already Proven

- `shannon-channel-coding-bec` (AXIOMATIZED): the information-theoretic BEC supremum $1-p$, with `channel_coding_converse` and `channel_coding_achievability` as axioms.
- Discrete Shannon entropy and mutual information appear (in some form) in the BEC entry and Mathlib's developing information-theory files.
- Classical Fano inequality (Fano 1961; Cover–Thomas Thm 2.10.1) — the target, not yet in Mathlib.

### What's Still Open

- Fano's inequality is not formalized in Mathlib.
- The operational BEC converse (`channel_coding_converse`) is axiomatized, not proved.

### Our Goal

Formalize Fano's inequality for finite message alphabets, then instantiate it for $n$ uses of the BEC to prove the converse $R \le 1-p$, discharging `channel_coding_converse`. A standalone finite-alphabet Fano inequality — independent of the BEC application — is itself a valuable, reusable result.

## Known Results — Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-channel-coding-bec | Parent; axiom to discharge | discrete entropy, erasure identity |
| shannon-channel-coding-awgn | Sibling channel (continuous) with its own converse target | differential entropy |
| shannon-entropy / discrete-entropy entries | Entropy inequalities used by Fano | Jensen, log-sum, chain rule |

## Initial Thoughts

### Potential Approaches

1. **Direct finite-alphabet Fano**: introduce the error indicator $E = \mathbf 1[\hat W \ne W]$; expand $H(E,W\mid\hat W)$ two ways via the chain rule to get $H(W\mid\hat W) \le H(E) + P_e\log(|\mathcal W|-1) \le 1 + P_e\log(|\mathcal W|-1)$. Then combine with $H(W\mid\hat W)\ge H(W) - I(W;\hat W)$ and the per-use mutual-information bound $\le 1-p$ for the BEC.
   - Why it might work: every step is a finite-sum entropy manipulation over a finite alphabet, well suited to Mathlib's `Finset` sums.
   - Risk: assembling the multi-use mutual-information bound $I(W;\hat W) \le n(1-p)$ requires a data-processing / channel-decomposition lemma.

2. **Specialize maximally to BEC**: exploit that erasures are known to the decoder, so the residual uncertainty is exactly the entropy of the erased positions, giving a sharper and more direct converse.
   - Why it might work: sidesteps general data-processing by using the erasure structure.
   - Risk: less reusable; still needs the counting of erased positions.

### Key Difficulties

- Formalizing conditional entropy $H(W\mid\hat W)$ and the chain rule over finite alphabets.
- The multi-use mutual-information bound $I(W;\hat W)\le n\,C$ (data-processing across $n$ channel uses).

### What Would a Proof Need?

- Key lemma 1: finite-alphabet Fano inequality $H(W\mid\hat W)\le H_b(P_e) + P_e\log(|\mathcal W|-1)$.
- Key lemma 2: single-use BEC mutual-information bound $I \le 1-p$.
- Key lemma 3: additivity/data-processing to $I(W;\hat W)\le n(1-p)$, then the rate converse.
- Technical requirements: discrete entropy over `Finset`, chain rule, binary entropy function.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Fano's inequality is finite-combinatorial (finite-alphabet entropy sums) and has a short classical proof.
- The parent already fixes the BEC information quantities; only the converse machinery is missing.
- Main risk is the multi-use data-processing bound, which can be staged after the standalone Fano lemma.

**Estimated Effort**:
- Exploration: 2-3 days (survey Mathlib discrete entropy)
- If tractable: 1-3 weeks (Fano lemma, then BEC converse)
- If hard: the data-processing step may need new Mathlib-level lemmas

## References

### Papers
- R. M. Fano, *Transmission of Information*, MIT Press 1961 — Fano's inequality.
- Cover & Thomas, *Elements of Information Theory*, §2.10, Ch. 7 — Fano and the channel-coding converse.

### Online Resources
- Cover–Thomas Chapter 7 — the converse-by-Fano argument for discrete memoryless channels.

### Mathlib
- `Mathlib.MeasureTheory` / developing information-theory files — discrete entropy substrate.
- `Mathlib.Analysis.SpecialFunctions.Log` — binary entropy and log inequalities.

## Metadata

```yaml
tags:
  - information-theory
  - fano-inequality
  - channel-coding
  - entropy
  - combinatorics
related_proofs:
  - shannon-channel-coding-bec
  - shannon-channel-coding-awgn
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 5/10

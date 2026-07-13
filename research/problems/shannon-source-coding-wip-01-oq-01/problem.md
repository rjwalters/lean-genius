# Problem: Entropy Additivity for n i.i.d. Copies: H(X^n)=n H(X) by Induction

**Slug**: shannon-source-coding-wip-01-oq-01
**Created**: 2026-06-27T11:33:01-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
H\!\left(p^{\otimes n}\right) = n \cdot H(p),
\qquad
p^{\otimes n}(x_1,\dots,x_n) = \prod_{i=1}^{n} p(x_i),
\quad
\sum_x p(x) = 1.
$$

Equivalently, with $H(p) = -\sum_x p(x)\log p(x) = \sum_x \operatorname{negMulLog}(p(x))$, the entropy of the $n$-fold product (i.i.d.) distribution of a single source $p$ equals $n$ times the single-source entropy, for every $n \in \mathbb{N}$.

### Plain Language

The parent proof shows that for two *independent* sources the entropies add: $H(p_X \otimes p_Y) = H(p_X) + H(p_Y)$. This problem asks to iterate that fact to $n$ identical, independent copies of one source. A block of $n$ i.i.d. symbols carries exactly $n$ times the information of a single symbol, so its entropy is $n \cdot H(p)$. The claim is a clean induction on $n$: the base case is $H(p^{\otimes 0}) = 0$ (and $H(p^{\otimes 1}) = H(p)$), and the step peels off one factor with the already-proven pairwise additivity.

### Why This Matters

The identity $H(X^n) = n H(X)$ is the quantitative backbone of Shannon's source coding theorem and the Asymptotic Equipartition Property (AEP): the average number of bits needed per symbol of an i.i.d. source converges to its entropy rate $H(p)$. Pinning the *exact* per-block entropy (not just an asymptotic estimate) makes the "$n \cdot H$ bits" statement fully formal in Lean, turning the pairwise additivity lemma into the entropy-rate foundation that downstream source-coding and AEP formalizations can cite directly.

## Known Results

### What's Already Proven

- `entropy_prod` (pairwise additivity, this gallery, `Proofs/ShannonSourceCodingWIP01.lean`) — $H(p_X \otimes p_Y) = H(p_X) + H(p_Y)$ for product distributions with $\sum p_X = \sum p_Y = 1$, 0 sorries / 0 axioms.
- `entropy_eq_neg_sum` (this gallery, `Proofs/ShannonSourceCodingWIP01.lean`) — the `negMulLog`-form entropy agrees with the standard $-\sum p\log p$.
- `Real.negMulLog_mul` (Mathlib, `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog`) — $\operatorname{negMulLog}(xy) = y\,\operatorname{negMulLog}(x) + x\,\operatorname{negMulLog}(y)$, the linearization engine.

### What's Still Open

- The $n$-fold iteration $H(p^{\otimes n}) = n\,H(p)$ itself (this problem) — not yet formalized.
- The converse direction noted in the parent: additivity characterizes independence (product distributions only), via the chain rule and the equality case of conditioning-reduces-entropy.

### Our Goal

Formalize $H(p^{\otimes n}) = n \cdot H(p)$ in Lean by induction on $n$, reusing `entropy_prod` for the inductive step and a normalization lemma $\sum_{x} p^{\otimes n}(x) = 1$. Scope is exactly this single identity for one source $p$ over a `Fintype`; we do not attempt the converse/characterization.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-source-coding-wip-01 | Direct parent; supplies the pairwise additivity base case `entropy_prod` we iterate | `negMulLog_mul`, `Fintype.sum_prod_type`, marginal collapse via $\sum p = 1$ |
| shannon-entropy | Defines Shannon entropy and proves subadditivity $H(X,Y) \le H(X)+H(Y)$; $n\cdot H$ is the saturated i.i.d. case | `negMulLog`, big-operator sums over `Fintype` |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Induction on $n$ with the product modeled as `Fin n → α` (functions), peeling the last coordinate via `Fin n → α ≃ (Fin (n-1) → α) × α`.
   - Why it might work: `entropy_prod` already handles a single binary product step; the `negMulLog` machinery is dimension-agnostic, and the equiv reduces $p^{\otimes (n+1)}$ to $p^{\otimes n} \otimes p$.
   - Risk: reindexing `Fin (n+1)` and transporting the entropy and the normalization hypothesis across the equiv (`Fintype.sum_equiv` / `Equiv.piFinSucc`) is fiddly bookkeeping.

2. **Approach B**: Induction with the product modeled as nested binary products `(α × (α × ...))`, so each step is literally `entropy_prod` applied to `αⁿ × α` with no `Fin`-reindexing.
   - Why it might work: every step is a verbatim instance of the proven lemma; the carrier type grows by one factor and the normalization $\sum p^{\otimes n} = 1$ follows from `Finset.sum_mul`/`Fintype.sum_prod_type`.
   - Risk: the carrier type changes shape each step, so the statement must be phrased generically (e.g. over an arbitrary normalized $q$ on a `Fintype`, specialized to $p^{\otimes n}$) to make the induction hypothesis applicable.

### Key Difficulties

- Choosing the $n$-fold product encoding (`Fin n → α` vs. nested `×`) so the induction hypothesis matches `entropy_prod`'s exact `(a, b) ↦ pX a * pY b` shape.
- Carrying the normalization side-condition $\sum_x p^{\otimes n}(x) = 1$ through the induction (needed as a hypothesis of `entropy_prod` at each step), proved from $\sum p = 1$ by `Fintype.sum_prod_type` + `Finset.sum_mul`.

### What Would a Proof Need?

- Key lemma 1: a definition of `entropyPow p n` (or product PMF on `Fin n → α`) plus normalization `∑ x, pPow n x = 1`.
- Key lemma 2: the inductive step `entropy (p^{⊗(n+1)}) = entropy (p^{⊗n}) + entropy p` via `entropy_prod` and the chosen reindexing equiv.
- Technical requirements: `Fintype`/`DecidableEq` instances on the product carrier; `Fintype.sum_prod_type`, `Finset.sum_mul`/`Finset.mul_sum`, and `Fintype.sum_equiv`/`Equiv.piFinSucc` for the `Fin`-encoding.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is a textbook induction whose single non-trivial step is *already formalized* (`entropy_prod`); the remaining work is encoding and reindexing, not new mathematics.
- Similar iterate-a-binary-lemma inductions are routine in Mathlib (e.g. `Finset.prod`/`sum` over `Fin n`, `MeasureTheory` product measures), so precedent and tooling exist.
- Mathlib provides the needed `Fintype` big-operator lemmas and product/`Fin`-equiv infrastructure; the main cost is careful PMF/product bookkeeping rather than any hard analysis.

**Estimated Effort**:
- Exploration: a few hours to settle the product encoding and normalization lemma.
- If tractable: 1–3 days for the full induction and a clean statement.
- If hard: if the `Fin n → α` reindexing proves stubborn, fall back to the nested-product phrasing — worst case roughly a week.

## References

### Papers
- C. E. Shannon, "A Mathematical Theory of Communication", 1948 — introduces entropy and the source coding theorem; $H(X^n)=nH(X)$ underlies the entropy rate.
- T. M. Cover & J. A. Thomas, "Elements of Information Theory", 2006 — Ch. 2 (entropy additivity for independent variables) and Ch. 3 (AEP) state the $n\cdot H$ identity.

### Online Resources
- https://en.wikipedia.org/wiki/Asymptotic_equipartition_property — AEP and the entropy rate $H$ of an i.i.d. source.
- https://en.wikipedia.org/wiki/Entropy_(information_theory)#Additivity — additivity of entropy for independent sources.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Log.NegMulLog` — `Real.negMulLog` and `Real.negMulLog_mul`, the per-symbol linearization driving each step.
- `Mathlib.Algebra.BigOperators.Pi` / `Mathlib.Algebra.BigOperators.Ring` — `Fintype.sum_prod_type`, `Finset.sum_mul`, `Finset.mul_sum` for factoring sums and collapsing marginals.
- `Mathlib.Logic.Equiv.Fin` / `Mathlib.Probability.ProbabilityMassFunction` — `Equiv.piFinSucc` style reindexing and PMF product infrastructure for the $n$-fold encoding.

## Metadata

```yaml
tags:
  - information-theory
  - shannon-entropy
  - source-coding
related_proofs:
  - shannon-source-coding-wip-01
  - shannon-entropy
difficulty: medium
source: proof-suggestion
created: 2026-06-27T11:33:01-07:00
```

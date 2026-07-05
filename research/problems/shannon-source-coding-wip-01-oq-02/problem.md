# Problem: Entropy Additivity Converse — Additivity Holds Only for Product Distributions

**Slug**: shannon-source-coding-wip-01-oq-02
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Let $p : \alpha \times \beta \to \mathbb{R}$ be a probability mass function on a finite
product alphabet, with marginals
$p_X(x) = \sum_{y} p(x,y)$ and $p_Y(y) = \sum_{x} p(x,y)$.
Writing $H(p) = \sum_z \operatorname{negMulLog}(p\,z) = -\sum_z p(z)\log p(z)$, prove the
equality case of subadditivity:

$$
H(p) = H(p_X) + H(p_Y)
\quad\Longleftrightarrow\quad
p(x,y) = p_X(x)\,p_Y(y)\ \text{ for all } (x,y).
$$

The parent entry (`shannon-source-coding-wip-01`) proves the $(\Leftarrow)$ direction
(`entropy_prod`: product distributions are additive). This problem is the $(\Rightarrow)$
direction: additivity forces independence.

### Plain Language

Entropy is subadditive: the information in a joint source $(X,Y)$ never exceeds the sum
of the information in $X$ and $Y$ separately, $H(X,Y) \le H(X) + H(Y)$. Equality is
special — it happens exactly when $X$ and $Y$ are independent. We already know the "if"
half (independent sources add). This task nails the "only if" half: if the entropies add
up exactly, the source must have been a product of independent parts.

### Why This Matters

The equality case turns a one-directional inequality into a characterization of
independence purely in terms of entropy. It is the information-theoretic statement that
"no redundancy" ($H(X,Y) = H(X)+H(Y)$) is equivalent to "no dependence." Together with
the parent's forward direction it gives a complete iff, closing the additivity story for
the gallery and providing the equality-case lemma reused by mutual-information results
($I(X;Y) = 0 \iff$ independence).

## Known Results

### What's Already Proven

- `entropy_prod` (parent `shannon-source-coding-wip-01`) — $H(p_X \otimes p_Y) = H(p_X) + H(p_Y)$ for product distributions (the $\Leftarrow$ direction).
- Subadditivity $H(X,Y) \le H(X) + H(Y)$ — standard; provable from concavity of $\log$ / Gibbs' inequality. Sibling `shannon-source-coding-wip-01-oq-01` (n-fold i.i.d., $H(p^{\otimes n}) = n\,H(p)$) is solved and shipped.
- Mathlib: `Real.negMulLog`, `Real.negMulLog_mul`, `Real.add_pow_le_pow_mul_pow_of_sq_le_sq` / strict concavity lemmas; `Real.inner_le_nnorm`-style Jensen tooling; `Finset.inner_mul_le_norm_mul_norm`.

### What's Still Open

- The converse (this problem): $H(p) = H(p_X) + H(p_Y) \Rightarrow p = p_X \otimes p_Y$.
- The mutual-information reformulation $I(X;Y) = 0 \iff$ independence (follow-on).

### Our Goal

Prove the $(\Rightarrow)$ direction as a standalone theorem in a new companion file, using
the same self-contained `entropy p = ∑ negMulLog (p x)` definition as the parent (not
Mathlib's measure-theoretic `measureEntropy`), so it composes directly with `entropy_prod`
into a single iff.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-source-coding-wip-01 | Parent; proves the forward direction `entropy_prod` | `negMulLog`, `negMulLog_mul` linearization |
| shannon-source-coding-wip-01-oq-01 | Sibling; n-fold i.i.d. entropy rate (solved) | induction on product additivity, `Fin.consEquiv` |
| shannon-entropy | Base entropy definitions and Gibbs' inequality | `negMulLog`, concavity |
| shannon-source-coding-oq-01 | Chain rule / conditional entropy building blocks | `condEntropy` |

## Initial Thoughts

### Potential Approaches

1. **Gibbs / KL-divergence equality case**: Write $H(p_X)+H(p_Y) - H(p) = D(p \,\|\, p_X \otimes p_Y) \ge 0$, the relative entropy between the joint and the product of marginals. Then $D = 0 \iff p = p_X \otimes p_Y$ is exactly the equality case of Gibbs' inequality (strict positivity of $\operatorname{negMulLog}$-based KL).
   - Why it might work: reduces the whole problem to the well-known equality case $D(p\|q)=0 \iff p=q$, a single clean lemma.
   - Risk: need a Lean-friendly KL-divergence equality lemma; may have to prove strict concavity / the $t\log t$ equality case by hand.

2. **Direct strict-concavity argument**: Expand $H(p_X)+H(p_Y)-H(p)$ termwise and apply the strict form of Jensen for $\log$, tracking the equality condition ($\log$ strictly concave ⇒ equality forces all arguments equal, i.e. $p(x,y)/(p_X(x)p_Y(y))$ constant $=1$).
   - Why it might work: mirrors the parent's termwise `negMulLog` manipulation.
   - Risk: equality-case bookkeeping over a double sum is fiddly.

### Key Difficulties

- Extracting the *equality* condition from a concavity/Gibbs inequality (Mathlib usually gives the inequality; the strict/equality version may need to be assembled).
- Handling zero-probability atoms ($p(x,y)=0$) cleanly so the $\log$ ratios stay well-defined.

### What Would a Proof Need?

- Key lemma 1: Gibbs equality case — $\sum_z p(z)\log\frac{p(z)}{q(z)} = 0$ with $p,q$ pmfs $\Rightarrow p = q$.
- Key lemma 2: identify $H(p_X)+H(p_Y)-H(p)$ with the KL divergence $D(p \| p_X\otimes p_Y)$.
- Technical requirements: finite alphabets, pmf hypotheses (nonneg, sum-to-one), `negMulLog` arithmetic matching the parent's conventions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The forward direction and all entropy scaffolding already exist in the gallery in a compatible `negMulLog` form.
- The mathematical content is a standard textbook equality case (Cover & Thomas Thm 2.6.5), not a research frontier.
- The one genuine obstacle is the *strict*/equality version of the concavity inequality in Lean; Mathlib has strict-concavity of `log` but the packaged equality case may need assembly.

**Estimated Effort**:
- Exploration: hours to locate the right Mathlib strict-concavity / Jensen equality lemmas.
- If tractable: 1–3 days for the KL-equality route.
- If hard: longer only if the equality case must be built from scratch.

## References

### Papers
- Cover & Thomas, *Elements of Information Theory* (2nd ed.), Thm 2.6.5 (independence bound on entropy and its equality case).

### Online Resources
- Wikipedia, "Conditional entropy" and "Mutual information" — $I(X;Y)=0 \iff$ independence.

### Mathlib
- `Real.negMulLog`, `Real.negMulLog_mul` — entropy term algebra (used by the parent).
- `Real.strictConcaveOn_log` / `StrictConcaveOn` API — equality case of Jensen.
- `Finset.sum` / `Finset.prod` lemmas — double-sum bookkeeping over the product alphabet.

## Metadata

```yaml
tags:
  - information-theory
  - entropy
  - independence
  - convexity
related_proofs:
  - shannon-source-coding-wip-01
  - shannon-source-coding-wip-01-oq-01
  - shannon-entropy
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10

# Problem: Effective Two-Sided Rate for the Diagonal Euler Beta Value

**Slug**: beta-central-binomial-asymptotic-oq-01
**Created**: 2026-07-09T15:40:16-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\exists\, c_1, c_2 > 0,\ \forall n \ge 1:\quad c_1 \cdot \frac{\sqrt{\pi n}}{(2n+1)\,4^{n}} \ \le\ B(n+1, n+1) \ \le\ c_2 \cdot \frac{\sqrt{\pi n}}{(2n+1)\,4^{n}},
$$

where $B(n+1,n+1) = \mathrm{betaDiag}(n) = 1/((2n+1)\,\binom{2n}{n})$ is the diagonal Euler Beta value, and the constants $c_1, c_2$ are explicit rational or elementary closed forms rather than existential black boxes.

### Plain Language

The parent entry proves only that the diagonal Beta value $B(n+1,n+1)$ is *asymptotically equivalent* to $\sqrt{\pi n}/((2n+1)4^{n})$ — the ratio tends to $1$ as $n \to \infty$, but this says nothing about how close the two sides are for any particular finite $n$. This problem asks to strengthen that bare limit into an honest, computable inequality: nail down concrete numerical constants $c_1$ and $c_2$ so that the leading term, scaled by those constants, sandwiches the true Beta value for *every* $n \ge 1$, not merely in the limit.

### Why This Matters

An asymptotic equivalence is qualitative; a two-sided effective bound is quantitative and usable. With explicit constants one can certify the Beta value's size at concrete $n$, feed it into estimates for Catalan-number growth, random-walk return probabilities, and de Moivre–Laplace central-limit error terms, and obtain machine-checkable numerics rather than a limit statement. It also demonstrates that Mathlib's effective Stirling apparatus (the genuine lower bound $\sqrt\pi \le \mathrm{stirlingSeq}\,n$ plus antitonicity) is strong enough to convert a pure `IsEquivalent` into a rate — a reusable pattern for other Stirling-derived asymptotics in the gallery.

## Known Results

### What's Already Proven

- `betaDiag_isEquivalent` (parent entry `beta-central-binomial-asymptotic`) — proves the bare equivalence $B(n+1,n+1) \sim \sqrt{\pi n}/((2n+1)4^{n})$, 0 axioms / 0 sorries.
- `beta-diag-effective-rate` (sibling gallery entry) — **answers this question affirmatively**: it factors $B(n+1,n+1)$ as its leading term times a correction $\mathrm{ratioR}\,n = \mathrm{stirlingSeq}(n)^2/(\sqrt\pi\,\mathrm{stirlingSeq}(2n))$ and pins it to $\sqrt{2\pi}/e \le \mathrm{ratioR}\,n \le e^2/(2\pi)$, giving constants $c_1 \approx 0.922$ and $c_2 \approx 1.176$ valid for all $n \ge 1$ (`ratioR_ge`, `ratioR_le`), 0 axioms / 0 sorries.
- Mathlib `Stirling.stirlingSeq` — supplies $\mathrm{stirlingSeq}\,n \to \sqrt\pi$, the lower bound $\sqrt\pi \le \mathrm{stirlingSeq}\,n$, and antitonicity `stirlingSeq'_antitone`, the raw material for the envelope.

### What's Still Open

- Sharpening the envelope $[\sqrt{2\pi}/e,\, e^2/(2\pi)] \approx [0.922, 1.176]$ toward the tight $1 + O(1/n)$ correction (pursued separately in `beta-central-binomial-explicit-rate`).
- Whether the same effective-envelope method extends to off-diagonal Beta values $B(an+1, bn+1)$ with $a \ne b$.

### Our Goal

Record and cross-reference the affirmative resolution supplied by `beta-diag-effective-rate`: an explicit two-sided rate for $\mathrm{betaDiag}(n)$ with elementary constants $\sqrt{2\pi}/e$ and $e^2/(2\pi)$, valid for all $n \ge 1$, obtained purely from Mathlib's `stirlingSeq` bounds with no new axioms.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| beta-central-binomial-asymptotic | Parent entry; states the bare equivalence this problem upgrades | Wallis ratio identity, `IsEquivalent` congruence transport |
| beta-diag-effective-rate | Sibling that resolves this question with explicit constants | `stirlingSeq` lower bound + antitonicity, exact algebraic factorization |
| beta-central-binomial-explicit-rate | Sharpens the envelope to a $1+O(1/n)$ Landau form | Telescoped Stirling tail bound |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Factor $B(n+1,n+1)$ as leading-term $\times$ correction and bound the correction.
   - Why it might work: this is exactly what `beta-diag-effective-rate` does — write $\mathrm{ratioR}\,n = \mathrm{stirlingSeq}(n)^2/(\sqrt\pi\,\mathrm{stirlingSeq}(2n))$ via an exact identity, then apply the two Mathlib bounds.
   - Risk: the exact identity $\binom{2n}{n}\sqrt n\,\mathrm{stirlingSeq}(n)^2 = \mathrm{stirlingSeq}(2n)\,4^n$ must be manipulated carefully to avoid division-by-zero side goals.

2. **Approach B**: Robbins-style direct $e^{1/(12n+1)} < n!/(\sqrt{2\pi n}(n/e)^n) < e^{1/(12n)}$ bounds.
   - Why it might work: gives sharper, monotone-in-$n$ constants closer to $1$.
   - Risk: Mathlib does not package the Robbins refinement, so it would require proving new Stirling tail estimates from scratch.

### Key Difficulties

- Turning a limit `IsEquivalent` statement into a per-$n$ inequality requires an *exact* algebraic bridge, not just an asymptotic one.
- Obtaining a *two-sided* bound needs both a genuine lower bound and an upper bound for `stirlingSeq`; the upper direction comes only via antitonicity evaluated at $n=1$.

### What Would a Proof Need?

- Key lemma 1: exact identity relating $\binom{2n}{n}$ to `stirlingSeq(n)` and `stirlingSeq(2n)` (the $4^n$ collapse).
- Key lemma 2: two-sided control $\sqrt{2\pi}/e \le \mathrm{ratioR}\,n \le e^2/(2\pi)$ from `stirlingSeq` monotonicity.
- Technical requirements: positivity of `stirlingSeq`, $\binom{2n}{n} > 0$, and careful `field_simp`/`nlinarith` bookkeeping.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The sibling entry `beta-diag-effective-rate` already completes this with 0 axioms and 0 sorries, so the mathematical path is fully validated.
- All required Stirling bounds (`stirlingSeq` lower bound, `stirlingSeq'_antitone`) already exist in Mathlib.
- The only real labor is the exact algebraic factorization and the arithmetic of the constant-factor envelope.

**Estimated Effort**:
- Exploration: hours
- If tractable: days (already realized in the sibling entry)
- If hard: not applicable — resolved

## References

### Papers
- H. Robbins, "A Remark on Stirling's Formula", Amer. Math. Monthly 62 (1955) — sharp two-sided factorial bounds $e^{1/(12n+1)} < n!/(\sqrt{2\pi n}(n/e)^n) < e^{1/(12n)}$.
- J. Wallis, "Arithmetica Infinitorum", 1656 — origin of the $\pi/2$ product underlying the $\sqrt{\pi n}$ rate.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Stirling.html — Mathlib's Stirling sequence and its convergence.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Stirling` — provides `Stirling.stirlingSeq`, its limit $\sqrt\pi$, the lower bound, and antitonicity used to build the envelope.
- `Mathlib.Analysis.SpecialFunctions.Gamma.Beta` — the complex Euler Beta integral that `betaDiag` is identified with.

## Metadata

```yaml
tags:
  - analysis
  - asymptotics
  - beta-function
  - stirling
  - wallis
  - central-binomial
  - research
related_proofs:
  - beta-central-binomial-asymptotic
  - beta-diag-effective-rate
  - beta-central-binomial-explicit-rate
difficulty: medium
source: proof-suggestion
created: 2026-07-09T15:40:16-07:00
```

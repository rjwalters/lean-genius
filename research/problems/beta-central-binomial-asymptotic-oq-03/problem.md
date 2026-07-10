# Problem: Wallis/Stirling Asymptotics of Off-Diagonal Beta Values B(an+1, bn+1)

**Slug**: beta-central-binomial-asymptotic-oq-03
**Created**: 2026-07-09T17:03:07-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Fix integers } a \ge b \ge 1 \text{ with } a \ne b. \quad
B(an+1,\, bn+1) \;=\; \frac{(an)!\,(bn)!}{((a+b)n+1)!}.
$$

Writing $H(a,b) = (a+b)\log(a+b) - a\log a - b\log b$ for the (integer-scaled) binary entropy, the conjecture is
$$
B(an+1,\, bn+1) \;\sim\; \frac{\sqrt{2\pi}}{\,(a+b)\,}\;\sqrt{\frac{ab}{(a+b)\,n}}\;\cdot\; e^{-H(a,b)\,n}\;\cdot\;\frac{1}{(a+b)n}, \qquad n \to \infty,
$$
in the sense of `Asymptotics.IsEquivalent`, generalizing the diagonal case $a=b=1$ (where $H(1,1)=2\log 2$, so $e^{-H\,n}=4^{-n}$) proved in the parent entry.

### Plain Language

The parent gallery entry proves that the *diagonal* Euler Beta value $B(n+1,n+1)$ decays like $\sqrt{\pi n}\,4^{-n}/(2n+1)$, extracted from Stirling's formula through a clean "Wallis ratio" collapse. This problem asks whether the *off-diagonal* values $B(an+1,\,bn+1)$ with $a \ne b$ (for example $B(2n+1,\,n+1)$) admit exactly the same treatment. Because $B(an+1,bn+1) = (an)!\,(bn)!/((a+b)n+1)!$ is again a pure ratio of factorials, feeding each factorial through Mathlib's Stirling equivalence should produce a single asymptotic with an *exponential* rate governed by the binary entropy $H(a,b)$ instead of the constant $4$, and a $1/\sqrt{n}$ polynomial factor whose constant now depends on $a$ and $b$.

### Why This Matters

Off-diagonal Beta asymptotics are the analytic heart of the Laplace/saddle-point estimates behind large-deviation rates for the binomial distribution: $B(an+1,bn+1)$ is (up to the normalizing binomial coefficient) the tail weight of a $\mathrm{Beta}(an+1,bn+1)$ density peaking at $t = a/(a+b) \ne 1/2$, and its exponential decay rate is precisely the relative entropy $H(a,b)$. Establishing the general asymptotic in Lean would (i) show the parent's Wallis-ratio method is not a diagonal coincidence but a genuine template, (ii) supply a reusable `IsEquivalent` lemma for the entropy-rate decay of general Beta values that Mathlib lacks, and (iii) connect the entry to the de Moivre–Laplace / Sanov circle of ideas via a fully machine-checked route.

## Known Results

### What's Already Proven

- `beta-central-binomial-asymptotic` (parent) — the diagonal case $a=b=1$: $C(2n,n)\sim 4^n/\sqrt{\pi n}$ (`centralBinom_isEquivalent`) and $B(n+1,n+1)\sim \sqrt{\pi n}/((2n+1)4^n)$ (`betaDiag_isEquivalent`), assembled from `Stirling.factorial_isEquivalent_stirling`. 0 axioms, 0 sorries.
- Mathlib `Stirling.factorial_isEquivalent_stirling`: $n! \sim \sqrt{2\pi n}\,(n/e)^n$ — the sole analytic input; it is a congruence-friendly `IsEquivalent` statement.
- Classical analysis: the Laplace/saddle-point method gives $B(an+1,bn+1) \asymp e^{-H(a,b)n}$ with $H(a,b)$ the binary relative entropy; this is textbook but is *not* stated in Mathlib in `IsEquivalent` form.

### What's Still Open

- No Lean statement of the general off-diagonal asymptotic $B(an+1,bn+1)\sim c(a,b)\,n^{-3/2}\,e^{-H(a,b)n}$ exists (diagonal or off-diagonal), even for a single fixed pair like $(a,b)=(2,1)$.
- Whether the parent's purely-algebraic `stirling_ratio_identity` collapse generalizes cleanly, or whether the mismatched exponents $a^{an}$, $b^{bn}$, $(a+b)^{(a+b)n}$ force a genuinely new bookkeeping step (the $e$-powers cancel, but the base-power product no longer simplifies to a single $4^n$).
- The exact polynomial prefactor constant $c(a,b)$ in the fully normalized form (getting the $\sqrt{2\pi}$, the $\sqrt{ab/(a+b)}$, and the $1/((a+b)n)$ from the trailing "$+1$" all correct simultaneously).

### Our Goal

Prove, for at least one fixed off-diagonal pair (target: $(a,b) = (2,1)$, i.e. $B(2n+1,\,n+1)$), the `IsEquivalent` asymptotic with exponential rate $e^{-H(2,1)n} = (4/27\cdot 27)\dots$ — concretely $e^{-H(2,1)} = 4/27$ so the rate is $(4/27)^n$ — and the correct $n^{-3/2}$ prefactor, reusing the parent's transport-of-equivalence architecture. A general-$a,b$ statement is the stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| beta-central-binomial-asymptotic | Direct parent: diagonal $a=b=1$ case; supplies the Wallis-ratio/Stirling transport method to be generalized | `Asymptotics.IsEquivalent`, `Stirling.factorial_isEquivalent_stirling`, algebraic ratio identity |
| beta-central-binomial | Provides the closed form $B(n+1,n+1)=1/((2n+1)C(2n,n))$ and Beta-integral identification underpinning the off-diagonal factorial ratio | Euler Beta integral, factorial identities |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Direct factorial-ratio transport (mirror the parent).**
   Write $B(an+1,bn+1) = (an)!\,(bn)!/((a+b)n+1)!$ exactly, then compose `Stirling.factorial_isEquivalent_stirling` with the linear maps $n\mapsto an$, $n\mapsto bn$, $n\mapsto (a+b)n$ and take the quotient (`IsEquivalent` is a congruence for products/quotients/composition).
   - Why it might work: it is exactly the parent's route; every factorial becomes $\sqrt{2\pi\cdot} (\cdot/e)^{\cdot}$ and the $e$-exponents cancel because $an + bn = (a+b)n$.
   - Risk: the surviving base-power product $a^{an}b^{bn}/(a+b)^{(a+b)n} = e^{-H(a,b)n}$ no longer collapses to a rational $4^{-n}$, so the "clean" `stirling_ratio_identity` must be replaced by an `exp`/`log` manipulation; also the trailing "$+1$" in $((a+b)n+1)!$ needs a `Nat.factorial_succ` step to expose $((a+b)n)!$.

2. **Approach B — Reduce to central binomial via a ratio to the parent.**
   Study $B(an+1,bn+1)/B(n+1,n+1)$ or express the general Beta value through generalized central binomial coefficients $\binom{(a+b)n}{an}$ and reuse the parent's $C(2n,n)$ equivalence as a black box, only proving the *correction* factor asymptotic.
   - Why it might work: isolates the genuinely new content (the entropy rate) into one lemma while reusing verified parent lemmas.
   - Risk: the correction factor still contains $a^{an}b^{bn}$-type terms, so it does not obviously simplify; may add algebraic overhead without removing the core difficulty.

### Key Difficulties

- The base-power product does not rationalize: $a^{an}b^{bn}/(a+b)^{(a+b)n}$ must be handled as $\exp(-H(a,b)n)$, requiring `Real.exp`/`Real.log` and `Real.rpow` bookkeeping the diagonal proof avoided.
- Correctly tracking the polynomial prefactor: the three $\sqrt{2\pi\cdot}$ factors give $\sqrt{2\pi an}\sqrt{2\pi bn}/\sqrt{2\pi (a+b)n} = \sqrt{2\pi ab n/(a+b)}$, and the "$+1$" in the denominator factorial and Beta arguments must be shepherded through `IsEquivalent` (they are lower-order but must be shown so).
- Keeping everything inside `Asymptotics.IsEquivalent` congruence lemmas rather than dropping to $\varepsilon$–$\delta$.

### What Would a Proof Need?

- Key lemma 1: an exact real identity $B(an+1,bn+1) = (an)!\,(bn)!/((a+b)n+1)!$ (or via a generalized central binomial coefficient), analogous to `centralBinom_cast`.
- Key lemma 2: a "Stirling triple-ratio" identity isolating the entropy rate, $\big(\tfrac{an}{e}\big)^{an}\big(\tfrac{bn}{e}\big)^{bn}/\big(\tfrac{(a+b)n}{e}\big)^{(a+b)n} = e^{-H(a,b)n}$, the analogue of `stirling_ratio_identity`.
- Technical requirements: `IsEquivalent` congruence for products/quotients/composition; `Real.rpow`/`Real.exp`/`Real.log` lemmas; `Nat.factorial_succ` to peel the trailing $+1$; positivity of $a,b,a+b$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The parent diagonal proof is fully verified (0 axioms, 0 sorries) and provides a near-complete template; the delta is replacing one rational collapse by an `exp/log` collapse.
- Similar transports of `Stirling.factorial_isEquivalent_stirling` already succeed in the gallery (parent entry, plus the explicit-rate follow-ons `BetaCentralBinomialExplicitRate*`), so the machinery is known to work.
- The main new obstacle — handling $a^{an}b^{bn}/(a+b)^{(a+b)n}$ as $e^{-H(a,b)n}$ — is standard `Real.log`/`Real.rpow` algebra available in Mathlib, not a research-level gap.

**Estimated Effort**:
- Exploration: 1–2 days (confirm the factorial identity and the triple-ratio collapse for $(a,b)=(2,1)$).
- If tractable: 1–2 weeks for a fixed pair; longer for a fully general-$a,b$ statement.
- If hard: the general-$a,b$ prefactor bookkeeping could balloon; unknown.

## References

### Papers
- W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. 1 (1968) — de Moivre–Laplace and Stirling-based binomial asymptotics; source of the entropy-rate heuristic $e^{-H(a,b)n}$.
- N. G. de Bruijn, *Asymptotic Methods in Analysis* (1958) — Laplace/saddle-point derivation of Beta-function and factorial-ratio asymptotics.

### Online Resources
- https://dlmf.nist.gov/5.11 — DLMF §5.11, asymptotic expansions of the Gamma and Beta functions (ratios of Gamma functions with large arguments).
- https://en.wikipedia.org/wiki/Beta_function — closed forms and integral representation of $B(x,y)$.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Stirling` — `Stirling.factorial_isEquivalent_stirling`, the sole analytic input.
- `Mathlib.Analysis.Asymptotics.AsymptoticEquivalent` — `Asymptotics.IsEquivalent` and its product/quotient/composition congruence lemmas.
- `Mathlib.Analysis.SpecialFunctions.Gamma.Beta` — the complex Euler Beta integral `Complex.betaIntegral` anchoring the analytic meaning.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` / `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.rpow`, `Real.exp`, `Real.log` for the entropy-rate manipulation.

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
  - beta-central-binomial
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:03:07-07:00
```

# Problem: Complete `normal_imp_irrational` in Lean 4, eliminating the axiom

**Slug**: e-transcendental-oq-02-oq-06
**Created**: 2026-07-04T12:34:40-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall\,b \ge 2,\ \forall\,x \in \mathbb{R},\quad \text{Normal}_b(x) \;\Rightarrow\; x \notin \mathbb{Q}.
$$

Here $\text{Normal}_b(x)$ means every finite block of $k$ base-$b$ digits occurs in the
base-$b$ expansion of $x$ with asymptotic density $b^{-k}$.

### Plain Language

A real number is *normal* in base $b$ when its digits are equidistributed: each digit
appears with frequency $1/b$, each pair of digits with frequency $1/b^2$, and so on.
Rational numbers have eventually periodic expansions, so their digit blocks cannot be
equidistributed. We want a fully machine-checked Lean 4 proof that normality forces
irrationality, replacing the `axiom` currently used as a placeholder in the
`e-transcendental-oq-02` gallery entry.

### Why This Matters

The gallery entry "Is e a Normal Number?" axiomatizes `normal_imp_irrational` so that the
downstream discussion of the (open) normality of $e$ can proceed. Discharging this axiom
removes an assumption from an otherwise self-contained entry and contributes a reusable
Mathlib-style lemma connecting digit equidistribution to irrationality.

## Known Results

### What's Already Proven

- Rationals have eventually periodic base-$b$ expansions — classical; partially in Mathlib via `Nat.Periodic`/decimal-expansion lemmas.
- Periodic expansions fail equidistribution — the block frequencies converge to rational multiples determined by the period, not to $b^{-k}$.

### What's Still Open

- A clean Lean statement of `Normal_b` (density of digit blocks) that is convenient to reason about.
- The contrapositive: eventually periodic $\Rightarrow$ not normal, formalized to close the axiom.

### Our Goal

Formalize the contrapositive `x ∈ ℚ ⇒ ¬ Normal_b x` for a fixed base $b \ge 2$ and derive
`normal_imp_irrational`, removing the axiom from the companion file.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| e-transcendental-oq-02 | parent entry that currently axiomatizes this lemma | digit expansions, Borel normality |
| algebraic-reals-meager-oq-02-oq-01 | measure/category arguments about real number sets | Baire category, measure zero |

## Initial Thoughts

### Potential Approaches

1. **Contrapositive via periodicity**: show a rational's base-$b$ expansion is eventually
   periodic with period $p$, hence the density of any block is a rational number with
   denominator dividing $p$; pick a block whose density differs from $b^{-k}$.
   - Why it might work: periodicity is decidable and finite to analyze.
   - Risk: formalizing "asymptotic density of a block" cleanly is fiddly.

2. **Single-digit weakening first**: prove the weaker `Normal_b ⇒ ¬(eventually periodic)`
   using only single-digit frequencies, which already contradicts periodicity for most rationals.
   - Why it might work: avoids the general block-density machinery.
   - Risk: pure repunits/edge cases where single-digit frequency happens to be $1/b$.

### Key Difficulties

- Defining asymptotic digit-block density and its basic limit lemmas in Lean.
- Handling the two base-$b$ representations of terminating rationals ($0.0999\ldots = 0.1$).

### What Would a Proof Need?

- Key lemma 1: rational $\Rightarrow$ eventually periodic base-$b$ expansion.
- Key lemma 2: eventually periodic $\Rightarrow$ block densities are period-determined rationals.
- Technical requirements: a workable `digitDensity` definition and Cesàro-limit lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is elementary and finite (periodicity), not the open normality of $e$.
- Mathlib has decimal/`b`-adic expansion scaffolding and density/`Filter.Tendsto` tools.
- The main cost is definitional plumbing for block density, not a deep theorem.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1-2 weeks
- If hard: unknown (density plumbing could balloon)

## References

### Papers
- É. Borel, "Les probabilités dénombrables et leurs applications arithmétiques" (1909) — origin of normal numbers.

### Online Resources
- https://en.wikipedia.org/wiki/Normal_number — definitions and basic properties.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` and `b`-adic expansion lemmas — digit machinery.
- `Filter.Tendsto` / `Nat.card` density tools — asymptotic frequencies.

## Metadata

```yaml
tags:
  - number-theory
  - normal-numbers
  - irrationality
  - analysis
  - borel
related_proofs:
  - e-transcendental-oq-02
  - algebraic-reals-meager-oq-02-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-07-04T12:34:40-07:00
```

**Significance**: 6/10
**Tractability**: 6/10

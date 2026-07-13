# Problem: Complete the Lean Formalization of Erdős #54 (Ramsey 2-Complete Sets)

**Slug**: erdos-54-wip-01
**Created**: 2026-07-09T17:33:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
g(N) \;=\; \min \{\, |A \cap [1,N]| \;:\; A \text{ is Ramsey 2-complete} \,\} \;=\; \Theta\big((\log N)^2\big)
$$

Here a set $A \subseteq \mathbb{N}$ is *Ramsey 2-complete* if for every $2$-colouring of $A$ there is a colour class whose subset sums cover all sufficiently large integers. Conlon–Fox–Pham (2021) proved the sharp growth rate $\Theta((\log N)^2)$. The formalization goal is to encode this statement faithfully in Lean 4 and discharge as many supporting lemmas as possible from proved Mathlib facts, isolating only the deep combinatorial bounds as named assumptions.

### Plain Language

A set of whole numbers is called Ramsey 2-complete when, no matter how you split it into two colours, at least one colour can still add up (using subset sums) to every large enough number. This project completes and hardens the existing Lean formalization of the Conlon–Fox–Pham theorem, which says the sparsest such sets grow like the square of the logarithm. We are not re-proving the theorem from scratch; we are tightening the Lean file so that routine claims are machine-checked and only the genuinely deep results remain stated as clearly-labelled axioms.

### Why This Matters

1. **Sharp Extremal Rate**: The $\Theta((\log N)^2)$ answer pins down exactly how sparse a Ramsey-complete set can be, resolving a question Erdős raised in 1995.
2. **Partition-Robust Completeness**: It connects classical complete-sequence theory to Ramsey theory, showing subset-sum completeness can survive an adversarial 2-colouring.
3. **Formalization Hygiene**: Separating the routine counting-function lemmas from the two deep bounds makes the Lean entry a credible, auditable record of what is and is not machine-checked.

## Known Results

### What's Already Proven

- Conlon–Fox–Pham (2021) upper bound: there exist Ramsey 2-complete sets with $O((\log N)^2)$ elements below $N$ — stated in the gallery Lean file as `conlon_fox_pham`.
- Matching lower bound $c(\log N)^2$ for any Ramsey 2-complete set — stated as the `burr_erdos_lower` assumption.
- Historical Burr–Erdős upper bound of order $(2\log_2 N)^3$ — captured as `burr_erdos_upper`.
- Basic definitions (`Colouring2`, `monoSubsetSums`, `IsRamsey2Complete`, `countingFn`) already type-check with 0 sorries.

### What's Still Open

- The exact multiplicative constant in the $c(\log N)^2$ lower bound.
- Whether an explicit (derandomized) construction attains the optimal rate.
- The analogous minimum growth rate for Ramsey $k$-complete sets with $k \ge 3$.

### Our Goal

Strengthen `Proofs/Erdos54Problem.lean` toward `verified` by (1) proving from Mathlib the routine monotonicity and lower-bound facts about `countingFn` built on `Finset.Icc`, (2) checking that `monoSubsetSums` and `IsRamsey2Complete` correctly encode the intended quantifiers, and (3) reducing the axiom surface to exactly the two Conlon–Fox–Pham bounds, documenting each remaining assumption precisely in `meta.json`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-54 | Parent gallery entry being completed | Finset.Icc counting, subset-sum completeness, Ramsey 2-colourings |
| erdos-30 | Related additive-combinatorics extremal count with matching-order bounds | Finset arithmetic, additive-combinatorics growth estimates |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Discharge the counting-function lemmas directly.
   - Why it might work: `countingFn N = (A.filter (· ≤ N)).card` is monotone and bounded by Mathlib's `Finset.card_le_card` and `Finset.Icc` cardinality lemmas, so many auxiliary claims need no new mathematics.
   - Risk: Encoding subtleties (off-by-one in `Finset.Icc`, coercions to `ℝ` for the $(\log N)^2$ comparison) can make even routine steps fiddly.

2. **Approach B**: Refactor the two deep bounds into a single `Erdos54Axioms` structure.
   - Why it might work: Bundling `conlon_fox_pham` and `burr_erdos_lower` as structure fields makes the assumption count explicit and lets the main $\Theta$ statement be derived cleanly.
   - Risk: Per the Axiom Integrity Policy this does not reduce the mathematical assumption count; it must be reflected honestly in `axiomCount`.

### Key Difficulties

- The Conlon–Fox–Pham bounds rely on the probabilistic method and are far beyond current Mathlib automation, so they must remain axioms.
- Real-valued asymptotics ($\Theta((\log N)^2)$) require careful handling of `Nat.log` versus `Real.log` and eventual-inequality bookkeeping.

### What Would a Proof Need?

- Key lemma 1: monotonicity and boundedness of `countingFn` from `Finset.card_le_card`.
- Key lemma 2: a faithful statement that `IsRamsey2Complete` implies covering of all large integers by one colour class's subset sums.
- Technical requirements: consistent coercion between `Nat.log`/`Real.log`, and a documented `Θ`-comparison combining the two axiomatized bounds.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The routine counting lemmas are within reach of Mathlib's `Finset` API and standard `omega`/`gcongr` automation.
- The deep bounds are famously hard (Conlon–Fox–Pham) and are not the target; only their faithful statement and clean combination are.
- Mathlib provides `Finset.Icc`, `Nat.log`, and big-operator lemmas that cover the mechanical parts.

**Estimated Effort**:
- Exploration: one to two days to map the axiom surface and encoding.
- If tractable: about one week to discharge the routine lemmas and tighten definitions.
- If hard: the deep bounds remain axiomatized indefinitely.

## References

### Papers
- Conlon, Fox, Pham, "Subset sums, completeness and colorings," 2021 — proves the sharp $\Theta((\log N)^2)$ growth rate.
- Burr, Erdős, "Completeness properties of perturbed sequences," J. Number Theory, 1985 — origin of the completeness framework and earlier bounds.

### Online Resources
- https://erdosproblems.com/54 — canonical statement and status of Erdős Problem #54.

### Mathlib
- Mathlib.Data.Finset.LocallyFinite — `Finset.Icc` closed integer intervals for the counting function.
- Mathlib.Data.Nat.Log — `Nat.log` for the logarithmic growth comparisons.
- Mathlib.Algebra.BigOperators.Group.Finset — `Finset.sum` for subset-sum definitions.

## Metadata

```yaml
tags:
  - erdos
  - ramsey-theory
  - additive-combinatorics
  - complete-sequences
  - number-theory
  - formalization
  - extremal-combinatorics
related_proofs:
  - erdos-54
  - erdos-30
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:19-07:00
```

**Significance**: 7/10
**Tractability**: 6/10

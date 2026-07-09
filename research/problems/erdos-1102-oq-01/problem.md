# Problem: Do the sequences 2ⁿ − 1 have property P

**Slug**: erdos-1102-oq-01
**Created**: 2026-07-09T15:40:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
A = \{\, 2^n - 1 : n \ge 1 \,\} \;\overset{?}{\in}\; P \quad\text{where}\quad P = \Bigl\{ A : \forall n \ge 1,\; \bigl|\{\, a \in A : \mu^2(n + a) = 1 \,\}\bigr| < \infty \Bigr\}.
$$

### Plain Language

Erdős's property P asks: for a set of integers A, is it true that for every fixed shift n ≥ 1 only finitely many elements a of A make n + a squarefree? Equivalently, each translate A + n eventually avoids squarefree numbers entirely. This open question asks whether the specific fast-growing sequence of Mersenne-type numbers 2ⁿ − 1 = 1, 3, 7, 15, 31, 63, 127, … satisfies property P.

### Why This Matters

Property P is one of the two extremal squarefree conditions Erdős introduced in Problem #1102, resolved in general by van Doorn–Tao (2025): P-sequences must have density 0. But density 0 alone does not decide any particular sparse sequence, and 2ⁿ − 1 grows exponentially, so it is a natural test case that van Doorn–Tao list as unresolved. Deciding it would sharpen our understanding of how additive shifts interact with squarefree distribution for multiplicatively structured sequences, and connects to classical questions about squarefree values of 2ⁿ − 1 (e.g. Wieferich-prime obstructions to squarefreeness).

## Known Results

### What's Already Proven

- van Doorn–Tao (2025): every sequence with property P has natural density 0 — arXiv preprint "Squarefree properties P and Q"
- The density of squarefree integers is 6/π² = 1/ζ(2) — classical (Basel problem / Mirsky 1947)
- Q-sequences have upper density at most 6/π², achieved by the squarefree numbers themselves — van Doorn–Tao (2025), formalized in gallery entry `erdos-1102`

### What's Still Open

- Whether A = {2ⁿ − 1 : n ≥ 1} has property P (this problem)
- Whether the factorial sequences n! ± 1 have property P — Erdős, listed in `erdos-1102` open questions
- Behaviour of the variant properties P′ and P′∞ for these specific sequences

### Our Goal

Formalize a precise Lean 4 statement of the assertion "{2ⁿ − 1 : n ≥ 1} has property P", reusing the `propertyP` predicate and `powersOfTwoMinus1` definition already present in `Proofs/Erdos1102Problem.lean`, and either establish the implication toward it that is provable or record it as a stated conjecture with the supporting finiteness lemmas needed to attack it.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1102 | Parent entry defining properties P and Q; already contains `propertyP` and `powersOfTwoMinus1` | Squarefree density, axiomatized van Doorn–Tao Q result |
| erdos-1103 | Squarefree sumsets — complementary squarefree-translate question | Sieve / density arguments |
| erdos-969 | Error term in squarefree counting — precision of the 6/π² constant | Analytic squarefree distribution |
| erdos-208 | Gaps between squarefree numbers — local squarefree distribution | Counting squarefree integers |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Direct finiteness via forbidden residues. For a fixed n, show that n + (2ᵏ − 1) is divisible by a fixed prime square for all but finitely many k by exploiting periodicity of 2ᵏ mod p².
   - Why it might work: 2ᵏ is eventually periodic modulo any prime power, so n + 2ᵏ − 1 lands in a fixed residue class infinitely often; if that class is divisible by p² we get non-squarefreeness.
   - Risk: Guaranteeing a single p² covering *all* large k for every n is not obviously possible; residues cycle but need not always hit a square divisor.

2. **Approach B**: Reduce to a covering-system / Wieferich argument. Assemble finitely many prime squares p² whose associated residues of 2ᵏ cover every sufficiently large exponent, giving a covering system that forces n + 2ᵏ − 1 non-squarefree.
   - Why it might work: Covering systems are the standard tool for exponential sequences (à la Erdős's covering congruences), and only finitely many exceptions need excluding.
   - Risk: No covering system may exist for a given n; existence is exactly what is open, so this may hit the genuine mathematical obstruction.

### Key Difficulties

- Squarefreeness of n + 2ᵏ − 1 depends on square divisors p², whose behaviour under the map k ↦ 2ᵏ mod p² is delicate (order of 2 modulo p²).
- The problem is genuinely open, so a full resolution is unlikely; the tractable target is a faithful formalization plus provable partial lemmas.

### What Would a Proof Need?

- Key lemma 1: periodicity of k ↦ 2ᵏ mod m and its multiplicative order, available from `ZMod` / `orderOf` in Mathlib.
- Key lemma 2: a criterion linking a fixed square divisor p² of n + 2ᵏ − 1 to an arithmetic progression of exponents k.
- Technical requirements: `Nat.Squarefree`, `Nat.factorization`, `ZMod`, and finiteness (`Set.Finite`) infrastructure.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The underlying number-theoretic question is unresolved even in the literature (listed open by van Doorn–Tao).
- Covering-system techniques for 2ⁿ ± c are subtle and partial in general.
- Mathlib provides `ZMod`, `orderOf`, and `Squarefree`, so a formal *statement* and small partial lemmas are within reach, but a full proof is a moonshot-adjacent effort.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 2–4 weeks for meaningful partial results
- If hard: unknown (matches open status)

## References

### Papers
- van Doorn, Floris; Tao, Terence, "Squarefree properties P and Q", 2025 — resolves Erdős #1102 in general and lists 2ⁿ − 1 as an open special case
- Erdős, Paul, "Problems and results in combinatorial number theory", 1981 (Astérisque 94) — original source of properties P and Q
- Mirsky, Leon, "On the frequency of pairs of square-free numbers with a given difference", 1947 — squarefree-difference distribution underpinning the density 6/π²

### Online Resources
- https://erdosproblems.com/1102 — canonical statement and status of Erdős Problem #1102

### Mathlib
- Mathlib.NumberTheory.Squarefree — `Squarefree` predicate for the translate condition
- Mathlib.Data.ZMod.Basic — modular reduction of 2ᵏ needed for periodicity arguments
- Mathlib.GroupTheory.OrderOfElement — order of 2 modulo prime powers

## Metadata

```yaml
tags:
  - number-theory
  - squarefree
  - analytic-number-theory
  - density
  - erdos
related_proofs:
  - erdos-1102
  - erdos-1103
  - erdos-969
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:19-07:00
```

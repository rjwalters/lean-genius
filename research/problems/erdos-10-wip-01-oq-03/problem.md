# Problem: Covering-Congruence Construction for Even Integers Outside S₃

**Slug**: erdos-10-wip-01-oq-03
**Created**: 2026-07-03
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\exists\, a, m \in \mathbb{N},\ m > 0,\quad \forall\, t \in \mathbb{N},\ (a + t m)\ \text{is even and}\ (a + t m) \notin S_3,
$$

where $S_3 = \{\, p + 2^{k_1} + 2^{k_2} + 2^{k_3} : p\ \text{prime or } 0,\ k_i \ge 0 \,\}$ is the set of integers representable as a prime plus at most three powers of two.

### Plain Language

The Erdős #10 thread studies which integers can be written as a prime plus a bounded number of powers of two. Using a *covering system* — a finite set of congruences whose union is all of $\mathbb{Z}$ — one can force an entire arithmetic progression to avoid such representations. The goal is to formalize that covering-congruence construction to exhibit infinitely many **even** integers that are **not** in $S_3$.

### Why This Matters

Covering systems are the classical tool (Erdős, 1950) proving a positive proportion of integers are not of the form $2^k + p$. Formalizing the construction for $S_3$ turns "infinitely many" into an explicit, machine-checked arithmetic progression and demonstrates covering-system reasoning in Lean, for which Mathlib has no direct analogue yet.

## Known Results

### What's Already Proven

- `RepWithAtMost` subadditivity and binary-popcount subadditivity — parent entry `erdos-10-wip-01`.
- `isPrimePlusKPowers_iff_popcount` characterization (O(log) form of the Erdős #10 predicate) — parent entry.
- Erdős (1950): a covering system yields an arithmetic progression of odd integers none of the form $2^k + p$.

### What's Still Open

- A fully formal covering-system construction in Lean producing an AP inside the complement of $S_3$.
- Making the residues/moduli explicit enough to be `decide`-checkable for the even, $\le 3$-powers case.

### Our Goal

Construct explicit even $a$ and $m$ together with a covering system certifying $a + tm \notin S_3$ for all $t$, then formalize the correctness proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-10-wip-01 | Direct parent; supplies the $S_3$ predicate and popcount lemmas | Additive representation, binary popcount |
| erdos-10 | Erdős #10 main thread on powers-of-two representations | Covering congruences |

## Initial Thoughts

### Potential Approaches

1. **Explicit small covering system**: fix congruences so that on each residue class membership in $S_3$ is blocked by a fixed prime obstruction.
   - Why it might work: reduces the universal claim to finitely many congruence checks.
   - Risk: the per-class prime obstruction may require large moduli.

2. **Reduction to the odd case**: double a known odd construction and track how $S_3$ membership behaves under doubling.
   - Why it might work: leverages Erdős's original odd construction.
   - Risk: doubling can re-introduce power-of-two summands.

### Key Difficulties

- Enforcing the exact bound of $\le 3$ powers of two throughout the argument.
- Certifying non-representability uniformly across a residue class.

### What Would a Proof Need?

- Key lemma 1: a covering system whose union is $\mathbb{Z}$, with a completeness proof.
- Key lemma 2: a per-class obstruction lemma ruling out $p + 2^{k_1}+2^{k_2}+2^{k_3}$.
- Technical requirements: modular arithmetic, finite case analysis over `Nat`/`ZMod`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Covering-system formalizations are rare in Mathlib and need bespoke completeness arguments.
- The bounded-power constraint adds case explosion beyond the classical $2^k + p$ setting.
- Parent-entry infrastructure (popcount, representation lemmas) already exists.

**Estimated Effort**:
- Exploration: days
- If tractable: weeks
- If hard: unknown

## References

### Papers
- P. Erdős, "On integers of the form $2^k + p$ and some related problems", Summa Brasil. Math. (1950) — original covering-system construction.
- A. Granville, K. Soundararajan — work on prime-plus-powers-of-two representations (source of the $S_3$ framing).

### Online Resources
- Erdős Problems database, Problem #10 — https://www.erdosproblems.com/10

### Mathlib
- `ZMod`, `Nat.ModEq` — modular arithmetic for covering congruences.
- `Nat.digits` / popcount infrastructure — powers-of-two bookkeeping.

## Metadata

```yaml
tags:
  - number-theory
  - covering-congruences
  - additive-combinatorics
  - erdos-problem
related_proofs:
  - erdos-10-wip-01
  - erdos-10
difficulty: high
source: proof-suggestion
created: 2026-07-03
```

**Significance**: 6/10
**Tractability**: 5/10

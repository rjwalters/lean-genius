# Problem: Exact Value g₃(N) = 2 via a Size-(N+1) Construction and Matching Upper Bound

**Slug**: erdos-866-wip-01-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- open question of the parent erdos-866-wip-01 -->

## Problem Statement

### Formal Statement

$$
g_3(N) = 2:\quad
\exists\, A \subseteq \{1,\ldots,N+1\}\ \text{(size } N+1)\ \text{with no forbidden } 3\text{-term pairwise-sum configuration}
\ \wedge\ \text{every larger set contains one, forcing } g_3(N) = 2.
$$

### Plain Language

The parent proof establishes a uniform parity lower bound g_k(N) ≥ 1 for all k ≥ 3. For k = 3 the exact value is known to be g₃(N) = 2. This problem asks to prove that exact value: exhibit an explicit construction realizing the lower side (a set of size N+1 avoiding the forbidden triple of pairwise sums), and establish the matching upper bound so that the two pin g₃(N) to exactly 2.

### Why This Matters

It upgrades a one-sided parity bound into a tight, exact result — the strongest possible statement for the k = 3 case of Erdős #866 — and demonstrates the construction/upper-bound pincer that the parent framework was built to support. Exact values are far more citable than one-sided bounds.

## Known Results

### What's Already Proven

- The uniform parity lower bound g_k(N) ≥ 1 for all k ≥ 3 — parent `erdos-866-wip-01` (axiomatized parent framework; this child targets the concrete k = 3 exact value).

### What's Still Open (in the gallery)

- The explicit size-(N+1) construction with no forbidden triple.
- The matching upper bound giving g₃(N) ≤ 2.

### Our Goal

Formalize both halves for k = 3: (1) a concrete construction (e.g., an interval or arithmetic-progression-based set) of size N+1 avoiding the forbidden configuration, and (2) the pigeonhole/parity upper bound forcing any larger set to contain it, yielding g₃(N) = 2.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-866-wip-01 | Direct parent; parity lower-bound framework and definitions | parity argument, pigeonhole, pairwise sums |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Explicit construction + pigeonhole upper bound (recommended)**: pin down the exact combinatorial object g₃ counts from the parent's definitions, give the extremal set explicitly (guided by the known g₃(N) = 2 result), verify it avoids the forbidden triple by a direct/`decide`-style parity check on the construction, and prove the upper bound by the same parity/pigeonhole argument the parent uses for the ≥ 1 bound, pushed to ≥ 2.
   - Why it might work: the value is known and small; the construction is explicit and the upper bound reuses parent machinery.
   - Risk: reconciling the parent's exact definition of g_k and the "forbidden triple" so the k = 3 statement is faithful.

### Key Difficulties

- Faithfully restating the parent's (axiomatized) definitions for the concrete k = 3 case.
- Making the avoidance check and the upper bound fully constructive (no residual sorry).

### What Would a Proof Need?

- Key lemma 1: the explicit size-(N+1) set avoids the forbidden 3-configuration.
- Key lemma 2: any set of size > N+1 contains the configuration (upper bound).
- Technical requirements: `Finset`, pigeonhole (`Finset.exists_ne_map_eq_of_card_lt_of_maps_to`), parity.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Known exact value with a small, explicit extremal construction.
- Upper bound reuses the parent's parity/pigeonhole idea.
- Main risk is definitional faithfulness to the axiomatized parent, not proof difficulty.

**Estimated Effort**:
- Exploration: hours–1 day
- If tractable: 2–5 days

## References

### Papers
- Erdős problem #866 (pairwise sums / g_k(N)); see the parent entry's references for the exact-value source.

### Mathlib
- `Mathlib.Combinatorics.Pigeonhole` — pigeonhole principle.
- `Mathlib.Data.Finset.*`, `Mathlib.Algebra.Parity` — finite sets and parity.

## Metadata

```yaml
tags:
  - erdos-problems
  - additive-combinatorics
  - pairwise-sums
  - extremal-combinatorics
related_proofs:
  - erdos-866-wip-01
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

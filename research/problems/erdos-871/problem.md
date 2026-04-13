# Problem: Erdős #871: Partitioning Additive Bases of Order 2

## Statement

### Plain Language
Erdős asked: if A ⊆ ℕ is an additive basis of order 2 with representation function r_A(n) → ∞,
can A always be partitioned into two disjoint additive bases of order 2?

**Answer: NO.** Disproved by Daniel Larsen (2026), using an extension of the
Erdős-Nathanson (1989) blocking construction.

### Formal Statement
```
∃ A : Set ℕ, IsAdditiveBasis2 A ∧ RepTendsToInfty A ∧ ¬CanPartitionIntoBases A
```

where:
- `IsAdditiveBasis2 A` = A + A covers all sufficiently large naturals
- `RepTendsToInfty A` = r_A(n) = #{(a,b) ∈ A×A : a+b=n} → ∞
- `CanPartitionIntoBases A` = A = B ∪ C, B∩C=∅, both B, C additive bases of order 2

## Classification

```yaml
tier: A
significance: 7
tractability: 7
tags:
  - erdos
  - disproved
  - additive-combinatorics
  - additive-bases
  - partitions
  - representation-function
  - larsen-2026
```

**Significance**: 7/10
**Tractability**: 7/10

## Current Lean Status

File: `proofs/Proofs/Erdos871Problem.lean`

**3 axioms remaining** (down from 4 — one was proved as theorem):

1. `erdos_nathanson_1989`: There exists a basis A with r_A(n) ≥ t for all large n,
   that cannot be partitioned into two bases. (Acta Arithmetica LII, 1989)

2. `erdos_nathanson_positive`: Partition IS possible when r_A(n) > c·log n for
   c > (log 4/3)⁻¹ ≈ 3.48. (Positive direction from same 1989 paper)

3. `larsen_construction_blocking`: The Larsen 2026 construction has the "blocking
   property" — r_A(n) → ∞ but A cannot be partitioned.

## Why This Matters

1. **Recent result**: Larsen's 2026 disproof is very recent; formalizing it in Lean
   would be a notable contribution alongside the paper itself.
2. **Reducible axioms**: The blocking property and positive direction may be partially
   tractable via density/combinatorial arguments in Mathlib.
3. **Mathlib tools**: `Mathlib.Combinatorics.Additive` has sumset and basis machinery.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| erdos-871 | Main gallery proof (parent) |
| erdos-1 | Additive basis techniques |
| erdos-131 | Representation function methods |

## Research Focus

**Primary goal**: Reduce axiom count from 3 to 2 or fewer.

**Best target**: `larsen_construction_blocking` — constructive argument that may
be formalized step-by-step from the explicit Larsen 2026 construction.

**Secondary**: Survey whether Mathlib has density lemmas usable for
`erdos_nathanson_positive` (the log growth positive direction).

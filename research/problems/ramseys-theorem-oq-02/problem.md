# Problem: Improve Ramsey Upper Bound R(r,s) ≤ C(r+s-2,r-1) in Lean

**Slug**: ramseys-theorem-oq-02
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-open-question

## Problem Statement

### Plain Language

The standard upper bound for Ramsey numbers is R(r,s) ≤ C(r+s-2, r-1) (proved by
the probabilistic/greedy argument). Can we do better? In particular, formalize the
improved bound due to Thomason (1988) or prove the (4,4) Ramsey number R(4,4) = 18
exactly in Lean. Even just tightening the existing bound formula in `RamseysTheorem.lean`
to a better constant would be valuable.

### Formal Statement

```lean
-- Current gallery bound (sketch):
theorem ramsey_upper : R r s ≤ Nat.choose (r + s - 2) (r - 1)

-- Target: improved bound or exact value
theorem ramsey_4_4 : R 4 4 = 18 := by sorry

-- Or: Thomason's improvement for symmetric case
theorem ramsey_improved (k : ℕ) : R k k ≤ (4 - ε) ^ k * ... := by sorry
```

### Why This Matters

The Ramsey number problem is a central topic in combinatorics (Wiedijk #65 area).
Exact values are notoriously hard — R(4,4) = 18 is known but its proof involves a
computer-assisted search. Formalizing even R(3,3) = 6 exactly (the dinner party problem)
in Lean would be a valuable gallery addition, extending `RamseysTheorem.lean`.

## Known Results

### What's Already Proven

- `RamseysTheorem.lean`: existence of Ramsey numbers (∀ r s, ∃ N, R r s ≤ N)
- `RamseyR4k.lean`: R(4,k) bounds
- Standard upper bound R(r,s) ≤ C(r+s-2, r-1) via induction

### Our Goal

Formalize either:
1. R(3,3) = 6 exactly (more tractable — only needs graphs on 5 and 6 vertices)
2. Or: derive any asymptotic improvement over the binomial coefficient bound

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ramseys-theorem | Base Ramsey proof | Finset, graph coloring, pigeonhole |
| ramseys-theorem-oq-04 | R(4,k) bounds | Related techniques |

## Initial Thoughts

### Potential Approaches

1. **R(3,3) = 6 exactly**: Prove lower bound (5-vertex 2-coloring with no monochromatic
   triangle) + upper bound (6 vertices forces one). Both are finite case checks.
   - Lean: use `Finset.decidableMem` and `decide` for small cases

2. **R(4,4) = 18 by search**: Requires a verified computer search — likely needs
   a verified SAT solver or brute-force Lean `decide` on small graphs

### Key Difficulties

- Lower bounds require explicit graph constructions (Lean `SimpleGraph` terms)
- R(4,4) by brute force requires very large `decide` calls (may not terminate)
- R(3,3) = 6 should be feasible with `decide` on small Finsets

## Tractability Assessment

**Difficulty**: Medium for R(3,3) = 6, Hard for R(4,4) = 18.

**Recommended starting point**: Prove R(3,3) = 6 as a concrete finite verification.

## Metadata

```yaml
tags:
  - combinatorics
  - graph-theory
  - ramsey-theory
  - wiedijk-100
  - extension
  - finite-combinatorics
related_proofs:
  - ramseys-theorem
  - ramseys-theorem-oq-04
difficulty: medium
source: gallery-open-question
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 4/10

# Erdős Problem #3: Arithmetic Progressions in Large Sets

**Lean file**: `proofs/Proofs/Erdos3Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: A | **Significance**: 8/10 | **Tractability**: 4/10

## Problem Statement

Erdős Conjecture #3: If $\sum_{a \in A} 1/a$ diverges, then A contains arithmetic progressions of every finite length.

**Status**: OPEN — one of the most important open problems in combinatorics.

## The Sorry

```lean
theorem required_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → RequiredBound k) → Erdos3Conjecture := by
  intro hbound A hdiv
  intro k
  -- If r_k(N) = o(N / log N), then any set with divergent reciprocal sum
  -- cannot avoid k-APs because its counting function grows too fast
  sorry
```

**Context**: `RequiredBound k` says `r_k(N) = o(N / log N)`. `Erdos3Conjecture` says every A with divergent sum contains k-APs. The sorry is the logical implication.

## Mathematical Content

This is an implication theorem: "If the Roth-type bound `r_k(N) = o(N/log N)` holds, then Erdős #3 follows."

The argument: If A has divergent sum and |A ∩ [1,N]| ≥ cN/log N for some c, then A contains k-APs by the bound assumption.

## Why This Might Be Provable

Even though Erdős #3 itself is open, this conditional implication might be formalizable:
- If `|A ∩ [1,N]| = Ω(N/log N)`, we need to show A has k-APs
- With `RequiredBound k`, `r_k(N) = o(N/log N)` means dense sets have k-APs
- The connection: divergent sum implies density Ω(N/log N) by a Cauchy-condensation type argument

The challenge is formalizing the density argument and connecting `RequiredBound` to the AP conclusion.

## Approach

1. Read the full file — what is `rothNumber`, `RequiredBound`, `Erdos3Conjecture`?
2. Understand the gap between `RequiredBound` and `Erdos3Conjecture`
3. Key step: divergent sum → `|A ∩ [1,N]| / (N/log N) → ∞`?
4. Apply `RequiredBound` to conclude AP existence

## Related Gallery Proof

- `src/data/proofs/erdos-3/` — Erdős Problem #3
- `proofs/Proofs/Erdos3Problem.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos3Problem.lean` fully — understand all definitions
2. Find what `RequiredBound` and `Erdos3Conjecture` state precisely
3. Look for density lower bound lemmas already in the file
4. Check if there's a direct path from divergence to density ≥ N/log N

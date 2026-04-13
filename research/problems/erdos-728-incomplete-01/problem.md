# Erdős Problem #728: Factorial Divisibility with Logarithmic Gap

**Lean file**: `proofs/Proofs/Erdos728Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 6/10 | **Tractability**: 6/10

## Problem Statement

Erdős #728: Are there integers a, b, n with a,b > εn, a!·b! | n!·(a+b-n)!, and n + C·log(n) < a+b < n + C'·log(n)?

**Status**: SOLVED — Barreto & ChatGPT-5.2 proved infinitely many solutions exist.

## The Sorry

```lean
theorem erdos_728_exists (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/4)
    (C C' : ℝ) (hC : 0 < C) (hC' : C < C') :
    ∃ a b n : ℕ, isErdos728Solution a b n ε C C' := by
  have h := erdos_728_resolution
  -- This follows from the resolution
  sorry
```

**Context**: `erdos_728_resolution` is already proved in the file. The sorry just needs to extract the existence from it.

## Approach

1. Read `erdos_728_resolution` — what is its type? It likely asserts existence.
2. If `erdos_728_resolution : ∃ a b n, isErdos728Solution a b n ε C C'` (or similar), just use `exact h` or `obtain ⟨a, b, n, h'⟩ := h; exact ⟨a, b, n, h'⟩`
3. May need to adjust ε, C, C' parameters

## Key Lean Tactics

- `obtain ⟨a, b, n, h'⟩ := erdos_728_resolution`
- `exact ⟨a, b, n, h'⟩`
- May need `apply Exists.intro` with specific witnesses

## Related Gallery Proof

- `src/data/proofs/erdos-728/` — Erdős Problem #728
- `proofs/Proofs/Erdos728Problem.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos728Problem.lean` fully
2. Find `erdos_728_resolution` definition — what exactly does it state?
3. Check if the sorry theorem directly follows from `erdos_728_resolution`
4. Look at parameter types to see if there's a type mismatch to resolve

# Erdős Problem #290: Denominator Non-Monotonicity in Harmonic Sums

**Lean file**: `proofs/Proofs/Erdos290Problem.lean`
**Sorries**: 2
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 4/10

## Problem Statement

Erdős #290: Let a ≥ 1. Must there exist b > a such that the reduced denominator of $\sum_{a \leq n \leq b} 1/n$ is strictly larger than that of $\sum_{a \leq n \leq b+1} 1/n$?

**Status**: SOLVED — van Doorn (2024) proved b(a) always exists with b(a) < 4.374a.

## The Sorries

### Sorry 1: van Doorn's theorem
```lean
noncomputable def bFunction (a : ℕ) : ℕ :=
  Nat.find (van_doorn_existence a)
where
  van_doorn_existence : ∀ a, ∃ b, HasDenominatorDrop a b := by
    intro a
    sorry -- van Doorn's theorem
```

### Sorry 2: Specific computation
```lean
· sorry -- harmonicDenom computation
```

## Mathematical Content

- `HasDenominatorDrop a b`: the denominator of $\sum_{n=a}^{b} 1/n$ > denominator of $\sum_{n=a}^{b+1} 1/n$
- van Doorn proved: for each a, b = some value ≤ 4.374a works
- The example: ∑_{3≤n≤5} 1/n = 47/60 (denom 60) > denom of ∑_{3≤n≤6} 1/n = 19/20 (denom 20)

## Approach

### For Sorry 2 (harmonicDenom computation)
This is likely a concrete calculation. Read the context to see if `norm_num` or `decide` applies.

### For Sorry 1 (van Doorn's theorem)
This needs the non-trivial mathematical content. Consider:
1. Use the explicit construction: b = 2·3^{k+1} - 1 when a ∈ (3^k, 3^{k+1}]
2. Formalize the example first, then generalize
3. Or: use the weaker bound that some such b exists by number theory

## Related Gallery Proof

- `src/data/proofs/erdos-290/` — Erdős Problem #290
- `proofs/Proofs/Erdos290Problem.lean` — file with sorries

## First Steps (OBSERVE phase)

1. Read `Erdos290Problem.lean` fully
2. Find Sorry 2's exact context (line ~137) — may be a `norm_num` computation
3. Check what `harmonicDenom` is defined as
4. For Sorry 1: can we use the explicit example (a=3, b=5) as a base case?

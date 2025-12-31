# Problem: Irrationality of √2 + √3

**Slug**: sqrt2-plus-sqrt3-irrational
**Created**: 2025-12-31T11:10:20-08:00
**Status**: Active
**Source**: user-request

## Problem Statement

### Formal Statement

$$
\sqrt{2} + \sqrt{3} \notin \mathbb{Q}
$$

### Plain Language

The sum of the square root of 2 and the square root of 3 is irrational. Even though both √2 and √3 are individually irrational, we need to prove that their sum cannot be expressed as a ratio of integers.

### Why This Matters

- Demonstrates that irrational numbers don't "cancel out" when added
- Classic example requiring algebraic manipulation beyond simple root proofs
- Foundational result in algebraic number theory

## Known Results

### What's Already Proven

- √2 is irrational — `Mathlib.Data.Real.Irrational.irrational_sqrt_two`
- √3 is irrational — `Mathlib.Data.Real.Irrational.Nat.Prime.irrational_sqrt`
- Sum of irrational + rational is irrational — `Irrational.add_rat`

### What's Still Open (in our gallery)

- Sums of distinct irrational square roots

### Our Goal

Prove that √2 + √3 is irrational using Mathlib.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sqrt2-irrational | Individual root irrationality | Parity argument, Mathlib |
| cube-root-2-irrational | n-th root irrationality | `irrational_nrt_of_notint_nrt` |

## Initial Thoughts

### Potential Approaches

1. **Contradiction via algebraic manipulation**
   - Assume √2 + √3 = p/q rational
   - Square: 5 + 2√6 = p²/q²
   - Rearrange: √6 = (p²/q² - 5)/2
   - This gives √6 rational, contradiction!
   - Risk: Need √6 irrational in Mathlib

2. **Minimal polynomial approach**
   - The minimal polynomial of √2 + √3 over ℚ is x⁴ - 10x² + 1
   - This is irreducible over ℚ, so √2 + √3 is algebraic of degree 4
   - Degree > 1 implies irrational
   - Risk: Need irreducibility machinery

3. **Direct Mathlib theorem**
   - Check if Mathlib has theorems about sums of square roots
   - Risk: May not exist

### Key Difficulties

- Need to combine two irrationality results
- Algebraic manipulation in ℝ can be tricky in Lean

### What Would a Proof Need?

- Key lemma: √6 is irrational (follows from non-perfect-square)
- Algebraic identity: (√2 + √3)² = 5 + 2√6
- Closure: If √2 + √3 = r rational, then √6 = (r² - 5)/2 is rational

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Standard contradiction argument
- All components likely in Mathlib (√6 irrational, algebraic manipulation)
- Similar techniques to existing proofs

**Estimated Effort**:
- Exploration: 30 min (search Mathlib)
- If tractable: 1-2 hours

## References

### Mathlib
- `Mathlib.Data.Real.Irrational` — irrationality definitions and lemmas
- `Mathlib.Data.Real.Sqrt` — square root properties
- `irrational_sqrt_natCast_iff` — √n irrational iff n not perfect square

## Metadata

```yaml
tags:
  - number-theory
  - irrationality
  - algebraic-numbers
related_proofs:
  - sqrt2-irrational
  - cube-root-2-irrational
difficulty: low-medium
source: user-request
created: 2025-12-31T11:10:20-08:00
```

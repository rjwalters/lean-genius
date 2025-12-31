# Knowledge Base: sqrt2-plus-sqrt3-irrational

## Key Insight

**Pattern: Sums of square roots → reduce to single square root irrationality**

If √a + √b = r (rational), then squaring gives:
- a + 2√(ab) + b = r²
- √(ab) = (r² - a - b) / 2

The RHS is rational, so √(ab) would be rational. If ab is not a perfect square, contradiction!

## Proof Strategy

1. **Assume** √2 + √3 = r (rational)
2. **Square**: (√2 + √3)² = 2 + 2√6 + 3 = 5 + 2√6 = r²
3. **Isolate**: √6 = (r² - 5) / 2
4. **Contradiction**: (r² - 5)/2 is rational, but √6 is irrational (6 not perfect square)

## Mathlib Theorems Used

| Theorem | Purpose |
|---------|---------|
| `irrational_sqrt_natCast_iff` | √n irrational iff n not perfect square |
| `IsSquare` | Predicate for perfect squares |
| `native_decide` | Compute `¬ IsSquare 6` |
| `sqrt_mul` | √a · √b = √(ab) for a ≥ 0 |
| `sq_sqrt` | (√a)² = a for a ≥ 0 |

## Generalization

This technique works for proving √a + √b is irrational whenever:
1. a, b > 0
2. ab is not a perfect square

Examples that would work:
- √2 + √5 (since 10 not perfect square)
- √3 + √5 (since 15 not perfect square)
- √2 + √7 (since 14 not perfect square)

## Tactical Notes

- Use `ring_nf` before `rw [sq_sqrt ...]` to simplify algebraic expressions
- Use `simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast]` for rational casting
- `linarith` handles the linear algebra for isolating √6

## Date

2025-12-31 - Proof completed in ~30 minutes

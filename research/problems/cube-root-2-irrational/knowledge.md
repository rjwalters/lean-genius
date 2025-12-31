# Knowledge Base: cube-root-2-irrational

## Problem Understanding

### Initial Assumptions
What we thought the problem was:
- Need complex multiplicity argument (like √2 proof mentions)
- Might need Eisenstein criterion or Rational Root Theorem
- Parity argument won't work for cubes

### Actual Structure
What we discovered:
- Mathlib has a simpler theorem: `irrational_nrt_of_notint_nrt`
- Only need to prove: (1) x^n = m, (2) x is not an integer
- The "not an integer" proof reduces to "2 is not a perfect cube"

### The "Aha" Moment
The key insight that unlocked the solution:
- The `irrational_nrt_of_notint_nrt` theorem is simpler than multiplicity-based approaches
- Proving "2 is not a perfect cube" just requires checking n ∈ {1} (bound elimination)

---

## Insights

### Theorems That Worked

| Theorem | Module | When to Use |
|---------|--------|-------------|
| `irrational_nrt_of_notint_nrt` | `Mathlib.Data.Real.Irrational` | Prove n-th roots irrational when base isn't perfect power |
| `Real.rpow_natCast` | `Mathlib.Analysis.SpecialFunctions.Pow.Real` | Convert between `rpow` and `^` |
| `Real.rpow_mul` | `Mathlib.Analysis.SpecialFunctions.Pow.Real` | Simplify `(x^a)^b = x^(a*b)` |

### Tactic Pattern: nlinarith with powers
```lean
-- Problem: nlinarith fails on n^k expressions
-- Solution: nlinarith handles products, not powers
have : n ^ 3 = n * n * n := by ring
rw [this]
nlinarith
```

### Tactic Pattern: Bound elimination for perfect powers
```lean
-- When: Proving "m is not a perfect k-th power" for small m
have h1 : 0 < n := by  -- eliminate n ≤ 0
  by_contra h; push_neg at h
  have : n ^ k ≤ 0 := by [rewrite to product, nlinarith]
  omega
have h2 : n < bound := by  -- eliminate n ≥ bound
  by_contra h; push_neg at h
  have : n ^ k ≥ bound^k := by [rewrite to product, nlinarith]
  omega
-- Now n in small range
have : n = only_option := by omega
```

### Tactic Pattern: Real power identity
```lean
-- Proving (m^(1/n))^n = m for real rpow
unfold my_nrt_def
rw [← Real.rpow_natCast]
rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ m)]
norm_num
```

---

## Dead Ends

### Approaches NOT Taken
| Approach | Why We Skipped It |
|----------|-------------------|
| Multiplicity argument | `irrational_nrt_of_notint_nrt` was simpler |
| Eisenstein criterion | Overkill for single irrationality |
| Rational Root Theorem | More complex than needed |

### Tactics That Failed
| Tactic | Why It Failed | Alternative |
|--------|---------------|-------------|
| `interval_cases n` (initially) | No bounds on n established | Manually prove bounds first |
| `nlinarith` on `n^3` directly | Doesn't understand powers | Rewrite to `n*n*n` first |

---

## Generalizations

This proof pattern applies to:
- ∛3, ∛5, ∛6, ... (any non-perfect cube)
- ⁴√2, ⁴√3, ... (any non-perfect 4th power)
- General: m^(1/n) where m is not k^n for any integer k

For variants, change:
- The base m (adjust bounds accordingly)
- The exponent n (adjust perfect power check)

---

## Future Research

- ∛3 is irrational (direct application)
- Replace axiom `cbrt_two_irrational` in GelfondSchneider.lean
- Create helper theorem `irrational_nrt_of_not_perfect_power`

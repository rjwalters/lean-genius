# Tactic Patterns

Reusable tactic patterns discovered during research.

---

## Arithmetic Tactics

### nlinarith with Powers
**Discovered**: cube-root-2-irrational (2025-12-30)

**Problem**: `nlinarith` fails on `n ^ k` expressions

**Solution**: Rewrite powers to products first
```lean
-- nlinarith can't handle n ^ 3 directly
have : n ^ 3 = n * n * n := by ring
rw [this]
nlinarith  -- Now works!
```

**When to use**: Any time nlinarith gives "failed to prove" on expressions with powers

### omega for Integer Bounds
**Use when**: Need to prove `n = k` from `a < n < b`
```lean
have h1 : 0 < n := by ...
have h2 : n < 2 := by ...
have : n = 1 := by omega
```

---

## Type Coercion Tactics

### exact_mod_cast
**Use when**: Goal has different numeric type than hypothesis
```lean
-- Goal: (n : ℝ) ^ 3 = 2
-- Have: (n : ℤ) ^ 3 = 2
exact_mod_cast h
```

### norm_cast
**Use when**: Need to normalize casts in goal or hypothesis
```lean
-- Simplifies nested casts
norm_cast
```

### push_cast
**Use when**: Need to push casts through operations
```lean
-- (↑n + ↑m : ℝ) becomes ↑(n + m)
push_cast
```

---

## Real Power Tactics

### Converting rpow to ^
**Use when**: Working with `Real.rpow` but need natural power
```lean
rw [← Real.rpow_natCast]
-- Now (x : ℝ) ^ (n : ℕ) becomes Real.rpow x n
```

### Simplifying Power Expressions
```lean
-- For (x^a)^b = x^(a*b)
rw [← Real.rpow_mul h_nonneg]
norm_num  -- Simplify the exponent arithmetic
```

---

## Linear Algebra Tactics

### linear_combination for Algebraic Sums
**Discovered**: hurwitz-three-square-impossibility (2025-12-30)

**Problem**: `nlinarith` times out on complex inner product expansions

**Solution**: Use `linear_combination` with explicit coefficients
```lean
-- Proving ⟨u,w⟩ = c₁*d₁ + c₂*d₂ + c₃*d₃ from orthonormality
linear_combination c₁ * d₁ * hv1v1 + c₂ * d₂ * hv2v2 + c₃ * d₃ * hv3v3 +
  (c₁ * d₂ + c₂ * d₁) * hv1v2 + (c₁ * d₃ + c₃ * d₁) * hv1v3 + (c₂ * d₃ + c₃ * d₂) * hv2v3
```

**When to use**: Bilinear Parseval identity proofs, inner product expansions, sums of coefficients

### Matrix Invertibility Pattern
**Discovered**: hurwitz-three-square-impossibility (2025-12-30)

**Problem**: Need to show matrix M is invertible from M^T*M = I

**Solution**: Use determinant and invertibleOfIsUnitDet
```lean
-- From M^T * M = I, derive det(M)² = 1, hence det(M) ≠ 0
have hdet : M.det ≠ 0 := by
  have : M.det ^ 2 = 1 := by
    calc M.det ^ 2 = M.det * M.det := by ring
      _ = M.det * M.transpose.det := by rw [Matrix.det_transpose]
      _ = (M.transpose * M).det := by rw [Matrix.det_mul]
      _ = (1 : Matrix _ _ ℝ).det := by rw [hMTM]
      _ = 1 := Matrix.det_one
  nlinarith [sq_nonneg M.det]

have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
have hMinv : Invertible M := Matrix.invertibleOfIsUnitDet M hunit
```

**When to use**: Proving vectors span a space, orthonormal bases are complete

---

## Syntax Patterns

### set_option Placement
**Discovered**: hurwitz-three-square-impossibility (2025-12-30)

**Problem**: `set_option maxHeartbeats N` causes "unexpected token" error

**Solution**: Place `set_option ... in` BEFORE the docstring, not after
```lean
-- WRONG:
/-- My lemma -/
set_option maxHeartbeats 400000 in  -- ERROR!
lemma my_lemma : ...

-- CORRECT:
set_option maxHeartbeats 400000 in
/-- My lemma -/
lemma my_lemma : ...
```

**When to use**: Any proof needing extended heartbeat budget

---

## Problem Sources

| Problem | Date | Patterns Added |
|---------|------|----------------|
| cube-root-2-irrational | 2025-12-30 | nlinarith+powers, omega bounds, exact_mod_cast, rpow |
| hurwitz-three-square-impossibility | 2025-12-30 | linear_combination, matrix invertibility, set_option syntax |

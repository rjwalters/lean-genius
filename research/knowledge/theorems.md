# Mathlib Theorems

Useful theorems organized by topic, discovered during research.

---

## Irrationality

### irrational_nrt_of_notint_nrt
**Module**: `Mathlib.Data.Real.Irrational`

**Signature**:
```lean
theorem irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ)
    (hxr : x ^ n = m) (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x
```

**When to use**: Prove n-th roots are irrational when base is not a perfect power

**Example**: Proving ∛2 is irrational
```lean
apply irrational_nrt_of_notint_nrt 3 2
· exact_mod_cast cbrt2_cubed  -- x^3 = 2
· exact cbrt2_not_int          -- x is not an integer
· norm_num                      -- 3 > 0
```

**Discovered**: cube-root-2-irrational (2025-12-30)

---

### Nat.Prime.irrational_sqrt
**Module**: `Mathlib.Data.Real.Irrational`

**When to use**: Prove √p is irrational for prime p

---

## Real Powers

### Real.rpow_natCast
**Module**: `Mathlib.Analysis.SpecialFunctions.Pow.Real`

**Use**: Convert between `Real.rpow` and natural power `^`

### Real.rpow_mul
**Module**: `Mathlib.Analysis.SpecialFunctions.Pow.Real`

**Signature**: `(x^a)^b = x^(a*b)` for non-negative x

---

## Problem Sources

| Problem | Date | Theorems Added |
|---------|------|----------------|
| cube-root-2-irrational | 2025-12-30 | irrational_nrt_of_notint_nrt, Real.rpow_* |

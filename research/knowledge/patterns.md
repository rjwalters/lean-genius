# Proof Patterns

Reusable proof patterns discovered during research. Use these to accelerate similar problems.

---

## Pattern: n-th Root Irrationality

**ID**: `nrt-irrational`
**Keywords**: irrational, root, cube root, square root, nth root, radical

### When to Use
- Proving ⁿ√m is irrational for integer m
- m is not a perfect n-th power (no integer k where k^n = m)

### Key Theorem
```lean
irrational_nrt_of_notint_nrt {x : ℝ} (n : ℕ) (m : ℤ)
    (hxr : x ^ n = m) (hv : ¬∃ y : ℤ, x = y) (hnpos : 0 < n) : Irrational x
```
**Module**: `Mathlib.Data.Real.Irrational`

### Template
```lean
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace CubeRoot{{M}}Irrational

noncomputable def cbrt{{M}} : ℝ := ({{M}} : ℝ) ^ (1/3 : ℝ)

theorem cbrt{{M}}_cubed : cbrt{{M}} ^ 3 = {{M}} := by
  unfold cbrt{{M}}
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ {{M}})]
  norm_num

theorem {{M}}_not_perfect_cube : ¬ ∃ (n : ℤ), n ^ 3 = {{M}} := by
  intro ⟨n, hn⟩
  have h1 : 0 < n := by
    by_contra h; push_neg at h
    have : n ^ 3 = n * n * n := by ring
    have hn3 : n ^ 3 ≤ 0 := by rw [this]; nlinarith
    omega
  have h2 : n < {{UPPER_BOUND}} := by
    by_contra h; push_neg at h
    have : n ^ 3 = n * n * n := by ring
    have hn3 : n ^ 3 ≥ {{UPPER_BOUND}}^3 := by rw [this]; nlinarith
    omega
  -- Check remaining candidates
  {{CANDIDATE_CHECK}}

theorem cbrt{{M}}_not_int : ¬ ∃ (n : ℤ), cbrt{{M}} = n := by
  intro ⟨n, hn⟩
  have h : n ^ 3 = {{M}} := by
    have h1 : cbrt{{M}} ^ 3 = {{M}} := cbrt{{M}}_cubed
    rw [hn] at h1
    exact_mod_cast h1
  exact {{M}}_not_perfect_cube ⟨n, h⟩

theorem irrational_cbrt{{M}} : Irrational cbrt{{M}} := by
  apply irrational_nrt_of_notint_nrt 3 {{M}}
  · exact_mod_cast cbrt{{M}}_cubed
  · exact cbrt{{M}}_not_int
  · norm_num

end CubeRoot{{M}}Irrational
```

### Parameter Guide

| Parameter | Description | How to Determine |
|-----------|-------------|------------------|
| `{{M}}` | The integer under the radical | Given in problem |
| `{{UPPER_BOUND}}` | Smallest k where k³ > M | Find k: (k-1)³ ≤ M < k³ |
| `{{CANDIDATE_CHECK}}` | Check remaining n values | For each n in [1, UPPER_BOUND-1], verify n³ ≠ M |

### Examples

| Problem | M | Upper Bound | Candidates | Check |
|---------|---|-------------|------------|-------|
| ∛2 | 2 | 2 | n=1 | 1³=1≠2 ✓ |
| ∛3 | 3 | 2 | n=1 | 1³=1≠3 ✓ |
| ∛5 | 5 | 2 | n=1 | 1³=1≠5 ✓ |
| ∛7 | 7 | 2 | n=1 | 1³=1≠7 ✓ |
| ∛9 | 9 | 3 | n=1,2 | 1³=1≠9, 2³=8≠9 ✓ |
| ∛10 | 10 | 3 | n=1,2 | 1³=1≠10, 2³=8≠10 ✓ |

### Source Problems
- `cube-root-2-irrational` (2025-12-30) — First discovery
- `cube-root-3-irrational` (2025-12-30) — Pattern confirmed

### Success Rate
**2/2 (100%)** — Both applications succeeded on first attempt

### Variations

#### 4th Root Variant
Change exponent from 3 to 4:
- `(1/3 : ℝ)` → `(1/4 : ℝ)`
- `n ^ 3` → `n ^ 4`
- `n * n * n` → `n * n * n * n`
- Upper bound: find k where k⁴ > M

#### General n-th Root
- Exponent: `(1/n : ℝ)`
- Power: `n ^ k`
- Product: repeat `n *` k times
- Adjust bounds based on n

---

## Pattern: [Future Pattern Placeholder]

*Add new patterns as they're discovered*

---

## Pattern Index

| ID | Name | Keywords | Success Rate |
|----|------|----------|--------------|
| nrt-irrational | n-th Root Irrationality | irrational, root, cube, radical | 2/2 (100%) |

---

## How to Use This File

1. **When starting a new problem**: Search keywords in this file
2. **If pattern matches**: Copy template, fill parameters
3. **If no pattern matches**: Use full OODA loop, document new pattern
4. **After success**: Update pattern with new source problem

---

*Last updated: 2025-12-30*

# Mathlib Exploration Protocol

Systematic approach to finding relevant Mathlib theorems before attempting proofs.

## Quick Reference: Common Modules

### Number Theory
| Topic | Module | Key Theorems |
|-------|--------|--------------|
| Irrationality | `Mathlib.Data.Real.Irrational` | `irrational_nrt_of_notint_nrt`, `Nat.Prime.irrational_sqrt` |
| Primes | `Mathlib.Data.Nat.Prime.Basic` | `Nat.Prime`, `Nat.minFac_prime` |
| Divisibility | `Mathlib.Algebra.Divisibility.Basic` | `dvd_antisymm`, `dvd_trans` |
| GCD/LCM | `Mathlib.Algebra.GCDMonoid.Basic` | `gcd_comm`, `lcm_dvd_iff` |
| Modular arithmetic | `Mathlib.Data.ZMod.Basic` | `ZMod.val_cast_of_lt` |

### Real Analysis
| Topic | Module | Key Theorems |
|-------|--------|--------------|
| Powers | `Mathlib.Analysis.SpecialFunctions.Pow.Real` | `Real.rpow_natCast`, `Real.rpow_mul` |
| Roots | `Mathlib.Analysis.SpecialFunctions.Pow.NNReal` | `NNReal.rpow_natCast_mul` |
| Limits | `Mathlib.Topology.Order.Basic` | `tendsto_atTop` |
| Continuity | `Mathlib.Topology.Basic` | `Continuous.comp` |

### Algebra
| Topic | Module | Key Theorems |
|-------|--------|--------------|
| Polynomials | `Mathlib.RingTheory.Polynomial.Basic` | `Polynomial.degree`, `Polynomial.roots` |
| Rational Root | `Mathlib.RingTheory.Polynomial.RationalRoot` | `Polynomial.isRoot_of_mem_roots` |
| Irreducibility | `Mathlib.RingTheory.Polynomial.Eisenstein.Basic` | `Polynomial.Irreducible` |

### Set Theory
| Topic | Module | Key Theorems |
|-------|--------|--------------|
| Cardinality | `Mathlib.SetTheory.Cardinal.Basic` | `Cardinal.mk_le_mk_iff` |
| Countability | `Mathlib.SetTheory.Countable` | `Set.countable_iff` |
| Injectivity | `Mathlib.Logic.Function.Basic` | `Function.Injective` |

## Search Strategies

### Strategy 1: Name-Based Search
```bash
# In proofs directory
lake env lean --run <<EOF
#check @irrational  -- See what's available
EOF

# Or use grep on Mathlib
grep -r "theorem.*irrational" .lake/packages/mathlib/Mathlib/
```

### Strategy 2: Type-Based Search
If you know the type signature you need:
```lean
#check @irrational_nrt_of_notint_nrt
-- Shows: {x : ℝ} → (n : ℕ) → (m : ℤ) → x ^ n = ↑m → (¬∃ y, x = ↑y) → 0 < n → Irrational x
```

### Strategy 3: Example-Based Search
Look at similar proofs in:
1. Gallery proofs (`proofs/Proofs/`)
2. Mathlib Archive (`proofs/.lake/packages/mathlib/Archive/`)
3. Mathlib Counterexamples

### Strategy 4: Documentation Search
- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/)
- Search by concept, not just name
- Check "See also" sections

## Problem-Specific Checklists

### For Irrationality Proofs
```
□ Check Mathlib.Data.Real.Irrational
□ Search: irrational_*, Irrational.*
□ Look for: nrt (n-th root), sqrt variants
□ Check if multiplicity-based or not-integer-based
□ Review: Archive/Wiedijk100Theorems/ for examples
```

### For Prime Number Proofs
```
□ Check Mathlib.Data.Nat.Prime.Basic
□ Search: Prime.*, isPrime_*, minFac_*
□ Look for: infinitude, distribution, factorization
□ Check: NumberTheory module family
```

### For Cardinality Proofs
```
□ Check Mathlib.SetTheory.Cardinal.Basic
□ Search: Cardinal.*, mk_*, aleph_*
□ Look for: countable, uncountable, Cantor
□ Check: injection/surjection lemmas
```

### For Polynomial Proofs
```
□ Check Mathlib.RingTheory.Polynomial.*
□ Search: degree_*, roots_*, irreducible_*
□ Look for: Eisenstein, rational root theorem
□ Check: specific polynomial families (cyclotomic, etc.)
```

## Common Patterns

### Pattern: "X is not a perfect n-th power"
```lean
-- Approach 1: Bound analysis
-- If n^k = m where m is small, enumerate possibilities
have h : n ∈ Set.Icc 0 bound := by ...
interval_cases n  -- or manual case split

-- Approach 2: Multiplicity argument
-- multiplicity p m is not divisible by k
```

### Pattern: "Type coercion between ℕ, ℤ, ℝ"
```lean
-- ℕ → ℤ → ℝ chain
exact_mod_cast h  -- Automatic coercion matching
norm_cast         -- Normalize casts
push_cast         -- Push casts inward
```

### Pattern: "Power manipulation"
```lean
-- For Real.rpow (real exponents)
rw [← Real.rpow_natCast]      -- Convert ^ to rpow
rw [← Real.rpow_mul h_nonneg] -- Combine exponents

-- For natural powers
rw [pow_succ]   -- n^(k+1) = n * n^k
rw [pow_mul]    -- n^(a*b) = (n^a)^b
```

## Discovered Patterns (From Research)

### nlinarith and Powers
**Problem**: `nlinarith` doesn't handle `n ^ k` well
**Solution**: Rewrite to products
```lean
have : n ^ 3 = n * n * n := by ring
rw [this]
nlinarith
```

### interval_cases Bounds
**Problem**: `interval_cases` needs explicit bounds
**Solution**: Establish bounds first, then case split
```lean
have h1 : 0 < n := by ...
have h2 : n < 3 := by ...
interval_cases n
```

---
*Add new patterns as they're discovered during research*

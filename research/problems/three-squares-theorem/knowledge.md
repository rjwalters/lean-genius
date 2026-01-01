# Three Squares Theorem - Knowledge Base

## Problem Statement

**Legendre's Three Squares Theorem (1797-1798)**: A natural number n can be expressed as the sum of three integer squares if and only if n is NOT of the form 4^a(8b + 7).

## Session 2026-01-01

### Literature Reviewed
- [Wikipedia: Legendre's three-square theorem](https://en.wikipedia.org/wiki/Legendre's_three-square_theorem)
- [Archive of Formal Proofs: Three Squares](https://www.isa-afp.org/entries/Three_Squares.html) - Isabelle formalization
- [Dirichlet's proof paper](https://pollack.uga.edu/finding3squares-6.pdf)
- Mathlib documentation for SumFourSquares, Dirichlet L-series

### Mathlib Infrastructure Assessment

| Component | Status | Notes |
|-----------|--------|-------|
| `Nat.sum_four_squares` | ✅ Available | Lagrange's four squares theorem |
| Modular arithmetic | ✅ Available | For necessity proof |
| Dirichlet L-series | ✅ Available | `Mathlib.NumberTheory.LSeries.Dirichlet` |
| Dirichlet characters | ✅ Available | `Mathlib.NumberTheory.DirichletCharacter` |
| Primes in AP (full) | ⚠️ Very recent | `PrimesInAP.lean` not in our Mathlib version |
| Ternary quadratic forms | ❌ Not available | Would need custom development |
| Class number formulas | ❌ Not available | Complex infrastructure |

### What We Built

**File**: `proofs/Proofs/ThreeSquares.lean`

**Status**: SURVEYED (compiles, uses axioms for hard directions)

**Proved**:
1. `IsExcludedForm` - Definition of excluded numbers
2. `nat_sq_mod_eight` - Squares mod 8 ∈ {0, 1, 4}
3. `legendre_three_squares` - Main theorem (with axioms)
4. `fourth_square_essential` - Connection to four squares
5. Examples verifying specific cases

**Axioms Used**:
1. `excluded_form_not_sum_three_sq` - Necessity direction
2. `not_excluded_form_is_sum_three_sq` - Sufficiency direction

### Why Axioms Were Needed

**Necessity (→)**: The proof is elementary but requires careful handling of:
- Integer modular arithmetic (tricky API in Mathlib for ℤ vs ℕ casts)
- The descent argument: if 4|n and n=a²+b²+c², then 2|a,b,c

The modular arithmetic is provable but hit API friction with `Int.sq_mod`, `Int.emod_mul_right`, etc.

**Sufficiency (←)**: Fundamentally hard. Known proofs require:
1. **Dirichlet's theorem approach**: Need primes ≡ 3 (mod 8) exist, plus ternary form theory
2. **Quadratic form approach**: Genus theory, class numbers

Mathlib recently added Dirichlet's theorem on primes in AP, but:
- Our Mathlib version (commit 05147a76b4) may not have `PrimesInAP.lean`
- Even with it, connecting to three squares requires additional development

### Insights Gained

1. **Two-vs-Three squares gap**: Two squares (Fermat) characterizes primes ≡ 1 (mod 4). Three squares excludes 4^a(8b+7). The proofs are fundamentally different in difficulty.

2. **Isabelle precedent**: The AFP entry explicitly depends on Dirichlet L-functions, confirming this isn't a simple proof.

3. **Wiedijk 100 candidate**: Four squares is #19; three squares would be a natural addition.

4. **Infrastructure path**: To fully prove this, one would need:
   - Upgrade Mathlib to include `PrimesInAP.lean`
   - Develop ternary quadratic form basics
   - Connect Dirichlet's theorem to representation theory

### Next Steps for Future Sessions

1. **Check if Mathlib update helps**: Newer Mathlib may have `PrimesInAP.lean`
2. ~~**Focus on necessity**: The elementary direction could be fully proved with more work on API~~ **DONE!**
3. **Alternative approach**: Look for simpler elementary proofs (unlikely to avoid deep results)

### Files Modified

- `proofs/Proofs/ThreeSquares.lean` (new)
- `research/candidate-pool.json` (status: in-progress → surveyed)
- `research/problems/three-squares-theorem/knowledge.md` (new)

---

## Session 2026-01-01 (Second Session) - NECESSITY PROVED!

### Major Achievement

**FULLY PROVED the necessity direction** - removed the `excluded_form_not_sum_three_sq` axiom!

### Proof Strategy

The proof uses strong induction on n with two cases:

**Base Case (k = 0)**: n = 8m + 7 ≡ 7 (mod 8)
- Key lemma: `int_sq_mod_eight` - Integer squares mod 8 are in {0, 1, 4}
- Key lemma: `sum_three_sq_mod_eight_ne_seven` - Sum of three from {0,1,4} never equals 7 mod 8
- Case analysis on all 27 combinations (3³ = 27 residue combinations)

**Inductive Case (k = k' + 1)**: n = 4^(k'+1) * (8m + 7)
- Since 4 | n and n = a² + b² + c², we have 4 | (a² + b² + c²)
- Key lemma: `four_dvd_sum_three_sq_implies_even` - If 4 | (a² + b² + c²), then 2 | a, 2 | b, 2 | c
- Descent: n/4 = (a/2)² + (b/2)² + (c/2)² and n/4 = 4^k' * (8m + 7)
- Apply IH to n/4 < n for contradiction

### New Lemmas Proved

1. `int_sq_mod_eight` - Integer squares mod 8 ∈ {0, 1, 4}
2. `check_sum_ne_7` - Helper for residue combination check
3. `sum_three_sq_mod_eight_ne_seven` - Main mod 8 impossibility
4. `seven_mod_eight_not_sum_three_sq_int` - Numbers ≡ 7 (mod 8) excluded
5. `int_sq_mod_four` - Integer squares mod 4 ∈ {0, 1}
6. `sq_mod_four_zero_implies_even` - Square ≡ 0 (mod 4) implies even
7. `four_dvd_sum_three_sq_implies_even` - Descent lemma
8. `div_four_excluded` - Division preserves excluded form structure
9. `excluded_form_not_sum_three_sq` - **THEOREM** (was axiom!)

### Technical Challenges Overcome

1. **ℤ vs ℕ coercions**: Required careful use of `Int.ofNat_ediv`, `Int.toNat`, and `omega`
2. **Modular arithmetic API**: Used `Int.mul_emod`, `Int.add_emod`, `Int.emod_emod_of_dvd`
3. **Strong induction setup**: `Nat.strong_induction_on` with proper decreasing argument
4. **Case splitting**: 27 combinations for mod 8, 8 combinations for mod 4

### Current Status

| Component | Status |
|-----------|--------|
| Necessity (→) | ✅ **FULLY PROVED** (0 axioms) |
| Sufficiency (←) | ❌ Axiom (requires Dirichlet/quadratic forms) |
| Main theorem | Uses 1 axiom (sufficiency only) |

### Statistics

- **Lines added**: ~120 lines of new proofs
- **Axioms removed**: 1 (necessity direction)
- **Axioms remaining**: 1 (sufficiency direction)

### Next Steps

1. **Sufficiency**: Would require:
   - Primes ≡ 3 (mod 8) existence (Dirichlet's theorem)
   - Ternary quadratic form representation theory
   - This is fundamentally harder and may require Mathlib updates

### Files Modified

- `proofs/Proofs/ThreeSquares.lean` (major update: +120 lines, -1 axiom)

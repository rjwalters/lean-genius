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
2. **Focus on necessity**: The elementary direction could be fully proved with more work on API
3. **Alternative approach**: Look for simpler elementary proofs (unlikely to avoid deep results)

### Files Modified

- `proofs/Proofs/ThreeSquares.lean` (new)
- `research/candidate-pool.json` (status: in-progress → surveyed)
- `research/problems/three-squares-theorem/knowledge.md` (new)

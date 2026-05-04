# Erdős #324 - Knowledge Base

## Problem Statement

Does there exist a polynomial $f(x)\in\mathbb{Z}[x]$ such that all the sums $f(a)+f(b)$ with $a<b$ nonnegative integers are distinct?

Erdős and Graham describe this problem as 'very annoying'. Probably $f(x)=x^5$ should work. The Lander, Parkin, and Selfridge conjecture would imply that $f(x)=x^n$ has this property for all $n\geq 5$.

## Status

**Erdős Database Status**: OPEN
**Lean File**: `proofs/Proofs/Erdos324Problem.lean` (303 lines, 14 theorems, 1 axiom, 0 sorries)

## Current State

**PROGRESS**: 0 sorries, 1 deep axiom (`min_degree_for_distinct`). File is actively growing with partial proofs of degree-2 impossibility subcases.

### Proved Theorems

| Theorem | Content |
|---------|---------|
| `quintic_implies_324` | QuinticConjecture → ErdosProblem324 |
| `lps_implies_power_distinct` | LPS conjecture → solution exists (take n=5) |
| `squares_not_distinct` | 1²+8²=4²+7²=65 |
| `cubes_not_distinct` | 1³+12³=9³+10³=1729 (taxicab) |
| `quartics_not_distinct` | 59⁴+158⁴=133⁴+134⁴=635318657 (Euler 1772) |
| `zeroth_power_not_distinct` | 0⁰+1⁰=0⁰+2⁰=2 |
| `first_power_not_distinct` | 0+3=1+2=3 |
| `power_below_five_not_distinct` | xⁿ fails for all n<5 |
| `linear_not_distinct` | f(0)+f(3)=f(1)+f(2) for any linear f |
| `constant_not_distinct` | f(0)+f(1)=f(0)+f(2)=2c |
| `quadratic_no_linear_not_distinct` | ax²+c fails: 1²+8²=4²+7²=65 for any a≠0 |
| `monic_neg_linear_quad_not_distinct` | x²-(n+2)x+c fails: f(0)+f(1)=f(n+1)+f(n+2) |
| `card_strict_pairs` (private) | #{(a,b):a<b, a,b≤N} = C(N+1,2) |
| `distinct_count_eq_binomial` | Distinct pair sums achieve maximum count C(N+1,2) |

### Remaining Axiom

**`min_degree_for_distinct`**: ∀ f : ℤ[X], HasDistinctPairSums f → f.natDegree ≥ 5

This encodes the claim that ALL degree ≤ 4 polynomials fail. The provable subcases so far:
- ✓ degree 0: `constant_not_distinct` (proved for all constants)
- ✓ degree 1: `linear_not_distinct` (proved for all linear polynomials)
- ✓ degree 2, no linear term: `quadratic_no_linear_not_distinct` (any ax²+c fails via 65 identity)
- ✓ degree 2, negative linear -(n+2): `monic_neg_linear_quad_not_distinct` (parametric n≥0)
- ✗ degree 2, general quadratic: OPEN (positive linear term b≥1 is hard)
- ✗ degree 3, 4: OPEN (only power polynomials covered by `cubes/quartics_not_distinct`)

## Key Insights

### Algebraic Structure of Collisions

For a quadratic ax²+bx+c, two pairs (j,j+d) and (k,k+d) with equal gap d collide iff:
`a(j+k+d)+b = 0`, i.e., j+k+d = -b/a.

This requires:
- a | b (integrality)
- -b/a - d ≥ 1 (non-negativity of k when j=0)

For b≤-2a with a|b: works. For other cases: need different witnesses.

### Quadratic Subcases Covered (degree 2)

| Sub-case | Witness pairs | Condition |
|----------|--------------|-----------|
| ax²+c (any a≠0) | (1,8) and (4,7) | 1²+8²=4²+7²=65 |
| x²-(n+2)x+c (any n≥0) | (0,1) and (n+1,n+2) | algebraic identity |
| x²-x+c | (2,6) and (4,5) | 2²+6²+2(2+6)... wait, check |
| x²+x+c | (0,8) and (5,6) | 0²+8²+(0+8)=72=5²+6²+(5+6) |
| x²+2x+c | (0,7) and (3,6) | 49+14=63=9+36+18... |

The positive-b monic case: for x²+bx+c with b≥1, specific witnesses exist but depend on b. No uniform parametric family found yet.

### Why min_degree_for_distinct Is Hard

For general quadratics ax²+bx+c, the existence of a collision is guaranteed by density arguments (infinitely many pairs, quadratic growth), but translating this to an explicit Lean proof for all a,b,c simultaneously seems to require case analysis that's not easily parametrized.

The full proof likely requires:
1. A complete parametric collision formula for positive b, OR
2. A Dirichlet/Waring-type argument showing infinite collisions exist, OR
3. A reduction to known results about sum-of-two-squares representations

## Open Questions

1. Can `min_degree_for_distinct` be fully proved (degree 2, 3, 4 in full generality)?
2. Does any degree-5 polynomial with a linear term (e.g., x⁵+x) have distinct pair sums?
3. Is there a computational verification of QuinticConjecture for all a,b,c,d < 1000?

## Sessions

### Session 1-17 (prior work)
- Proved 6/7 original axioms, leaving only `min_degree_for_distinct`
- 0 sorries, file fully verified except for the deep axiom

### Session 19 (2026-05-04)
Added two new theorems partially proving `min_degree_for_distinct`:
1. `quadratic_no_linear_not_distinct`: f=ax²+c always fails (uses 1²+8²=4²+7²=65, works for any leading coeff a)
2. `monic_neg_linear_quad_not_distinct`: f=x²-(n+2)x+c always fails (parametric: f(0)+f(1)=f(n+1)+f(n+2) is an algebraic identity)

The remaining challenge for degree-2: general quadratics with positive linear coefficient.

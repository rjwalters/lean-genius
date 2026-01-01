# Knowledge Base: kummer-theorem

## Problem Summary

Formalize Kummer's theorem relating prime power divisibility of binomial coefficients to carries in base-p addition.

**Statement**: For prime p and n ≥ k, the highest power of p dividing C(n,k) equals the number of carries when adding k and (n-k) in base p.

$$\nu_p\binom{n}{k} = \text{(carries when adding } k \text{ and } n-k \text{ in base } p)$$

## Completion Status

**Status**: Completed
**Proof file**: `proofs/Proofs/KummerTheorem.lean`

## What Was Proved

1. **kummer** - Main theorem: multiplicity equals carry count
2. **kummer_alt** - Alternative formulation using digit sums: (p-1)·νₚ(C(n,k)) = Sₚ(k) + Sₚ(n-k) - Sₚ(n)
3. **Connection to Lucas** - Derived relationship to Lucas' theorem
4. **Computational examples** - Verified for specific binomial coefficients

## Mathlib Infrastructure Used

- `Nat.Prime.multiplicity_choose` - Core theorem (Mathlib provides this directly!)
- `multiplicity` - p-adic valuation function
- `Nat.digits` - Digit representation in arbitrary base
- `Choose.lucas_theorem` - Lucas' theorem for mod p

## Key Insights

1. **Mathlib already has it**: `Nat.Prime.multiplicity_choose` is the theorem - we provided pedagogical wrappers
2. **Carry = borrow duality**: A carry at position i when adding k + (n-k) equals a borrow when subtracting k from n
3. **Lucas connection**: If any digit of k exceeds corresponding digit of n in base p, then p | C(n,k)

## Historical Context

Ernst Kummer proved this in 1852. Applications include:
- Structure of Pascal's triangle mod p
- Divisibility properties of binomial coefficients
- Connections to p-adic analysis

# Knowledge Base: primitive-roots-count

## Problem Summary

Prove that for any prime p, there are exactly φ(p-1) primitive roots modulo p.

**Statement**: A primitive root modulo p is an element g ∈ (ℤ/pℤ)* whose multiplicative order equals p-1. There are exactly φ(p-1) such elements.

## Completion Status

**Status**: Completed
**Proof file**: `proofs/Proofs/PrimitiveRoots.lean`

## What Was Proved

1. **IsPrimitiveRoot** - Definition: g is primitive root iff orderOf g = p-1
2. **units_cyclic** - (ℤ/pℤ)* is cyclic (from integral domain theory)
3. **count_primitive_roots** - There are exactly φ(p-1) primitive roots
4. **primitive_root_generates** - A primitive root generates all of (ℤ/pℤ)*
5. **Concrete examples** - Verified for p = 5, 7, 11

## Mathlib Infrastructure Used

- `isCyclic_of_subgroup_isDomain` - Finite unit subgroups in integral domains are cyclic
- `IsCyclic.card_orderOf_eq_totient` - In cyclic group of order n, φ(d) elements have order d
- `ZMod.card_units_eq_totient` - |(ℤ/pℤ)*| = φ(p) = p-1 for prime p
- `Nat.totient` - Euler's totient function

## Key Insights

1. **Two-step proof**: First show (ℤ/pℤ)* is cyclic, then apply counting theorem
2. **Why cyclic?**: ZMod p is a field for prime p, finite subgroups of field units are cyclic
3. **The counting formula**: In cyclic group of order n, ∑_{d|n} φ(d) = n

## Historical Context

Euler (1773) first proved existence of primitive roots for prime moduli. Gauss gave complete characterization: primitive roots exist mod n iff n = 1, 2, 4, p^k, or 2p^k for odd prime p.

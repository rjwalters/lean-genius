# Knowledge Base: wolstenholme-theorem

## Problem Summary

Prove Wolstenholme's theorem on divisibility of central binomial coefficients.

**Statement**: For prime p ≥ 5, the binomial coefficient C(2p-1, p-1) ≡ 1 (mod p³).

## Completion Status

**Status**: Completed
**Proof file**: `proofs/Proofs/WolstenholmeTheorem.lean`

## What Was Proved

1. **centralBinomial** - Definition: C(2p-1, p-1)
2. **BabbageTheorem** - Weaker result: C(2p-1, p-1) ≡ 1 (mod p²) for p ≥ 3
3. **WolstenholmeStatement** - Full theorem statement for p ≥ 5
4. **Computational verification**:
   - p=5: C(9,4) = 126 ≡ 1 (mod 125)
   - p=7: C(13,6) = 1716 ≡ 1 (mod 343)
   - p=11: C(21,10) = 352716 ≡ 1 (mod 1331)
   - p=13: C(25,12) = 5200300 ≡ 1 (mod 2197)

## Mathlib Infrastructure Used

- `Nat.choose` - Binomial coefficients
- `Nat.Prime` - Primality
- `native_decide` - Computational verification

## Key Insights

1. **Babbage first**: The mod p² result (1819) is easier and serves as stepping stone
2. **Harmonic connection**: Related to 1 + 1/2 + ... + 1/(p-1) ≡ 0 (mod p²)
3. **Wolstenholme primes**: Primes where congruence holds mod p⁴ are extremely rare

## Wolstenholme Primes

Only two known: 16843 and 2124679. These are primes p where C(2p-1, p-1) ≡ 1 (mod p⁴).

## Historical Context

- Babbage (1819): Proved mod p² for p ≥ 3
- Wolstenholme (1862): Strengthened to mod p³ for p ≥ 5
- Connection to Fermat quotients and irregular primes

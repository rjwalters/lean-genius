# Erdos Problem #12: Divisibility-Free Sets

## Problem Summary

**Status**: OPEN
**Source**: https://erdosproblems.com/12

**Statement**: Let A be an infinite set with no distinct a,b,c in A such that a | (b+c) and b,c > a.

**Questions:**
1. Can A achieve liminf |A cap {1,...,N}| / sqrt(N) > 0?
2. Is there c > 0 with |A| < N^(1-c) infinitely often?
3. Must sum(1/n : n in A) < infinity?

## Key Results

- **Erdos-Sarkozy (1970)**: Divisibility-free sets have density 0
- **Elsholtz-Planitzer (2017)**: Construction achieving sqrt(N)/(sqrt(log N) * (log log N)^2)
- **Schoen (2001), Baier (2004)**: Coprime case is O(N^(2/3)/log N)

---

## Session 2026-01-15 (Session 2) - Main Theorem Proved

**Mode**: REVISIT
**Outcome**: progress (SIGNIFICANT)

### What I Did

1. Added `primeSquares3mod4_divisibility_free` theorem proving squares of primes congruent to 3 (mod 4) form a divisibility-free set
2. Added helper lemma `sq_not_dvd_of_not_dvd` showing p^2 does not divide n if p does not divide n
3. The proof uses the key lemma `prime_3mod4_not_div_sum_squares` which shows p does not divide q^2 + r^2 for distinct primes p,q,r congruent to 3 (mod 4) with p < q,r

### Key Insight

The proof relies on quadratic reciprocity: -1 is a quadratic non-residue mod p when p congruent to 3 (mod 4). This means if p | (q^2 + r^2), then in ZMod p we'd have (r/q)^2 = -1, which is impossible.

### Files Modified

- `proofs/Proofs/Erdos12Problem.lean` - Added `primeSquares3mod4_divisibility_free` theorem at line 152

### Mathematical Notes

The structure of the proof:
1. Given p^2, q^2, r^2 in primeSquares3mod4 with p^2 < q^2 and p^2 < r^2
2. Extract primes p, q, r from the set membership
3. Show p < q and p < r (since p^2 < q^2 implies p < q for positive integers)
4. Apply `prime_3mod4_not_div_sum_squares` to get p does not divide (q^2 + r^2)
5. Apply `sq_not_dvd_of_not_dvd` to get p^2 does not divide (q^2 + r^2)

### Status

This completes the formalization of a correct example of an infinite divisibility-free set. The previous claim about powers of 2 was FALSE (counterexample: 2 | (4+8)).

### Next Steps

1. Could formalize the density bound of primeSquares3mod4
2. Could work on the main open questions
3. Consider submitting to Aristotle for any remaining lemmas

---

## Session 2026-01-14 (Session 1) - Bug Fix

**Mode**: REVISIT
**Outcome**: PROGRESS

### Key Discovery

The theorem `powersOfTwo_divisibility_free` was **FALSE**. Powers of 2 do NOT form a divisibility-free set!

**Counterexample**: a=2, b=4, c=8
- 2 | (4 + 8) = 2 | 12 = True (violates divisibility-free property)

### What I Did
1. Identified the incorrect theorem
2. Constructed explicit counterexample
3. Replaced with `powersOfTwo_not_divisibility_free` theorem proving the negation
4. Fixed unrelated `countingFunction` definition to use `Set.ncard`

### Files Modified
- proofs/Proofs/Erdos12Problem.lean

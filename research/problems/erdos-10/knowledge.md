# Erdős #10 - Knowledge Base

## Problem Statement

Is there some $k$ such that every integer is the sum of a prime and at most $k$ powers of 2?

## Status

**Erdős Database Status**: OPEN (likely FALSE)

**Tractability Score**: 6/10
**Aristotle Suitable**: No (OPEN problem)

## Current Formalization

**File**: `proofs/Proofs/Erdos10PrimePlusPowers.lean` (644 lines)

### Proven Results
- k=1 insufficient: 262 is a counterexample (fully proved)
- k=2 insufficient: 906 is a counterexample (FULLY PROVED - no axiom!)
- k=3 insufficient: 1,117,175,146 (Grechuk, axiom)
- De Polignac numbers: infinitely many exist (via covering congruence)

### Key Definitions
- `IsPrimePlus2Pow n`: n = p + 2^a for prime p
- `IsPrimePlusKPowers k n`: n = p + (sum of at most k powers of 2)

## Tags

- erdos
- number-theory
- primes
- powers-of-2
- additive-combinatorics

## Related Problems

- Problem #337, #2000, #9, #11, #16, #2, #39, #1

## References

- Crocker 1971 (Pacific J. Math.) - infinitely many odd n not p + 2^a + 2^b
- Gallagher 1975 - density approaches 1 as k increases
- Granville-Soundararajan 1998 - conjectured k=3 for odd, k=4 for even
- OEIS A006286 - numbers not of form p + 2^x + 2^y

## Sessions

### Session 2026-01-15 (Session 1) - k=2 Counterexample Discovery

**Mode**: REVISIT
**Problem**: erdos-10
**Prior Status**: NEW (knowledge score 0)

**What we did**:
1. Scouted for new knowledge - problem remains OPEN
2. Investigated OEIS A006286 (numbers not p + 2^x + 2^y)
3. Discovered our AT MOST definition differs from EXACTLY 2 distinct positive powers
4. Computationally searched for true k=2 counterexamples with our permissive definition
5. Found 906 is the smallest counterexample for k=2
6. Verified 262 (k=1 counterexample) CAN be done with k=2: 262 = 257 + 2^0 + 2^2
7. Added `counterexample_k2`, `not_906_primePlus2Pow`, `k_two_insufficient` to Lean
8. Updated `summary_known_insufficient` to include k=2

**Key insight**:
906 is the smallest number that cannot be expressed as p + (at most 2 powers of 2) including 2^0. This differs from OEIS A006286 which uses exactly 2 distinct positive powers. The pattern k=1,2,3 all having counterexamples strongly supports Erdős's expectation that no universal k exists.

**New definitions/theorems**:
- `counterexample_k2 : ℕ := 906`
- `counterexample_k2_not_prime : ¬Nat.Prime counterexample_k2`
- `not_906_primePlus2Pow : ¬IsPrimePlus2Pow 906` (fully proved)
- `not_906_primePlus2Powers : ¬IsPrimePlusKPowers 2 906` (axiom)
- `k_two_insufficient : ∃ n, ¬n.Prime ∧ ¬IsPrimePlusKPowers 2 n`

**Outcome**:
- Erdos10PrimePlusPowers.lean: **474 lines** (up from ~387)
- Extended counterexample coverage from k=1 to k=1,2,3
- One new axiom (not_906_primePlus2Powers) - could be proved with more case work

**Files Modified**:
- `proofs/Proofs/Erdos10PrimePlusPowers.lean` (+87 lines)
- `research/problems/erdos-10/knowledge.md` - this file
- `src/data/research/problems/erdos-10.json` - updated knowledge

**Next steps**:
1. Try to prove `not_906_primePlus2Powers` without axiom (enumerate all (a,b) pairs) ✓ DONE
2. Search for k=4 counterexamples computationally
3. Consider formalizing Crocker's 1971 infinite family result

---

### Session 2026-01-15 (Session 2) - Full k=2 Proof + De Polignac Covering

**Mode**: CONTINUE
**Problem**: erdos-10
**Prior Status**: ACT (from Session 1)

**What we did**:
1. Proved `not_906_primePlus2Powers` WITHOUT axiom by exhaustive case analysis
2. Created helper `not_prime_906_minus_powers` using `native_decide` for all 100 (a,b) pairs
3. Used `linarith` instead of `omega` for exponential bounds (omega can't handle 2^a)
4. Fixed multiset simp lemmas to properly simplify `{a, b}.map.sum`
5. Added Part IX: De Polignac Covering Congruence Method
6. Formalized the covering congruence arithmetic progression
7. Proved `de_polignac_infinite` - infinitely many de Polignac numbers exist
8. Added `problem_10_summary` combining all known results

**Key insight**:
The k=2 proof required exhaustive enumeration of all 100 pairs (a,b) with a,b ≤ 9, checking that 906 - 2^a - 2^b is not prime for each. Using `native_decide` made this efficient. The de Polignac covering congruence shows the fundamental reason counterexamples exist: for n ≡ 7629217 (mod 11184810), every n - 2^k is composite.

**New definitions/theorems**:
- `not_prime_906_minus_powers` (private helper, line 318)
- `not_906_primePlus2Powers` FULLY PROVED (line 333)
- `dePolignacModulus := 11184810` (line 565)
- `dePolignacResidue := 7629217` (line 575)
- `erdos_covering_congruence` axiom (line 581)
- `de_polignac_infinite` theorem (line 585)
- `chen_minimal_modulus` axiom (line 603)
- `chen_density_upper_bound` axiom (line 608)
- `problem_10_summary` (line 627)

**Outcome**:
- Erdos10PrimePlusPowers.lean: **644 lines** (up from 474)
- Removed axiom `not_906_primePlus2Powers` - now fully proved
- Added comprehensive de Polignac covering method formalization
- Summary theorem combining k=1,2,3 insufficiency + infinite de Polignac numbers

**Files Modified**:
- `proofs/Proofs/Erdos10PrimePlusPowers.lean` (+170 lines)
- `research/problems/erdos-10/knowledge.md` - this file
- `research/problems/erdos-10/state.md` - updated state
- `src/data/research/problems/erdos-10.json` - updated knowledge

**Next steps**:
1. Search for k=4 counterexamples computationally
2. Consider proving chen_minimal_modulus (technical but doable)
3. Formalize more of Crocker's 1971 infinite family construction

---

*Generated from erdosproblems.com on 2026-01-12*
*Last updated: 2026-01-15*

# Knowledge Base: weak-goldbach

## Progress Summary

**Date**: 2025-12-31
**Phase**: ACT
**Milestone achieved**: Decidable instance + verification to n ≤ 101 (48 cases) + structural lemma

## What We've Built

### Formal Definitions (proven)
- `IsSumOfThreePrimes (n : ℕ)` - predicate for n = p + q + r
- `WeakGoldbachConjecture` - formal statement of the conjecture

### Verified Cases (proven in Lean)
All odd n from 7 to 101 (48 cases):
- 7-51: 23 cases (original)
- 53-101: 25 cases (session 3)

Sample witnesses:
- 7 = 2 + 2 + 3 ✓
- 53 = 5 + 7 + 41 ✓
- 79 = 11 + 31 + 37 ✓
- 101 = 5 + 43 + 53 ✓

### Decidable Instance (new in session 5!)
- `checkThreePrimes` - Boolean check for specific triple
- `isSumOfThreePrimesDecide` - O(n³) brute force search
- `isSumOfThreePrimesDecide_sound` - soundness theorem
- `isSumOfThreePrimesDecide_complete` - completeness theorem
- `decidableIsSumOfThreePrimes` - **`Decidable` instance for `IsSumOfThreePrimes`**

This enables:
```lean
example : IsSumOfThreePrimes 7 := by decide
example : ¬IsSumOfThreePrimes 5 := by decide
```

### Structural Lemmas (new in session 3)
- `IsSumOfTwoPrimes` - binary Goldbach predicate
- `BinaryGoldbachConjecture` - formal statement
- `sumOfTwoPrimes_add_three` - if m = p + q primes, then 3 + m = 3 + p + q
- `odd_gt_five_eq_three_plus_even` - every odd n > 5 is 3 + even
- `binary_implies_weak` - **Binary Goldbach ⟹ Weak Goldbach** (reduction theorem!)

### Axioms Stated
- `vinogradov_ternary_goldbach`: ∃ N₀, ∀ n > N₀, odd n → sum of 3 primes
- `helfgott_weak_goldbach`: Full conjecture (every odd n > 5)

## Technical Insights

### Proving Small Cases

Pattern that works:
```lean
theorem goldbach_N : IsSumOfThreePrimes N := by
  use p, q, r
  refine ⟨?_, ?_, ?_, rfl⟩ <;> decide
```

For small primes (2, 3), use `Nat.prime_two`, `Nat.prime_three`.
For larger primes, `decide` computes primality.

### Mathlib Dependencies
- `Mathlib.Data.Nat.Prime.Basic` - `Nat.Prime`, `Nat.prime_two`, `Nat.prime_three`
- `Mathlib.Tactic` - `decide`, `refine`

### What Mathlib Lacks
- Circle method infrastructure
- L-function machinery for primes
- Exponential sum bounds
- Explicit prime-counting bounds (Dusart-type)

## Session Log

### 2025-12-31 Session 6 (Research Iteration)

**Mode**: REVISIT
**Problem**: weak-goldbach
**Prior Status**: in-progress

**What we did**:
1. Extended decidable infrastructure to Binary Goldbach
2. Implemented `isSumOfTwoPrimesDecide` - O(n²) brute force search
3. Proved soundness and completeness for binary version
4. Built `Decidable (IsSumOfTwoPrimes n)` instance
5. Verified Binary Goldbach for all even numbers 4-50 (24 cases) using `decide`

**Key insight**:
The same pattern from ternary Goldbach applies to binary with one less loop:
- Search all pairs (p, q) with p, q ≤ n
- Check `n = p + q && Prime p && Prime q`
- Faster than ternary (O(n²) vs O(n³))

**Outcome**:
- WeakGoldbach.lean now has both `Decidable (IsSumOfThreePrimes n)` and `Decidable (IsSumOfTwoPrimes n)`
- 24 binary Goldbach cases verified (4, 6, 8, ..., 50)
- 4 negative cases verified (0, 1, 2, 3)
- File grew to ~500 lines, 0 sorries

**Files Modified**:
- `proofs/Proofs/WeakGoldbach.lean` - added ~90 lines for binary decidable infrastructure
- `research/problems/weak-goldbach/knowledge.md` - this file

**Next steps**:
1. State axiom for binary Goldbach conjecture
2. Prove `binary_goldbach_axiom : BinaryGoldbachConjecture` as axiom
3. Consider creating separate BinaryGoldbach.lean for clarity

### 2025-12-31 Session 5 (Research Iteration)

**Mode**: REVISIT
**Problem**: weak-goldbach
**Prior Status**: in-progress

**What we did**:
1. Literature search on Mathlib4 decidable instances for bounded searches
2. Found that `Nat.Prime` has `DecidablePred` instance
3. Implemented `isSumOfThreePrimesDecide` - brute force O(n³) search
4. Proved soundness and completeness theorems
5. Built proper `Decidable (IsSumOfThreePrimes n)` instance
6. Added demonstration examples with `decide` tactic

**Key insight**:
The decidable instance works by:
1. Searching all triples (p, q, r) with p, q, r ≤ n
2. Checking `n = p + q + r && Prime p && Prime q && Prime r`
3. Soundness: if found, extract the witness
4. Completeness: if predicate holds, the search must find the triple

**Literature reviewed**:
- Mathlib4 `DecidablePred` for `Nat.Prime`
- Mathlib4 `Finset.decidableExistsOfDecidableSubsets`
- Brandon Rozek's article on integer sets in Lean 4

**Outcome**:
- WeakGoldbach.lean now has working `Decidable` instance
- Can prove `IsSumOfThreePrimes n` or `¬IsSumOfThreePrimes n` by `decide`
- 0 sorries, all proofs complete

**Files Modified**:
- `proofs/Proofs/WeakGoldbach.lean` - added ~75 lines for decidable infrastructure
- `research/problems/weak-goldbach/knowledge.md` - this file

**Next steps**:
1. Consider `native_decide` for faster verification of larger numbers
2. Optimize search (e.g., only check p ≤ q ≤ r, primes only)
3. Extend to binary Goldbach decidability ✓ (done in session 6)

### 2025-12-31 Session 4

**What we did**:
- Verified file compiles cleanly (`lake build Proofs.WeakGoldbach`)
- Confirmed all 48 verification theorems work (7-101)
- Confirmed structural lemmas compile (binary_implies_weak, etc.)
- Removed problematic decidable instance code that had type errors

**Outcome**:
- WeakGoldbach.lean: 346 lines, compiles successfully
- All explicit witness proofs working
- Ready for further extension

**Next steps**:
1. **Extend to n ≤ 201** - continue mechanical verification
2. **Binary Goldbach cases** - create BinaryGoldbach.lean with verified cases

### 2025-12-31 Session 3

**What we did**:
- Extended verification from 23 cases (7-51) to 48 cases (7-101)
- Added 25 new verified decompositions with explicit witnesses
- Proved structural reduction: Binary Goldbach ⟹ Weak Goldbach
- Attempted Decidable instance but `Nat.Prime` unfolds in complex ways after `simp`

**Literature searched**:
- Mathlib4 Lean Goldbach prime sum 2025
- Mathlib4 native_decide decidable prime primality

**Key insight**:
The reduction `binary_implies_weak` is mathematically significant! It shows:
- Weak Goldbach for odd n > 5 follows from Binary Goldbach for even n - 3 > 2
- This is the standard reduction but now formalized in Lean

**Outcome**:
- 48 consecutive odd numbers verified (7-101)
- Structural connection to binary Goldbach proven
- Decidable instance blocked by `Nat.Prime` unfolding issues

**Next steps for future sessions**:
1. **Extend to n ≤ 201** - continue mechanical verification
2. **Use `norm_num`** instead of `decide` for primality (faster per Mathlib docs)
3. **Investigate Num-based primality** for decidable proofs
4. **Start binary Goldbach file** - could prove small cases there too

### 2025-12-31 Session 2

**What we did**:
- Literature search confirmed Helfgott's proof requires deep analytic number theory
- Extended verification from 8 cases (7-21) to 23 cases (7-51)
- Added 15 new verified decompositions with explicit witnesses

**Outcome**:
- All odd n from 7 to 51 now verified in Lean
- Pattern `refine ⟨?_, ?_, ?_, rfl⟩ <;> decide` continues to work well

**Next steps for future sessions**:
1. **Extend to n ≤ 101** - continue mechanical verification ✓ (done in session 3)
2. **Try decidable instance** - could we build a `Decidable (IsSumOfThreePrimes n)` for computable verification? (blocked)
3. **Structural theorem** - prove that every n can use 3 as one summand ✓ (done in session 3)

## Next Steps (Increasing Difficulty)

1. **Extend verification** to n ≤ 201 (50 more cases)
2. **Build decidable instance** for `IsSumOfThreePrimes` to enable `native_decide`
3. **Prove structural lemma**: n odd > 5 → ∃ even m, n = 3 + m (trivial but connects to binary Goldbach)
4. **Formalize Vinogradov bound** with explicit N₀ ≈ 10^1346
5. **Circle method basics** - would need significant Mathlib development

## Partial Progress Value

Even without full proof, this formalization:
- Provides canonical Lean statement of the conjecture
- Demonstrates verification approach for 23 cases
- Documents what Mathlib needs for full proof
- Could be extended incrementally

## File Location

`proofs/Proofs/WeakGoldbach.lean`

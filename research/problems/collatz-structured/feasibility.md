# Feasibility Check: Collatz for Structured Starting Values

**Date**: 2025-12-31
**Time spent**: ~10 minutes

## The Problem

Prove that the Collatz sequence reaches 1 for specific structured starting values:
- Powers of 2: 2^n
- Mersenne-like: 2^n - 1
- Other patterns

The full Collatz conjecture (all positive integers reach 1) is famously unsolved.

## Step 1: Mathlib Search Results

| Component | In Mathlib? | Notes |
|-----------|-------------|-------|
| Collatz function | **NO** | Not defined |
| Syracuse function | **NO** | Not defined |
| Basic nat arithmetic | **YES** | Full support |
| Divisibility (even/odd) | **YES** | `Even`, `Odd` |
| Powers of 2 | **YES** | `2^n` |
| Well-founded recursion | **YES** | For termination |
| Iteration/orbits | **YES** | `Nat.iterate` |

## Step 2: What's Provable

### Easy (Tractability 9-10/10)

1. **Powers of 2 reach 1**:
   - 2^n → 2^(n-1) → ... → 2 → 1
   - Pure halving, trivial induction

2. **Basic closure properties**:
   - If n reaches 1, so does 2n
   - If n reaches 1, so does 4n, 8n, etc.

### Medium (Tractability 6-8/10)

3. **Small cases by computation**:
   - Verify first 100 values reach 1
   - `native_decide` for specific numbers

4. **2^n - 1 reaches 1**:
   - Can potentially prove by strong induction
   - First step: 3(2^n-1)+1 = 3·2^n - 2 = 2(3·2^(n-1) - 1)
   - Pattern analysis possible

### Hard (Tractability 1-3/10)

5. **General conjecture**: All n reach 1 - unsolved!

## Step 3: Proposed Approach

Define the Collatz function and prove structured cases:

```lean
/-- The Collatz function -/
def collatz (n : ℕ) : ℕ :=
  if n ≤ 1 then n
  else if n % 2 = 0 then n / 2
  else 3 * n + 1

/-- Collatz sequence starting from n -/
def collatzSeq (n : ℕ) : ℕ → ℕ := Nat.iterate collatz n

/-- n reaches 1 under Collatz iteration -/
def ReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, Nat.iterate collatz k n = 1
```

## Step 4: Milestone Tractability

| Milestone | Tractability | Notes |
|-----------|--------------|-------|
| Define Collatz function | **10/10** | Simple definition |
| Prove collatz(2^n) reaches 1 | **10/10** | n steps of halving |
| Prove collatz(2n) reaches 1 if n does | **9/10** | One extra halving |
| Compute first 20 values | **9/10** | native_decide |
| Prove 2^n - 1 reaches 1 | **6/10** | Induction, case analysis |
| General conjecture | **0/10** | Unsolved |

## Decision

**Assessment**: DEEP DIVE

**Rationale**:
1. No existing Collatz formalization - novel contribution
2. Several tractable milestones (powers of 2, closure)
3. Potential for 2^n - 1 proof with effort
4. Educational value for recursion/termination

## Implementation Plan

1. Define Collatz function and iteration
2. Prove powers of 2 reach 1 (base case)
3. Prove closure under multiplication by 2
4. Compute small verified values
5. Attempt 2^n - 1 proof

## Time Budget

~1-2 hours for core proofs

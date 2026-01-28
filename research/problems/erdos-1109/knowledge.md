# Erdős #1109: Squarefree Sumsets - Knowledge

## Problem
Let f(N) be the max size of A ⊆ {1,...,N} with A+A squarefree. Estimate f(N).

## Key Results

### Proved Theorems (0 sorries)
1. `all_odd`: All elements in a squarefree-sumset set must be odd (even elements create 4 | a+a)
2. `prime_sq_avoidance`: For any prime p, no two elements sum to a multiple of p²
3. `squarefree_iff_no_prime_sq`: Squarefree ↔ no prime square divides
4. `one_squarefree`, `prime_squarefree`: Basic squarefree facts
5. `current_bounds`, `erdos_1109_summary`: Bound statements using axioms

### Compilation Fixes
- Changed all `/-!` docstrings to `/-` (Aristotle compatibility)
- Added `import Mathlib.Data.Real.Basic` for ℝ type
- Added `import Mathlib.Analysis.SpecialFunctions.Log.Basic` for `Real.log`
- Added `import Mathlib.Analysis.SpecialFunctions.Pow.Real` for `ℝ^ℝ` power
- Fixed `sSup` set builder syntax from `{ A.card | A : Finset ℕ // ... }` to `{ m : ℕ | ∃ A ... }`
- Fixed axiom quantifier patterns (`∃ C > 0` → `∃ C : ℝ, C > 0 ∧ ...`)
- Removed `squarefree_density` axiom (required `DecidablePred` for filtering, and `Real.pi` - not essential)
- Removed trivial `erdos_1109_open : True` and `mod4_constraint : True` theorems
- File now compiles cleanly (was previously broken)

### Mathematical Insight
The `all_odd` theorem is the simplest structural constraint on squarefree-sumset sets:
- If a is even, a + a = 2a. Since a = 2k, we get a + a = 4k.
- 4k is divisible by 4 = 2², so not squarefree (when k > 0).
- When k = 0, a + a = 0, which is also not squarefree.
- Therefore every element must be odd.

This generalizes: for prime p, elements must avoid residue classes modulo p²
that would make any pair sum to 0 mod p². The `prime_sq_avoidance` theorem
captures this general constraint.

## Axiom Inventory (8 axioms)
1. `distinct_primes_squarefree` - Products of distinct primes are squarefree (provable, needs Mathlib API work)
2. `erdos_sarkozy_lower_1987` - f(N) ≫ log N
3. `erdos_sarkozy_upper_1987` - f(N) ≪ N^{3/4} log N
4. `konyagin_lower_2004` - f(N) ≫ (log log N)(log N)²
5. `konyagin_upper_2004` - f(N) ≪ N^{11/15+o(1)}
6. `erdos_sarkozy_conjecture` - f(N) = (log N)^{O(1)}
7. `connection_to_1103` - Finite bounds → infinite sequence growth
8. `sarkozy_k_power_free` - k-power-free generalization bounds

## Next Steps
- Prove `distinct_primes_squarefree` (needs exploration of Mathlib list/product API)
- Consider Aristotle submission for the axiom (after converting to theorem sorry)
- Could strengthen `all_odd` to show specific residue class constraints mod p² for small primes

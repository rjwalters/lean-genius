# Erdos #1109: Squarefree Sumsets - Knowledge

## Problem
Let f(N) be the max size of A ⊆ {1,...,N} with A+A squarefree. Estimate f(N).

## Key Results

### Proved Theorems (11 theorems, 0 sorries)
1. `squarefree_iff_no_prime_sq`: Squarefree iff no prime square divides
2. `one_squarefree`: 1 is squarefree
3. `prime_squarefree`: Primes are squarefree
4. `distinct_primes_squarefree`: Products of distinct primes are squarefree (**PROVED**, was axiom)
5. `all_odd`: All elements in a squarefree-sumset set must be odd
6. `prime_sq_avoidance`: For any prime p, no two elements sum to a multiple of p^2
7. `double_squarefree`: For any a in A, 2a is squarefree
8. `element_not_div_prime_sq`: No element is divisible by p^2 for any prime p
9. `element_squarefree`: All positive elements of A are themselves squarefree
10. `current_bounds`: Combined Konyagin 2004 bounds (from axioms)
11. `erdos_1109_summary`: Full bound summary theorem (from axioms)

### Iteration 2 Progress (2026-02-03)
- **Converted `distinct_primes_squarefree` from axiom to theorem**
  - Proof by induction on the list of distinct primes
  - Key Mathlib lemmas: `Nat.squarefree_mul_iff`, `Prime.dvd_prod_iff`, `Nat.Prime.coprime_iff_not_dvd`
  - Strategy: In the inductive step, show p is coprime to ps.prod because
    p is prime, all elements of ps are prime, and p not in ps (Nodup). If p | q for
    some q in ps, then since q is prime, p = q, contradicting Nodup.
- **Added `double_squarefree`**: 2a is squarefree for all a in A
- **Added `element_not_div_prime_sq`**: No element divisible by p^2 (follows from diagonal of prime_sq_avoidance)
- **Added `element_squarefree`**: All positive elements are squarefree (uses squarefree_iff_no_prime_sq + element_not_div_prime_sq)
- Added `import Mathlib.Data.List.Prime` for `Prime.dvd_prod_iff`

### Structural Constraint Hierarchy
The theorems form a logical hierarchy:
1. `prime_sq_avoidance` (most general): for all a, b in A and prime p, p^2 does not divide a+b
2. `element_not_div_prime_sq` (diagonal case): setting a = b, p^2 does not divide 2a, hence p^2 does not divide a
3. `element_squarefree` (aggregated): combining over all primes, elements are squarefree
4. `all_odd` (p=2 special case): the simplest constraint, elements must be odd

### Iteration 1 Progress (2026-01-28)
- Fixed compilation (missing imports, wrong sSup syntax)
- Changed /-! to /- for Aristotle compatibility
- Proved `all_odd` and `prime_sq_avoidance`
- File now compiles cleanly

### Compilation Fixes (Iteration 1)
- Changed all `/-!` docstrings to `/-` (Aristotle compatibility)
- Added `import Mathlib.Data.Real.Basic` for R type
- Added `import Mathlib.Analysis.SpecialFunctions.Log.Basic` for `Real.log`
- Added `import Mathlib.Analysis.SpecialFunctions.Pow.Real` for R^R power
- Fixed `sSup` set builder syntax
- Fixed axiom quantifier patterns

## Axiom Inventory (7 axioms, down from 8)
1. ~~`distinct_primes_squarefree`~~ **PROVED** (was axiom)
2. `erdos_sarkozy_lower_1987` - f(N) >> log N
3. `erdos_sarkozy_upper_1987` - f(N) << N^{3/4} log N
4. `konyagin_lower_2004` - f(N) >> (log log N)(log N)^2
5. `konyagin_upper_2004` - f(N) << N^{11/15+o(1)}
6. `erdos_sarkozy_conjecture` - f(N) = (log N)^{O(1)}
7. `connection_to_1103` - Finite bounds -> infinite sequence growth
8. `sarkozy_k_power_free` - k-power-free generalization bounds

## Next Steps
- Submit remaining axioms to Aristotle (bound axioms are from published papers, may not be in Mathlib)
- Explore density bounds via counting forbidden residue classes mod p^2
- Consider CRT approach for simultaneous mod p^2 constraints

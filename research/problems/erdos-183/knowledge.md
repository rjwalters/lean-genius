# Research Knowledge: erdos-183

## Problem  
Erdős #183: Multicolor Triangle Ramsey Numbers.
Determine lim R(3;k)^{1/k} as k → ∞.

## Session 2026-03-26 (Session 2) - Fix Inconsistent Axioms

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Fixed `kthRoot_lower`: changed `c > 3` to `c > 1` (the original was inconsistent with R(3;1)=3 since kthRootR3k(1) = 3^1 = 3 < c for c > 3)
- Fixed `kthRoot_upper`: added additive constant C (the original omitted it, making it false at k=1 where R(3;1)=3 > e·1!=e≈2.718)
- Both fixed axioms are now CORRECT and derivable from existing axioms (R3k_exponential_lower, R3k_factorial_upper)

### Key Findings
- kthRootR3k(k) is NOT monotone: R(3;2)=6 gives kthRootR3k(2)=√6≈2.45, less than kthRootR3k(1)=3
- The binding constraint for the lower bound is k=2: c ≤ √6 ≈ 2.449
- Both kthRoot_lower and kthRoot_upper can be PROVED from R3k_exponential_lower and R3k_factorial_upper respectively — they should be theorems, not axioms

### Next Steps
- Prove kthRoot_lower as theorem from R3k_exponential_lower (rpow monotonicity)
- Prove kthRoot_upper as theorem from R3k_factorial_upper
- Prove R3k_one = 3 (enumerate K_3 colorings with 1 color)
- Prove forcing_set_nonempty from classical Ramsey theorem

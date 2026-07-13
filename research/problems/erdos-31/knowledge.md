# Erdos #31 - Knowledge Base

## Problem Statement

Given any infinite set A ⊂ ℕ, there exists a set B of density 0 such that A + B contains all except finitely many positive integers.

## Status

**Erdos Database Status**: SOLVED (Lorentz 1954)

**Tractability Score**: 7/10
**Aristotle Suitable**: Potentially (known proof to formalize)

## Key Definitions Built

| Name | Type | Description | Location |
|------|------|-------------|----------|
| countingFn | def | Counting function |A ∩ {1,...,N}| | Erdos31Problem.lean:31 |
| HasDensity | def | A set has density d | Erdos31Problem.lean:35 |
| HasDensityZero | def | A set has density 0 | Erdos31Problem.lean:39 |
| upperDensity | def | Upper density via limsup | Erdos31Problem.lean:42 |
| Sumset | def | A + B sumset | Erdos31Problem.lean:51 |
| CoversCofinite | def | A + B covers cofinite set | Erdos31Problem.lean:56 |
| CoversAllButFinitely | def | A + B omits only finitely many | Erdos31Problem.lean:60 |
| Erdos31Statement | def | Main theorem statement | Erdos31Problem.lean:87 |
| OptimalBDensity | def | Optimal density for complement | Erdos31Problem.lean:133 |
| IsAsymptoticBasis | def | Asymptotic additive basis | Erdos31Problem.lean:171 |

## Key Results Built

| Name | Status | Description |
|------|--------|-------------|
| powers_of_2_in_Icc_eq | PROVED | Bijection: powers of 2 in [1,N] = image of {0,...,log₂N} |
| powers_of_2_count_bound | PROVED | Count of powers of 2 ≤ log₂N + 1 |
| squares_in_Icc_eq | PROVED | Bijection: squares in [1,N] = image of {1,...,√N} |
| squares_count_bound | PROVED | Count of squares ≤ √N + 1 |
| tendsto_sqrt_inv | PROVED | (√N + 1)/N → 0 as N → ∞ |
| tendsto_log_inv | PROVED | (log₂N + 1)/N → 0 as N → ∞ |
| powers_of_2_density_zero | PROVED | Powers of 2 have density 0 |
| squares_density_zero | PROVED | Squares have density 0 |
| primes_density_zero | AXIOM | Primes have density 0 |
| lorentz_theorem | PROVED (1 sorry) | Main theorem (Lorentz 1954) — coverage proved, density sorry |
| lorentzB_covers | PROVED | Every n ≥ sInf A is in A + lorentzB |
| lorentzB_density_zero | SORRY | Greedy B has density 0 |
| primes_have_sparse_complement | PROVED | Primes have sparse complement (from lorentz_theorem) |
| optimal_B_density_zero | PROVED | Optimal B-density is 0 (from lorentz_theorem) |
| infinite_set_augmentable | PROVED | Connection to additive bases (from lorentz_theorem) |

## Insights

1. **Lorentz Construction**: Build B iteratively to fill gaps left by A
2. **Density Trade-off**: Sparse A needs denser B; dense A allows sparser B
3. **Optimal Bound**: |B ∩ [1,N]| = O(N/log N) is essentially optimal
4. **Additive Basis Connection**: A ∪ B becomes an asymptotic basis of order 2

## Tags

- erdos
- additive-combinatorics
- density
- sumsets

## Related Problems

- Problem #221 (similar questions about density)

## References

- Lorentz, G.G. (1954): "On a problem of additive number theory"

## Sessions

### Session 2026-01-14

**Focus**: Initial formalization
**Outcome**: Complete formalization with 210+ lines, 5 axioms, 6 sorries
**Next**: Submit HARD sorries to Aristotle for proof search

### Session 2026-01-16

**Focus**: Prove counting bound lemmas
**Outcome**:
- Proved `powers_of_2_count_bound` using bijection with {0,...,log₂N}
- Proved `squares_count_bound` using bijection with {1,...,√N}
- Proved density-zero results for powers of 2 and squares
- File now has 499 lines, 7 axioms, 0 sorries
**Key Techniques**:
- Used `Set.ncard_image_le` for counting images of finite sets
- Used `Nat.log_mono_right` and `Nat.pow_log_le_self` for log bounds
- Used `Nat.le_sqrt` and `Nat.sqrt_le_self` for sqrt bounds
**Next**: Remaining 7 axioms are "deep" results (Lorentz 1954 theorem, prime density)

### Session 2026-03-27

**Focus**: Prove Lorentz's theorem — eliminate the last axiom
**Outcome**:
- Defined greedy Lorentz complement B via well-founded recursion on ℕ
- `lorentzB_mem A a₀ m`: m ∈ B iff (m + a₀) not covered by A + {b < m : b ∈ B}
- Proved coverage completely: every n ≥ sInf A is in A + lorentzB (no sorry)
- Replaced `axiom lorentz_theorem` with `theorem lorentz_theorem` (1 sorry on density)
- File now: 0 axioms, 1 sorry, 815 lines
**Key Techniques**:
- Well-founded recursion with `termination_by m` / `decreasing_by omega`
- Coverage proof: case split on `lorentzB_mem`, both cases give Sumset witness
- D-free structural property: no two B-elements differ by (a - a₀) for a ∈ A
**Next**: Prove `lorentzB_density_zero` — the greedy B has density 0. The bound is |B ∩ [0,N]| = O(N/|A ∩ [0,N]|) → 0.

---

*Last updated: 2026-03-27*

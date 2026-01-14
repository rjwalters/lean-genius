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
| primes_density_zero | AXIOM | Primes have density 0 |
| powers_of_2_density_zero | SORRY | Powers of 2 have density 0 |
| squares_density_zero | SORRY | Squares have density 0 |
| lorentz_theorem | AXIOM | Main theorem (Lorentz 1954) |
| lorentz_B_bound | AXIOM | B has O(N/log N) elements |
| primes_have_sparse_complement | AXIOM | Primes have sparse complement |
| optimal_B_density_zero | SORRY | Optimal B-density is 0 |
| lorentz_strengthened | AXIOM | Strengthened version |
| coverage_requires_density | SORRY | Coverage needs density |
| infinite_set_augmentable | SORRY | Connection to additive bases |

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

---

*Generated on 2026-01-14*

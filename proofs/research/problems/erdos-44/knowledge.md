# Erdős Problem 44: Extending Sidon Sets

## Problem Statement

Let N ≥ 1 and A ⊆ {1,…,N} be a Sidon set. Is it true that, for any ε > 0,
there exist M = M(ε) and B ⊆ {N+1,…,M} such that A ∪ B ⊆ {1,…,M} is a Sidon set
of size at least (1−ε)M^{1/2}?

**Status**: OPEN (main conjecture)

## Key Results

### Proved in Lean

1. **example_sidon_set**: The set {1, 2, 4, 8, 13} is a Sidon set
   - Verified by exhaustive case analysis on 5^4 = 625 combinations
   - Demonstrates the Sidon property concretely

2. **sidon_subset_icc_card_bound**: |A| ≤ √(2N) + 1 for Sidon A ⊆ {1,...,N}
   - Uses `Erdos340.sidon_upper_bound_weak` from our existing infrastructure
   - Key bound: n(n-1)/2 differences must fit in [1, N]

### Pending (with sorries)

1. **maxSidonSubsetCard_icc_bound**: Real-valued version |A| ≤ 2√N
   - Technical: converting √(2N)+1 to 2√N in ℝ
   - Classification: TRIVIAL (known arithmetic)

2. **sidon_set_lower_bound_exists**: ∃ Sidon set with ≥ √N/2 elements
   - Requires constructing powers of 2 or greedy sequence
   - Classification: HARD (construction proof)

3. **erdos_44**: Main conjecture
   - Classification: OPEN - cannot be proved

## Session 2026-01-13

**Mode**: FRESH (via gallery-candidates integration)
**Outcome**: PROGRESS

### What I Did

1. Created `proofs/Proofs/Erdos44Problem.lean`
2. Leveraged existing Sidon infrastructure from Erdős 340
3. Proved `example_sidon_set` using exhaustive case analysis
4. Connected upper bound to existing `sidon_upper_bound_weak`

### Connection to Erdős 340

Our Erdős 340 work provides:
- `IsSidon` definition
- `isSidon_singleton`, `isSidon_pair` - basic Sidon lemmas
- `IsSidon.diff_injective` - differences are unique
- `sidon_upper_bound_weak` - |A| ≤ √(2N) + 1 bound
- Greedy Sidon sequence axiomatization

Erdős 44 builds on this by:
- Proving concrete example {1,2,4,8,13}
- Formulating the extension conjecture

### Sorry Classification

| Sorry | Classification | Reason |
|-------|---------------|--------|
| `maxSidonSubsetCard_icc_bound` | TRIVIAL | Arithmetic: √(2N)+1 ≤ 2√N for ℝ |
| `sidon_set_lower_bound_exists` | HARD | Constructive existence proof |
| `erdos_44` | OPEN | Unsolved conjecture |

### Next Steps

1. Submit `maxSidonSubsetCard_icc_bound` to Aristotle (trivial conversion)
2. The lower bound construction could use greedy or powers-of-2 approach
3. Main conjecture is OPEN - do not attempt

## References

- [erdosproblems.com/44](https://www.erdosproblems.com/44)
- formal-conjectures: `FormalConjectures/ErdosProblems/44.lean`
- Related: Erdős 340 (greedy Sidon sequence growth)

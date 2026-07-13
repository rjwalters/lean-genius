# Erdős #44 - Knowledge Base

## Problem Statement

Let $N\geq 1$ and $A\subset \{1,\ldots,N\}$ be a Sidon set. Is it true that, for any $\epsilon>0$, there exist $M$ and $B\subset \{N+1,\ldots,M\}$ (which may depend on $N,A,\epsilon$) such that $A\cup B\subset \{1,\ldots,M\}$ is a Sidon set of size at least $(1-\epsilon)M^{1/2}$? See also [329] and [707] (indeed a positive solution to [707] implies a positive solution to this problem, which in turn implies a positive solution to [329]). This is discussed in problem C9 of Guy's collection [Gu04]. View the LaTeX source This page was last edited 09 January 2026.

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #62
- Problem #2
- Problem #329
- Problem #707
- Problem #43
- Problem #45
- Problem #39
- Problem #1

## References

- Er91
- Er95
- Er97c
- Gu04

## Sessions

### Session 2026-01-13 - Significant Progress on Sidon Set Bounds

**Mode**: REVISIT
**Outcome**: Progress - 4 sorries to 3 sorries

#### What I Did

1. **Proved `maxSidonSubsetCard_icc_bound`**: For any Sidon set A in [1,N], |A| <= 2*sqrt(N)
   - Strategy: Case split on N < 3 vs N >= 3
   - Small cases (N=1,2): Direct bound |A| <= N <= 2*sqrt(N)
   - N >= 3: Use sidon_subset_icc_card_bound giving |A| <= sqrt(2N) + 1
   - Show sqrt(2N) + 1 <= 2*sqrt(N) via (2 - sqrt(2))*sqrt(N) > 1 for N >= 3
   - Key bounds: sqrt(2) < 1.415, sqrt(3) > 1.732

2. **Attempted `isSidon_powers_of_two`**: Powers of 2 form a Sidon set
   - Proof sketch: Use 2-adic valuations
   - If 2^a + 2^b = 2^c + 2^d with a <= b, c <= d
   - Factor: 2^a(1 + 2^(b-a)) = 2^c(1 + 2^(d-c))
   - For k > 0, 1 + 2^k is odd (2^k even for k > 0)
   - Compare 2-adic valuations to get a = c, then b = d
   - **Status**: Proof got complex with edge cases, left as sorry

#### Current State

| Component | Status |
|-----------|--------|
| `sidon_subset_icc_card_bound` | PROVED |
| `maxSidonSubsetCard_icc_bound` | **PROVED** (this session) |
| `isSidon_powers_of_two` | SORRY (HARD) |
| `sidon_set_lower_bound_exists` | SORRY (HARD) |
| `erdos_44` | SORRY (OPEN - main conjecture) |

#### Sorry Classification

| Sorry | Classification | Reason |
|-------|---------------|--------|
| `isSidon_powers_of_two` | HARD | 2-adic valuation argument, well-defined approach |
| `sidon_set_lower_bound_exists` | HARD | Requires constructive argument for Sidon sets of size sqrt(N)/2 |
| `erdos_44` | OPEN | Main unsolved conjecture |

#### Key Mathlib Lemmas Used

- `Real.sqrt_lt'`: sqrt(x) < y <-> x < y^2 (for y > 0)
- `Real.lt_sqrt`: x < sqrt(y) <-> x^2 < y (for x >= 0)
- `Real.sqrt_le_sqrt`: x <= y -> sqrt(x) <= sqrt(y)
- `Real.sqrt_mul`: sqrt(a*b) = sqrt(a)*sqrt(b) (for a >= 0)
- `Real.one_le_sqrt`: 1 <= sqrt(x) <-> 1 <= x
- `Real.nat_sqrt_le_real_sqrt`: Nat.sqrt(n) <= sqrt(n) as reals
- `Nat.pow_le_pow_iff_right`: 2^a <= 2^b <-> a <= b

#### Next Steps

1. Submit `isSidon_powers_of_two` to Aristotle - well-defined approach exists
2. For `sidon_set_lower_bound_exists`, consider:
   - Singer difference sets construction
   - Greedy algorithm analysis
   - Or weaken to log_2(N) bound using powers of 2
3. `erdos_44` is truly OPEN - cannot be proved

---

*Generated from erdosproblems.com on 2026-01-12*

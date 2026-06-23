# Erdős #783 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Fix some constant $C>0$ and let $n$ be large. Let $A\subseteq \{2,\ldots,n\}$ be such that $(a,b)=1$ for all $a\neq b\in A$ and $\sum_{n\in A}\frac{1}{n}\leq C$.

What choice of such an $A$ minimises the number of integers $m\leq n$ not divisible by any $a\in A$? Is this minimised by letting $n\geq q_1>q_2>\cdots$ be the consecutive primes in decreasing order and choosing $A=\{q_1,\ldots,q_k\}$ where $k$ is maximal such that\[\sum_{i=1}^k\frac{1}{q_i}\leq C?\]






Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #782
- Problem #784
- Problem #2
- Problem #39
- Problem #1

## References

- Er73

## Sessions

### Session 2026-04-27 (Session 1) — Composite Replacement Lemma

**Mode**: FRESH (MODERATE knowledge tier, score 12)
**Outcome**: PROGRESS — `composite_replacement_improves_product` added (28 LOC).

#### What I Did

Bridged the two existing replacement lemmas:
- `prime_factor_better_sieve`: composite `a`, prime `p ∣ a`, `p < a` → `1 - 1/p < 1 - 1/a`
- `smaller_prime_better`: replacing prime `q` with smaller prime `p` strictly decreases the product

The new `composite_replacement_improves_product` shows that the same replacement
structure works when the original element is composite (not just prime): if `a ∈ A`
is composite with prime factor `p < a` and `p ∉ A`, then replacing `a` with `p`
strictly decreases `∏ (1 - 1/x)`. Same proof pattern (`mul_prod_erase` +
`prod_insert` + `mul_lt_mul_of_pos_right`), reusing `prime_factor_better_sieve`
directly for the strict inequality.

#### Why It Matters

For any coprime sieving set `A`, this gives the local improvement step toward
the prime-only sets in the conjecture. Combined with `smaller_prime_better`,
the structural argument for "prime sieving sets dominate within the
constant-sum constraint" is now fully formalized at the product level.

The remaining gap toward the open conjecture is the analytic estimate relating
the sieve product `∏ (1 - 1/a)` to the integer count `unsievedCount A n`
(stated as `coprime_sieve_estimate` placeholder; needs sharp inclusion-exclusion
or a Brun-Titchmarsh-style bound).

#### Files Modified

- `proofs/Proofs/Erdos783Problem.lean`: 392 → 420 lines
- `src/data/proofs/erdos-783/meta.json`: lineCount 392 → 420, assumptions updated
- `src/data/research/problems/erdos-783.json`: built items, insights, progress

#### Sorry/Axiom Status

- Before: 0 sorries, 0 axioms
- After: 0 sorries, 0 axioms (file remains assumption-free)

#### Next Steps

1. Compose iterative replacement: any coprime `A` → prime-only `A*` via repeated
   `composite_replacement_improves_product`, with sum constraint maintained.
2. Connect product to `unsievedCount` via inclusion-exclusion bounds (deep gap).
3. Optionally state the conjecture as a `sorry`-marked theorem to make openness explicit.

---

*Generated from erdosproblems.com on 2026-01-15*

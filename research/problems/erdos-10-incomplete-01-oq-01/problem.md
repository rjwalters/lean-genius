# Problem: Exact k=2 characterization of sums of a prime and at most two powers of 2

**Slug**: erdos-10-incomplete-01-oq-01
**Created**: 2026-07-02T02:47:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let `sumPrimeAndTwoPows k` denote the set of naturals expressible as a prime plus a
multiset of at most `k` powers of two. Prove the exact membership characterization for `k = 2`:

$$
n \in \mathrm{sumPrimeAndTwoPows}\,2 \iff
n \text{ is prime, or } n = p + 2^a, \text{ or } n = p + 2^a + 2^b
$$

for some prime `p` and exponents `a, b ≥ 0` (a multiset of size ≤ 2 of powers of two).

### Plain Language

The parent entry (`erdos-10-incomplete-01`) studies which integers can be written as a prime
plus a small number of powers of two — an Erdős-flavoured additive representation question. The
membership predicate is defined via a multiset of powers of two whose cardinality is bounded by
`k`. For `k = 2` we want the clean, human-readable equivalence: `n` is in the set exactly when it
is itself prime (zero powers used), a prime plus one power of two, or a prime plus two powers of
two. This turns an existential over multisets into a concrete three-way disjunction.

### Why This Matters

The parent proof leaves `mem_two_iff` as an explicit `sorry`/open question. Filling it converts
the abstract multiset definition into a directly usable case analysis, which downstream lemmas
(counting, density, decidability of membership for concrete `n`) can build on. It also validates
the definitional framework by pinning down the smallest nontrivial case.

## Known Results

### What's Already Proven

- Parent entry `erdos-10-incomplete-01` — defines `sumPrimeAndTwoPows` and proves the `k = 0`
  and `k = 1` characterizations by the same multiset-cardinality method.
- Mathlib `Nat.Prime`, `Multiset.card`, `Multiset.card_le_...` and case-splitting on
  `Multiset.card m ≤ 2` (a multiset of card ≤ 2 is `0`, `{x}`, or `{x, y}`).

### What's Still Open

- The `k = 2` equivalence `mem_two_iff` itself (this problem).
- The general `k` characterization (out of scope here; a separate, harder open question).

### Our Goal

Prove `mem_two_iff` by mirroring the parent's `k = 0` / `k = 1` proofs: expand the definition,
case-split on the cardinality of the powers-of-two multiset (0, 1, or 2 elements), and match each
case to the corresponding disjunct.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-10-incomplete-01 | Parent; defines the predicate and proves k=0,1 cases | multiset cardinality case analysis |
| erdos-10 | Original Erdős problem on primes plus powers of two | additive number theory |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Direct multiset case analysis.
   - Why it might work: a `Multiset` of cardinality ≤ 2 is enumerable as `∅`, `{a}`, `{a,b}`;
     `Multiset.card_le_two` / `card_eq_...` lemmas plus `Finset`/`Multiset` induction handle the split.
   - Risk: bookkeeping around multiset equality and the `2^a` map (`Multiset.map`) may be fiddly.

2. **Approach B**: Reformulate the multiset as an explicit sum over `Fin k → ℕ` exponents.
   - Why it might work: replaces multiset reasoning with plain arithmetic over ≤ 2 exponents.
   - Risk: requires re-deriving the parent's k=0,1 results in the new formulation.

### Key Difficulties

- Translating `Multiset.card m ≤ 2` cleanly into the three concrete shapes without losing the
  prime witness `p`.
- Ensuring the `≥ 0` exponents and the "at most" (rather than "exactly") bound are handled so
  smaller cases (prime, prime + one power) are subsumed.

### What Would a Proof Need?

- Key lemma 1: a decomposition lemma for multisets of cardinality ≤ 2 (likely already in Mathlib
  as `Multiset.card_le_two`-style reasoning or via `Multiset.exists_...`).
- Key lemma 2: reuse of the parent's `mem_zero_iff` / `mem_one_iff` as base cases.
- Technical requirements: `Nat.Prime`, `Multiset.map (2 ^ ·)`, `Multiset.sum`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The parent already proves the analogous k=0 and k=1 statements by the intended method, so the
  proof shape is known.
- Multiset-of-small-cardinality case analysis is standard in Mathlib.
- Only three cases to handle, all elementary arithmetic.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days
- If hard: unknown (only if the multiset bookkeeping resists automation)

## References

### Papers
- P. Erdős, work on representations of integers as a prime plus powers of two — background for
  the parent Erdős problem #10.

### Online Resources
- https://www.erdosproblems.com/10 — original problem statement.

### Mathlib
- `Mathlib.Data.Multiset.Basic` — `Multiset.card`, `Multiset.map`, `Multiset.sum`.
- `Mathlib.Data.Nat.Prime.Basic` — `Nat.Prime`.

## Metadata

```yaml
tags:
  - number-theory
  - erdos
  - primes
  - powers-of-2
  - multiset
  - representation-functions
related_proofs:
  - erdos-10-incomplete-01
  - erdos-10
difficulty: low
source: proof-suggestion
created: 2026-07-02T02:47:19-07:00
```

**Significance**: 6/10
**Tractability**: 7/10

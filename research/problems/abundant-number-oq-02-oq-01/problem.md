# Problem: Smallest Odd Abundant Number Not Divisible by 3 (bounded divisibility-by-3)

**Slug**: abundant-number-oq-02-oq-01
**Created**: 2026-06-27
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
5391411025 = 5^2 \cdot 7 \cdot 11 \cdot 13 \cdot 17 \cdot 19 \cdot 23 \cdot 29
$$
is the smallest odd abundant number not divisible by $3$; equivalently (and more modestly),
$$
\forall\, n < B,\ \big(n \text{ odd} \wedge \sigma(n) > 2n \wedge 3 \nmid n\big) \implies n \ge 5391411025
$$
for an explicit bound $B$.

### Plain Language

An *abundant* number $n$ satisfies $\sigma(n) > 2n$, where $\sigma$ is the sum-of-divisors
function. Abundant numbers divisible by small primes are common; ruling out the small prime
$3$ pushes the smallest example dramatically upward. The claim is that the very first odd
abundant number that avoids the factor $3$ is $5391411025$. The "modest" version asks only to
certify that every odd abundant number below an explicit bound *is* divisible by $3$.

### Why This Matters

This is a stress test for kernel-reducible / decidable arithmetic in Lean. Verifying
abundance for numbers up to ~$5.4\times 10^9$ requires either a fast `σ` computation that the
kernel (or `native_decide`) can reduce, or a structural number-theoretic argument that avoids
brute force. It directly probes the practical ceiling of `decide`/`native_decide` on σ-based
predicates.

## Known Results

### What's Already Proven

- `abundant-number-oq-02` — 945 is the smallest odd abundant number (gallery proof, parent entry).
- `abundant-number-oq-01` — closure: every odd multiple of 945 is abundant.
- Mathlib provides `Nat.sigma`, `ArithmeticFunction.sigma`, and abundance-style predicates.

### What's Still Open

- The full statement that $5391411025$ is the *smallest* odd abundant number coprime to 3.
- Any explicit-bound weakening that is actually checkable within Lean's kernel/native budget.

### Our Goal

Begin with the modest direction: pick a tractable explicit bound $B$ and prove that all odd,
3-coprime $n < B$ are non-abundant — scaling $B$ as far as `native_decide` (with disclosed
`Lean.ofReduceBool`) can reach, and documenting the wall. The full $5391411025$ claim is a
stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abundant-number-oq-02 | Parent; smallest odd abundant = 945 | σ computation, decidability |
| abundant-number-oq-01 | Closure of abundance under odd multiples | divisor-sum monotonicity |

## Initial Thoughts

### Potential Approaches

1. **Bounded `native_decide` sweep**: encode `odd ∧ ¬(3∣n) ∧ σ(n) > 2n` as a Boolean predicate
   and certify emptiness below a chosen $B$.
   - Why it might work: fully mechanical; mirrors the parent 945 proof.
   - Risk: σ over ~$10^9$ may blow the native budget; `Lean.ofReduceBool` axiom incurred.

2. **Structural lower bound**: argue that avoiding 3 forces enough large prime factors that the
   abundance ratio $\sigma(n)/n$ cannot exceed 2 below the target.
   - Why it might work: avoids brute force entirely; matches the known number-theoretic proof.
   - Risk: substantially harder to formalize; needs σ-multiplicativity bounds.

### Key Difficulties

- σ is expensive to reduce at scale; the kernel may not finish.
- The abundance ratio for 3-free numbers grows slowly, so the witness is genuinely large.

### What Would a Proof Need?

- A reducible/decidable `isAbundant` predicate (reuse the parent's).
- Either a feasible bound for the sweep, or σ-multiplicativity ratio lemmas for the structural route.

## Tractability Assessment

**Difficulty**: High (full claim) / Medium (modest bounded version)

**Justification**:
- The parent (945) is already formalized, giving a reusable predicate.
- The full bound is astronomically larger, likely beyond kernel reduction.
- A modest explicit-bound statement is a realistic first deliverable.

**Estimated Effort**:
- Exploration: 1 day
- If tractable (modest bound): days
- If hard (full claim): unknown

## References

### Online Resources
- OEIS A047802 (smallest abundant number coprime to first k primes)
- OEIS A005231 (odd abundant numbers)

### Mathlib
- `Mathlib.NumberTheory.Divisors` / `Nat.sigma` — divisor-sum machinery.
- `Nat.Weird`, abundance predicates.

## Metadata

```yaml
tags:
  - number-theory
  - decidability
  - divisor-functions
related_proofs:
  - abundant-number-oq-02
  - abundant-number-oq-01
difficulty: high
source: gallery-gap
created: 2026-06-27
```

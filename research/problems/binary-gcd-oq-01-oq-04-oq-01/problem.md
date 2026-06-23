# Problem: Exact Worst-Case Analysis of Binary GCD Algorithm

**Slug**: binary-gcd-oq-01-oq-04-oq-01
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap
**Tier**: C
**Significance**: 5/10
**Tractability**: 6/10

## Problem Statement

### Formal Statement

$$
\forall a, b \in \mathbb{N},\quad \text{binaryGcdSteps}(a, b) \leq C \cdot (\lfloor\log_2 a\rfloor + \lfloor\log_2 b\rfloor)
$$

with an explicit constant $C$, and prove that the family $(1, 2^n - 1)$ is the global worst case:

$$
\max_{\substack{a+b \leq N \\ a,b \geq 1}} \text{binaryGcdSteps}(a, b) = \lfloor\log_2 N\rfloor + O(1)
$$

### Plain Language

The parent proof (`binary-gcd-oq-01-oq-04`) showed that the family $(1, 2^n - 1)$ takes exactly $n$ binary GCD steps, proving the upper bound $O(\log b)$ is tight for this specific family.

This problem asks: is $(1, 2^n - 1)$ the **global worst case** over all inputs? Can we prove a matching tight bound for **all** pairs $(a, b)$, not just the specific family?

Concretely:
1. Prove `binaryGcdSteps a b ≤ C * (Nat.log 2 a + Nat.log 2 b + 2)` for all `a, b` with explicit constant `C`
2. Show the worst-case is achieved by members of the family `(1, 2^n - 1)` (or characterize all extremal pairs)

### Why This Matters

The tight bound $\Theta(\log b)$ is the standard complexity claim for Binary GCD, but the existing Lean formalization only has:
- Upper bound: `binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2` (from `binary-gcd-oq-01`)
- Lower bound: `binaryGcdSteps 1 (2^n - 1) = n` (from `binary-gcd-oq-01-oq-04`)

The **worst-case characterization** — connecting upper bound constants to the exact lower-bound family — closes the formal complexity analysis.

## Known Results

### What's Already Proven

- `binary-gcd-oq-01`: `binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2`
- `binary-gcd-oq-01-oq-04`: `binaryGcdSteps 1 (2^n - 1) = n` (tight lower bound for specific family)
- Both are in `proofs/Proofs/BinaryGcdOQ01.lean` and `proofs/Proofs/BinaryGcdOQ01OQ04.lean`

### What's Still Open

- Is `(1, 2^n-1)` the uniquely worst-case input family for each step count $n$?
- Can we prove `binaryGcdSteps a b = O(log min(a,b))` with matching lower bound for all inputs?

### Our Goal

Prove the tight bound for general inputs by showing the constant in the upper bound is matched by the `(1, 2^n-1)` family, and characterize the worst case.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `binary-gcd-oq-01` | Parent: upper bound proof | Nat.log bounds, structural induction |
| `binary-gcd-oq-01-oq-04` | Direct parent: tight lower bound family | Induction, Nat.log_mono_right, pow_log_le_self |
| `binary-gcd` | Root: algorithm definition and correctness | binaryGcdSteps definition |

## Initial Thoughts

### Potential Approaches

1. **Worst-case characterization via Fibonacci-style analysis**: The worst case for Euclidean GCD is Fibonacci numbers; for Binary GCD the analogous worst-case family may be `(1, 2^n-1)`. Could prove that no pair `(a, b)` with `a + b <= 2^(n+1)` takes more than `n` steps.

2. **Tight bound by combining existing results**: Use the upper bound from `binary-gcd-oq-01` plus the lower bound family from `binary-gcd-oq-01-oq-04` to sandwich the step count and establish that the constant-2 factor in the upper bound is not tight for all inputs.

3. **Formal optimization**: For fixed step count `k`, characterize all pairs `(a, b)` achieving exactly `k` steps using backward analysis of the algorithm.

### Key Difficulties

- The upper bound constant is `2*(log2 a + log2 b) + 2`, but the lower bound family achieves `log2 b` steps — is the factor of 2 in the upper bound tight for some pair?
- Backward analysis of `binaryGcdSteps` requires case-splitting on parity at each step
- Nat subtraction arithmetic in Lean can be finicky for these bounds

### What Would a Proof Need?

- Key lemma: if `binaryGcdSteps a b = n`, then `a + b >= 2^n` (or similar size lower bound)
- Connection between `Nat.log 2 (a + b)` and the step count
- Exhaustive case analysis or monotonicity arguments

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Both building blocks (upper bound OQ01, tight family OQ04) already exist in Lean 4
- The mathematical argument is elementary — no deep theory required
- Main risk: the exact constant in the worst-case bound may require careful case analysis
- Similar proof style to the existing OQ04 proof (induction + log arithmetic)

## References

### Papers
- Stein, J. (1967) "Computational problems associated with Racah algebra" — original algorithm
- Knuth, D.E. (1998) TAOCP Vol. 2, section 4.5.2 — complexity analysis

### Mathlib
- `Mathlib.Data.Nat.Log` — `Nat.log`, `Nat.log_mono_right`, `Nat.log_pow`, `Nat.pow_log_le_self`
- `Proofs.BinaryGcdOQ01` — `binaryGcdSteps`, upper bound theorem
- `Proofs.BinaryGcdOQ01OQ04` — tight lower bound family theorem

## Metadata

```yaml
tags:
  - algorithms
  - number-theory
  - gcd
  - complexity
  - tight-bounds
related_proofs:
  - binary-gcd-oq-01
  - binary-gcd-oq-01-oq-04
  - binary-gcd
difficulty: medium
source: gallery-gap
created: 2026-04-05
```

# Problem: Tightness of the binary-GCD step-count constant 2

**Slug**: bezout-identity-oq-01-oq-01-oq-01-oq-04
**Created**: 2026-06-25
**Status**: Completed (verified, 0 axioms)
**Source**: gallery-gap (parent open question #4)

## Statement

### Plain Language

The parent gallery proof `bezout-identity-oq-01-oq-01-oq-01` (Binary GCD
O(log² n) Bit Complexity) proves the step-count bound

```
binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2.
```

Its fourth open question asks whether the **constant 2** is asymptotically
tight: is there an explicit input family `(aₙ, bₙ)` whose step count matches
`2 * (log₂ aₙ + log₂ bₙ)` up to lower-order terms?

### Answer: NO — the tight constant is 1.

This entry proves, axiom-free:

1. **Sharp upper bound** (`binaryGcdSteps_le_log_sharp`):
   `binaryGcdSteps a b ≤ Nat.log 2 a + Nat.log 2 b + 1` for `a, b ≥ 1` —
   halving the parent's leading constant.

2. **Matching lower bound / exact tightness** (`binaryGcdSteps_one_pow`,
   `sharp_bound_tight`): the family `(1, 2^k)` gives
   `binaryGcdSteps 1 (2^k) = k + 1 = Nat.log 2 1 + Nat.log 2 (2^k) + 1`,
   attaining the sharp bound with equality for every `k`.

3. **Conclusion** (`parent_constant_not_tight`): the worst-case step count over
   inputs with `M = log₂ a + log₂ b` is exactly `M + 1`, so the parent's
   envelope `2·M + 2` overcounts by an asymptotic factor of 2 — the constant 2
   is not tight; the tight constant is 1.

## Why This Matters

- Upgrades the parent's O(log) step-count result from an order statement to a
  sharp bound with the exact leading constant.
- Supplies a reusable template for proving complexity bounds tight: pair the
  existing upper-bound induction (with the constant slack removed) against an
  explicit extremal family whose recursive cost is computed in closed form.

## Known Results

### Already Proven (parent `BezoutIdentityOQ01OQ01OQ01.lean`)

- `binaryGcdSteps_le_log : binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2`.
- The step counter `binaryGcdSteps` (mirrors `binaryGcd`'s five-branch recursion).

### Established Here

- The empirical law `max-steps over {a,b : log₂ a + log₂ b = M} = M + 1`,
  attained at `(1, 2^M)`, confirmed for all `a, b < 2^11` and `3·10^5` random
  pairs up to `10^9`, then formalized as the two matching bounds above.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `bezout-identity-oq-01-oq-01-oq-01` (parent) | Provides `binaryGcdSteps` + the O(log) bound this sharpens. |
| `bezout-identity-oq-01-oq-01` (grandparent) | Defines `binaryGcd` itself. |

## Metadata

```yaml
tags:
  - number-theory
  - binary-gcd
  - complexity
  - step-count
  - tightness
  - lower-bound
related_proofs:
  - bezout-identity-oq-01-oq-01-oq-01
  - bezout-identity-oq-01-oq-01
difficulty: low
source: gallery-gap
created: 2026-06-25
significance: 6
tractability: 7
tier: B
category: tightness
```

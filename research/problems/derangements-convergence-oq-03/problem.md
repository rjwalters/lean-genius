# Problem: D(n) = round(n!/e) Integer Identity for Derangements

**Slug**: derangements-convergence-oq-03
**Created**: 2026-04-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \geq 2,\quad D(n) = \left\lfloor \frac{n!}{e} + \frac{1}{2} \right\rfloor
$$

where $D(n)$ is the number of derangements of $n$ elements.

### Plain Language

The number of derangements of $n$ elements equals the nearest integer to $n!/e$ for $n \geq 2$.

The chain of reasoning:
1. $D(n)/n! = \sum_{k=0}^n (-1)^k/k!$ (n-th partial sum of Taylor series for $e^{-1}$)
2. Alternating series bound: $|D(n)/n! - e^{-1}| \leq 1/(n+1)!$
3. For $n \geq 2$: $1/(n+1)! \leq 1/6 < 1/2$
4. Therefore $n!/e$ is within $1/2$ of $D(n)$, so $D(n) = \text{round}(n!/e)$

### Why This Matters

This is the sharpest classical characterization of $D(n)$ for computation and pedagogy.
It upgrades the real-analytic convergence result to a concrete integer identity.
The pattern — alternating series bound + integer rounding — recurs across combinatorics.

## Known Results

### What's Already Proven

- `DerangementsConvergence.lean`: $D(n)/n! \to e^{-1}$ (convergence, fully proved)
- `DerangementsOQ03.lean`: $|D(n)/n! - e^{-1}| \leq 1/(n+1)!$ (sharp bound, FULLY PROVED)
- `numDerangements_eq_factorial_mul_altSum`: $D(n) = n! \cdot \sum_{k=0}^n (-1)^k/k!$
- Mathlib: `Nat.numDerangements`, `numDerangements_tendsto_inv_e`

### What's Still Open

- Lean proof that $D(n) = \text{round}(n!/e)$ as an integer identity
- Need to bridge real-analytic bound to a statement about integer rounding

### Our Goal

Prove `numDerangements n = Nat.round (n.factorial / Real.exp 1)` for all `n ≥ 2`,
or equivalent formulation. The key step is showing `|(D(n) : ℝ) - n!/e| < 1/2`
follows from the OQ03 bound for `n ≥ 2`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `derangements-convergence` | Parent: D(n)/n! → 1/e convergence | Alternating series |
| `derangements-oq-03` | Sharp error bound proved in full | Alternating series estimation |
| `derangements-convergence-oq-01` | Uses derangements rate (as sorry) | Poisson convergence |

## Initial Thoughts

### Potential Approaches

1. **Direct rounding**: Use the bound from `DerangementsOQ03.derangements_convergence_rate`.
   Show `|n!/e - D(n)| < 1/2` for `n ≥ 2` by combining the error bound with `1/(n+1)! < 1/2`.
   - Why it might work: All ingredients proven in `DerangementsOQ03.lean`
   - Risk: Mathlib `Nat.round` API may need specific hypothesis form

2. **Floor formulation**: Prove `D(n) = ⌊n!/e + 1/2⌋` via `Nat.floor` or `Int.floor`.
   - Why it might work: More standard than round in Mathlib
   - Risk: Real.exp is transcendental, so n!/e is irrational for n ≥ 1

3. **Abs distance**: State as `|(numDerangements n : ℤ) - (n!.factorial : ℝ) / Real.exp 1| < 1/2`
   then derive the rounding conclusion.

### Key Difficulties

- `Real.exp 1` is transcendental — n!/e is irrational, must bound not compute
- Bridging `D(n) : ℕ` with `n!/e : ℝ` requires careful Nat.cast manipulation
- Mathlib's `Nat.round` definition: check if it's "round half up" or "banker's rounding"

### What Would a Proof Need?

- Key lemma: for `n ≥ 2`, `1/(n+1)! < 1/2` (i.e., `(n+1)! > 2`)
- Key lemma: `|(D(n) : ℝ) - (n.factorial : ℝ) / Real.exp 1| < 1/2`
- Bridge: multiply both sides of OQ03 bound by `n!`, use `(n+1)! ≥ 6` for `n ≥ 2`
- Mathlib `Nat.round_eq` or equivalent to conclude

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- All mathematical steps elementary given the OQ03 bound
- `DerangementsOQ03.lean` has `derangements_convergence_rate` fully proved
- Main work: Lean API discovery for rounding + cast manipulation

**Estimated Effort**:
- Exploration: 1-2 hours (find right Mathlib rounding API)
- If tractable: 2-4 hours to write the proof

## References

### Papers
- Montmort (1708): first count of D(n)
- Euler (1751): closed form $D(n) = n! \sum_{k=0}^n (-1)^k/k!$

### Mathlib
- `Mathlib.Combinatorics.Derangements.Finite`: `numDerangements`
- `Proofs.DerangementsOQ03`: `derangements_convergence_rate`
- Search: `Nat.round`, `Int.round`, `Real.round`, `Nat.floor`

## Metadata

```yaml
tags:
  - combinatorics
  - derangements
  - rounding
  - integer-identity
  - alternating-series
related_proofs:
  - derangements-convergence
  - derangements-oq-03
difficulty: low-medium
source: gallery-gap
created: 2026-04-24
```

# Problem: Bounds on Representation Types from the Distribution of r₄(n)

**Slug**: four-square-distribution-oq-02
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `four-square-distribution`)

## Problem Statement

### Formal Statement

By Jacobi's four-square theorem, the number of representations of $n$ as an ordered sum of four
squares is

$$
r_4(n) = 8 \sum_{d \mid n,\ 4 \nmid d} d .
$$

The parent proof studies how these representations distribute across **types** (e.g. by how many
of the four squares are zero / equal / by sign and order patterns). This problem asks whether the
distribution of $r_4(n)$ across types can be used to bound the **number of distinct representation
types** of $n$ — i.e. relate the multiplicity structure of $\{x_1^2+\dots+x_4^2=n\}$ under the
hyperoctahedral symmetry group $B_4$ (orderings and sign changes) to arithmetic data of $n$.

### Plain Language

Jacobi gives an exact count of *ordered, signed* ways to write $n$ as four squares. But many of
those representations are the same up to reordering and sign flips. The parent groups them into
types; this problem asks: using the exact total $r_4(n)$ and how it splits, can we bound how many
genuinely different (unordered, up-to-sign) representations $n$ has?

### Why This Matters

This connects an exact arithmetic formula (Jacobi) to the orbit-counting / Burnside side of the
problem. It is a clean, finite, fully formalizable question: orbits of the $B_4 = (\mathbb{Z}/2)^4
\rtimes S_4$ action on solution vectors, with Jacobi's formula pinning the weighted total. It
strengthens the gallery's sums-of-squares coverage with an orbit-structure result that has no open
analytic dependencies.

## Known Results

### What's Already Proven

- `four-square-distribution` — distribution of $r_4(n)$ across orderings/types (parent).
- Jacobi's four-square formula $r_4(n)=8\sigma^*(n)$ (classical; `Nat.sum_four_squares` gives existence in Mathlib, the *count* may need assembling).
- Mathlib: group actions (`MulAction`), orbit/stabilizer (`MulAction.orbitEquivQuotientStabilizer`), Burnside-type counting.

### What's Still Open (in this gallery)

- A bound on the number of $B_4$-orbits (distinct representation types) of $n$ in terms of $r_4(n)$ and divisor data.
- The orbit-size accounting (stabilizers for vectors with zero/equal/sign-symmetric entries).

### Our Goal

Formalize the $B_4$ action on four-square solution vectors of $n$, compute orbit sizes via
stabilizers, and derive a bound `numTypes(n) ≤ f(r4 n)` (and ideally an exact orbit count via
Burnside) using Jacobi's total as the weighted sum.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| four-square-distribution | Direct parent; the type decomposition | Jacobi formula, case analysis |
| lagrange-four-squares-waring-g2 | Existence side of four squares | Lagrange, descent |
| burnside / orbit-counting (gallery) | Orbit-counting machinery | group actions, stabilizers |

## Initial Thoughts

### Potential Approaches

1. **Orbit–stabilizer + Burnside (recommended)**: classify stabilizers of solution vectors under
   $B_4$ (free orbits size 384, smaller for vectors with zeros/equal coordinates), then
   $\text{numTypes}=\sum_{\text{orbits}} 1$ with $\sum |\text{orbit}| = r_4(n)$.
   - Why it might work: finite, explicit, fully inside Mathlib's `MulAction` API.
   - Risk: enumerating the stabilizer cases (which coordinates vanish or coincide) is detailed.

2. **Direct divisor bound**: bound numTypes by $r_4(n)/(\text{min orbit size})$ and refine.
   - Why it might work: gives an immediate crude bound to start.
   - Risk: crude unless paired with the stabilizer analysis.

### Key Difficulties

- Correctly accounting for degenerate vectors (zeros, repeated coordinates) where the orbit is smaller than $384$.
- Relating the orbit count to divisor sums cleanly.

### What Would a Proof Need?

- Key lemma 1: orbit sizes of $B_4$ on $\{(x_1,\dots,x_4): \sum x_i^2 = n\}$ by stabilizer type.
- Key lemma 2: Jacobi's exact $r_4(n)$ as the weighted total (or assume it as a hypothesis from the parent).
- Technical requirements: `MulAction`, `orbitEquivQuotientStabilizer`, `Finset.card`, divisor sums.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The question is finite and combinatorial once Jacobi's total is taken as input.
- Mathlib's group-action and orbit–stabilizer API is mature.
- The stabilizer case analysis is the main labor, but bounded and explicit.

**Estimated Effort**:
- Exploration: days
- If tractable: 1–3 weeks
- If hard: 1 month (if Jacobi's exact count must be formalized from scratch)

## References

### Papers
- Jacobi (1834), four-square representation formula.
- Grosswald, *Representations of Integers as Sums of Squares* (1985).

### Online Resources
- Parent gallery entry `four-square-distribution`.

### Mathlib
- `Mathlib.GroupTheory.GroupAction.Basic` — orbits and stabilizers.
- `Mathlib.NumberTheory.SumFourSquares` — four-square existence baseline.

## Metadata

```yaml
tags:
  - number-theory
  - sums-of-squares
  - group-actions
  - orbit-counting
related_proofs:
  - four-square-distribution
  - lagrange-four-squares-waring-g2
difficulty: medium
source: proof-suggestion
created: 2026-06-14
```

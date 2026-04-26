# Problem: Liouville's Theorem: p-adic and Function Field Extensions

**Slug**: liouville-theorem-oq-04
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Can the following p-adic analogue of Liouville's approximation theorem be formalized in Lean 4?

$$
\text{For } \alpha \in \mathbb{Q}_p \text{ algebraic of degree } n \text{ over } \mathbb{Q},\ \exists c > 0 \text{ s.t. } |\alpha - p/q|_p \geq c/q^n \text{ for all } p/q \in \mathbb{Q}
$$

More precisely: formalize Liouville-type lower bounds on p-adic Diophantine approximation
for algebraic numbers, analogous to the archimedean Liouville inequality
`|α - p/q| ≥ c(α) / q^deg(α)`.

### Plain Language

The existing gallery proof establishes Liouville's theorem: algebraic numbers of degree n
cannot be approximated by rationals at rate better than 1/q^n. This shows that Liouville
numbers (approximable at any rate) are transcendental.

The open question asks: does the same structure hold in the p-adic world? The p-adic
absolute value |·|_p gives Q a completely different metric completion. Algebraic numbers
exist in Q_p, and one can ask: are p-adically algebraic numbers "hard to p-adically
approximate" by rationals?

The function field analogue replaces Q with F_q(T) and asks the same question over
function fields — a setting where many number-theoretic results have cleaner analogues.

### Why This Matters

- Connects classical Diophantine approximation to p-adic and non-archimedean geometry
- p-adic Liouville numbers and transcendence in Q_p are active research areas
- Function field analogues often yield cleaner proofs that illuminate the archimedean case
- Lean 4 / Mathlib has growing p-adic infrastructure (`Mathlib.NumberTheory.Padics`)

## Known Results

### What's Already Proven

- **Gallery**: `liouville-theorem` — archimedean Liouville inequality, transcendence of Liouville numbers
- **Mathlib**: `Padic`, `PadicInt`, `padicNorm` — p-adic absolute value and basic properties
- **Mathlib**: `Polynomial.aeval_eq_zero_of_root` and minimal polynomial machinery
- **Classical**: Mahler (1935) classified p-adic transcendence; Koblitz textbook covers p-adic Diophantine approximation

### What's Still Open (in Lean)

- Formalization of the p-adic minimal polynomial lower bound argument
- `padicNorm` interaction with `minpoly` for algebraic elements of Q_p
- A `PadicLiouville` type analogous to the real Liouville numbers
- The function field analogue via `RatFunc F_q`

### Our Goal

Formalize the **p-adic Liouville inequality**: for α algebraic of degree n over Q
embedded in Q_p, there exists c(α) > 0 such that for all p/q ∈ Q,
`padicNorm p (α - p/q) ≥ c / q^n`.

This requires:
1. Embedding Q-algebraic numbers into Q_p
2. Relating the p-adic absolute value to the minimal polynomial evaluation
3. Adapting the archimedean Liouville argument to the non-archimedean setting

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `liouville-theorem` | Parent proof: archimedean case to adapt | Minimal polynomial, product formula |
| `algebraic-numbers-countable` | Algebraic number theory infrastructure | Degree, minimal polynomial |

## Initial Thoughts

### Potential Approaches

1. **Non-archimedean Liouville via minimal polynomial**:
   - Use the fact that for algebraic α, the minimal polynomial P satisfies P(p/q) ≠ 0
   - Bound `|P(p/q)|_p` from below using the integer coefficients
   - Use `|P(α) - P(p/q)|_p = |P(p/q)|_p` (since P(α) = 0)
   - Apply p-adic derivative bound analogous to the archimedean mean value theorem
   - Risk: the non-archimedean MVT has a different form — may need ultrametric tricks

2. **Product formula approach**:
   - Use the product formula `∏_v |x|_v = 1` for x ∈ Q
   - The archimedean place gives a lower bound that constrains p-adic places
   - This might yield a weaker but easier-to-formalize result
   - Risk: product formula setup in Lean/Mathlib may not be developed enough

3. **Function field analogue first**:
   - Work over F_q(T) where tools may be cleaner
   - `RatFunc` in Mathlib provides the scaffolding
   - Risk: less direct connection to the gallery's existing proof

### Key Difficulties

- `Q_p` algebraic closure and embeddings of number fields: Mathlib has `AdicCompletion` but algebraic closure of Q_p is less developed
- The p-adic MVT: in non-archimedean analysis, `|f(a) - f(b)|_p ≤ |a - b|_p · sup|f'|` works but needs formalization
- Precision on what "degree n algebraic over Q" means when embedded in Q_p (all embeddings or one?)

### What Would a Proof Need?

- Key lemma 1: `padicNorm_minpoly_bound`: for P = minpoly ℚ α, `‖P(p/q)‖_p ≥ C / ‖q‖^n`
- Key lemma 2: Non-archimedean analogue of continuity bound on polynomial evaluation
- Technical: Mathlib `Padic.algebraMap` or similar for embedding Q-algebraics into Q_p

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematical argument is well-understood (classical, 1930s-1950s)
- The Lean infrastructure for p-adic algebraic numbers is sparse — this is the main obstacle
- May need to axiomatize the p-adic embedding of algebraic numbers as a stepping stone
- Starting with the function field case (RatFunc) may be more tractable

**Estimated Effort**:
- Exploration: 1-2 days (survey Mathlib p-adic infrastructure)
- If Q_p embedding is available: 3-5 days for the inequality
- If infrastructure missing: weeks (need to build up algebraic closure machinery)

## References

### Papers
- Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions* (1984) — Chapter 4
- Mahler, *Über die Annäherung algebraischer Zahlen durch periodische Algorithmen* (1935)

### Mathlib
- `Mathlib.NumberTheory.Padics.PadicNorm` — p-adic norm, ultrametric inequality
- `Mathlib.NumberTheory.Padics.PadicNumbers` — Q_p as metric completion
- `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` — polynomial tools
- `Mathlib.RingTheory.IntegralClosure` — algebraic elements framework

## Metadata

```yaml
tags:
  - number-theory
  - p-adic
  - diophantine-approximation
  - transcendence
  - function-fields
related_proofs:
  - liouville-theorem
  - algebraic-numbers-countable
difficulty: high
source: gallery-gap
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 4/10

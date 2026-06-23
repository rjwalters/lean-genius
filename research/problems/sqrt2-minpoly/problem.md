# Problem: Minimal Polynomial of √2 over ℚ

**Slug**: sqrt2-minpoly
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{minpoly}(\mathbb{Q}, \sqrt{2}) = X^2 - 2
$$

Equivalently: $X^2 - 2$ is irreducible over $\mathbb{Q}$ and $(\sqrt{2})^2 - 2 = 0$.

In Lean 4 (Mathlib):
```lean
theorem sqrt2_minpoly : Polynomial.minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2 := by sorry
```

### Plain Language

The minimal polynomial of an algebraic number α over a field K is the unique monic irreducible polynomial in K[X] that has α as a root.

For α = √2 over ℚ:
1. **Root verification**: (√2)² - 2 = 2 - 2 = 0, so X²-2 vanishes at √2.
2. **Irreducibility**: X²-2 has no rational roots (±1, ±2 don't satisfy it), so it is irreducible in ℚ[X] by the rational root theorem (degree 2 case).
3. **Minimality**: Therefore X²-2 is the minimal polynomial of √2 over ℚ, and [ℚ(√2):ℚ] = 2.

### Why This Matters

The minimal polynomial is the fundamental algebraic invariant of an algebraic number. This result:
- Establishes that √2 is algebraic of degree 2 over ℚ
- Proves [ℚ(√2):ℚ] = 2, so {1, √2} is a ℚ-basis for ℚ(√2)
- Complements the gallery's `sqrt2-irrational` proof with algebraic structure
- Provides a bridge to `sqrt2-plus-sqrt3-irrational-oq-03` (which proves the degree-4 minpoly of √2+√3)
- Connects to `cayley-hamilton-minpoly` (general minimal polynomial theory)

## Known Results

### What's Already Proven

- `sqrt2-irrational`: √2 is irrational (uses `irrational_sqrt_two` from Mathlib) — gallery
- `Mathlib.Data.Real.Irrational`: `irrational_sqrt_two`, `Nat.Prime.irrational_sqrt` — Mathlib
- `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic`: minimal polynomial API — Mathlib
- `Polynomial.minpoly.irreducible`: minpoly is irreducible over the base field — Mathlib
- `Polynomial.minpoly.eq_X_pow_sub_C_of_isSplittingField`: specialized minpoly computations — Mathlib

### What's Still Open

- Explicit computation: `Polynomial.minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2`
- This connects irrationality (existence of no rational root) to irreducibility (minimal polynomial degree)

### Our Goal

Prove `Polynomial.minpoly ℚ (Real.sqrt 2) = X ^ 2 - C 2` in Lean 4 using Mathlib.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `sqrt2-irrational` | Irrationality of √2; implies no degree-1 rational polynomial vanishes at √2 | `irrational_sqrt_two`, modular arithmetic |
| `sqrt2-plus-sqrt3-irrational-oq-03` | Minpoly of √2+√3 is X⁴-10X²+1 (degree 4 analogue) | `Polynomial.minpoly`, irreducibility |
| `cayley-hamilton-minpoly` | General minimal polynomial theory over fields | `Polynomial.minpoly` API |
| `sqrt2-from-axioms` | Axiomatic construction of √2 | algebraic properties of √2 |

## Initial Thoughts

### Potential Approaches

1. **Direct via `Polynomial.minpoly.eq_of_irreducible`**:
   - Show X²-2 is irreducible over ℚ (rational root theorem / Eisenstein criterion with p=2)
   - Show `aeval (Real.sqrt 2) (X ^ 2 - C 2) = 0` (direct computation)
   - Apply `Polynomial.minpoly.eq_of_irreducible_of_monic`
   - Why it might work: Mathlib has this API path
   - Risk: Need correct lemma names; `Real.sq_sqrt` should give (√2)² = 2

2. **Eisenstein criterion**:
   - X²-2 is Eisenstein at p=2: 2|(-2) and 2∤1 (leading coeff) and 4∤(-2)
   - Mathlib has `Polynomial.Irreducible.of_eisenstein_criterion`
   - Why it might work: Clean, well-supported path
   - Risk: Need to verify Eisenstein API exists for ℤ and then lift to ℚ

3. **Via degree argument**:
   - √2 is algebraic of degree ≥ 2 (irrational means degree > 1)
   - X²-2 annihilates √2, so degree ≤ 2
   - Therefore degree = 2 and X²-2 is the minpoly
   - Why it might work: Conceptually clear
   - Risk: Need to formalize "degree exactly 2" argument

### Key Difficulties

- Connecting `Real.sqrt 2` (analysis) to `Polynomial.minpoly ℚ` (algebra) requires coercion infrastructure
- `Real.sqrt 2` is defined analytically; algebraic properties need `Real.sq_sqrt`, `Real.sqrt_nonneg`
- Verifying `aeval (Real.sqrt 2) (X ^ 2 - C 2) = 0` requires `Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)`

### What Would a Proof Need?

- `Real.sq_sqrt`: (√x)² = x for x ≥ 0
- `Polynomial.minpoly.eq_of_irreducible_of_monic` or similar API
- Irreducibility of X²-2 over ℚ: either by Eisenstein or rational root theorem
- `Polynomial.Monic` for X²-2
- Cast from ℚ to ℝ for evaluation

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The mathematics is completely determined: X²-2, irreducibility via Eisenstein (p=2)
- Mathlib has `Polynomial.minpoly` API, `Real.sq_sqrt`, and `irrational_sqrt_two`
- The analogous proof for √2+√3 (`sqrt2-plus-sqrt3-irrational-oq-03`) is the harder version
- Degree 2 case is simpler than degree 4

**Estimated Effort**:
- Exploration: 1-2 hours to find correct API calls
- If tractable: 1 session (high confidence)
- Fallback: axiomatize with Eisenstein manually proven in ℤ, lifted to ℚ

## References

### Mathlib
- `Mathlib.RingTheory.Polynomial.Basic` — `Polynomial.minpoly` definitions and API
- `Mathlib.Data.Real.Sqrt` — `Real.sqrt`, `Real.sq_sqrt`
- `Mathlib.Data.Real.Irrational` — `irrational_sqrt_two`
- `Mathlib.RingTheory.Polynomial.Cyclotomic.Irreducible` — irreducibility tools
- `Mathlib.RingTheory.Eisenstein.Basic` — Eisenstein criterion

## Metadata

```yaml
tags:
  - algebraic-number-theory
  - minimal-polynomial
  - sqrt2
  - irrationality
  - irreducibility
related_proofs:
  - sqrt2-irrational
  - sqrt2-plus-sqrt3-irrational
  - cayley-hamilton-minpoly
difficulty: low
source: gallery-gap
created: 2026-04-22
```

**Significance**: 6/10
**Tractability**: 8/10

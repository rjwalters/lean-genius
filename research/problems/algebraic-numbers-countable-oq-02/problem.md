# Problem: ℝ Uncountability via Cantor Diagonal Argument

**Slug**: algebraic-numbers-countable-oq-02
**Created**: 2026-04-04T20:56:00-07:00
**Status**: Active
**Source**: gallery-gap
**Tier**: B | **Significance**: 7/10 | **Tractability**: 7/10

## Problem Statement

### Formal Statement

$$
\neg \exists f : \mathbb{N} \to \mathbb{R},\ \text{Surjective}(f)
$$

Equivalently: prove `¬ Countable (Set.univ : Set ℝ)` in Lean 4, or show
`Cardinal.mk ℝ > Cardinal.aleph0`.

### Plain Language

Prove in Lean 4 that ℝ is uncountable, completing Cantor's 1874 paper alongside
the parent proof that the algebraic numbers are countable. The parent proof shows
|Algebraic| = ℵ₀; this problem provides the complementary result |ℝ| > ℵ₀,
establishing that transcendental numbers exist (and dominate).

### Why This Matters

Together with the countability of algebraic numbers, this closes Cantor's original
argument that "most" real numbers are transcendental. The diagonal argument is a
cornerstone of set theory and computability. Formalizing it exercises Lean's
cardinal arithmetic and `Classical.choice`/`Finset` machinery. Mathlib already
contains infrastructure (e.g., `Cardinal.not_countable_real`), but a self-contained
pedagogical proof would strengthen the gallery entry significantly.

## Known Results

### What's Already Proven

- `algebraic-numbers-countable`: algebraic numbers form a countable set (|𝔸| = ℵ₀)
- Cantor's theorem (Mathlib): for any set S, `Cardinal.mk S < Cardinal.mk (Set S)`
- `Cardinal.mk_real`: Mathlib has `Cardinal.mk ℝ = 2 ^ Cardinal.aleph0`
- Schroeder-Bernstein theorem: available in Mathlib

### What's Still Open

- A clean, self-contained Lean 4 diagonal argument for ℝ uncountability in gallery
- Making the proof explicit enough to be pedagogically useful

### Our Goal

Prove `¬ Countable (Set.univ : Set ℝ)` or equivalently show no surjection ℕ → ℝ
exists, ideally via an explicit diagonal construction that is readable and educational.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| algebraic-numbers-countable | Parent proof; countability of algebraic numbers | Cardinal arithmetic, Finset |
| cantor-diagonalization | Cantor's general diagonal argument formalized | Diagonal construction |

## Initial Thoughts

### Potential Approaches

1. **Via Cardinal Arithmetic (short path)**: Use Mathlib's `Cardinal.mk_real = 2 ^ aleph0 > aleph0`
   - Why it might work: Mathlib has this already; could be a clean one-liner
   - Risk: Trivial if Mathlib exports the right lemma; not pedagogically deep

2. **Direct Diagonal Argument**: Given any f : ℕ → ℝ, construct x : ℝ with
   x ≠ f(n) for all n via decimal digit manipulation (Cantor's original method).
   - Why it might work: Standard argument, well-understood, educational
   - Risk: Decimal digit manipulation requires care with 9-periodicity

3. **Via Baire Category**: ℝ is a complete metric space with no isolated points →
   not countable (Baire Category Theorem).
   - Why it might work: Avoids explicit diagonalization; uses topology
   - Risk: Heavier imports; less direct connection to Cantor's original proof

### Key Difficulties

- Lean's real number representation: reals defined via Cauchy sequences; extracting
  "digits" for diagonal argument requires care
- The 9-periodicity issue: 0.999... = 1.000... means naive digit diagonal fails

### What Would a Proof Need?

- Key lemma 1: Existence of uncountable interval `Set.Icc 0 1`
- Key lemma 2: `not_countable_Icc` or injection from [0,1] → ℝ
- Technical: Mathlib's `Real` definition and `Cardinal` namespace

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Mathlib almost certainly has `Cardinal.mk_real` or equivalent — check first
- Even the constructive diagonal argument is well-documented in formalization literature
- The parent proof already navigates the required cardinal arithmetic machinery
- Multiple fallback approaches available if one is blocked

**Estimated Effort**:
- Exploration (OBSERVE): 1 session to find Mathlib lemmas
- If Mathlib has `not_countable_real`: trivial wrapper (hours)
- Direct diagonal construction from scratch: 2-4 sessions

## References

### Papers
- Cantor, G. (1874). "Über eine Eigenschaft des Inbegriffes aller reellen algebraischen Zahlen"

### Mathlib
- `Mathlib.SetTheory.Cardinal.Basic` — Cardinal arithmetic
- `Mathlib.Data.Real.Basic` — Real number definition
- `Mathlib.Topology.Baire.Basic` — Baire category (alternative approach)
- Search for: `Cardinal.not_countable_real`, `Real.not_countable`, `Cardinal.mk_real`

## Metadata

```yaml
tags:
  - set-theory
  - real-analysis
  - countability
  - cantor-diagonal
  - cardinal-arithmetic
related_proofs:
  - algebraic-numbers-countable
  - cantor-diagonalization
difficulty: low-medium
source: gallery-gap
created: 2026-04-04T20:56:00-07:00
```

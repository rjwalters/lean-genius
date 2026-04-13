# Problem: Fermat's Theorem on Sums of Two Squares

**Slug**: infinitude-primes-4k1-oq-01
**Created**: 2026-04-12T14:53:27-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
p \text{ is an odd prime} \implies \bigl(p \equiv 1 \pmod{4} \iff \exists\, a\, b \in \mathbb{N},\; p = a^2 + b^2\bigr)
$$

### Plain Language

Fermat's theorem on sums of two squares states that an odd prime $p$ can be written as a sum of two perfect squares if and only if $p \equiv 1 \pmod{4}$. This is one of the most elegant characterizations in elementary number theory.

The existing gallery proof (`infinitude-primes-4k1`) already uses the forward direction implicitly — via Mathlib's `mod_four_ne_three_of_dvd_isSquare_neg_one` — to show there are infinitely many such primes. The open question asks: can we formalize the full equivalence as a standalone theorem using `Mathlib.NumberTheory.SumTwoSquares`?

### Why This Matters

- Fermat's two-squares theorem is a cornerstone result connecting quadratic residues, Gaussian integers, and prime decomposition
- The gallery already has the infinitude proof that depends on one direction; making the full characterization explicit adds significant mathematical depth
- Mathlib likely has the pieces (`Nat.Prime.sq_add_sq` or similar) — the question is how cleanly we can assemble them

## Known Results

### What's Already Proven

- `InfinitudePrimes4k1.lean`: Infinitely many primes ≡ 1 (mod 4), using `mod_four_ne_three_of_dvd_isSquare_neg_one` — `proofs/Proofs/InfinitudePrimes4k1.lean`
- `Mathlib.NumberTheory.SumTwoSquares`: Contains Nat.Prime representations as sums of two squares
- `ZMod.isSquare_neg_one_iff`: Characterization of when -1 is a quadratic residue

### What's Still Open

- Full formalization of the biconditional: p ≡ 1 (mod 4) ⟺ p = a² + b²
- Connection to Gaussian integer factorization (p splits in ℤ[i] iff p ≡ 1 mod 4)
- Explicit witness extraction: given p ≡ 1 (mod 4), compute (a, b)

### Our Goal

Formalize the complete Fermat two-squares characterization as a Lean theorem, connecting it to the existing infinitude proof as a strengthening. The result should cleanly state the biconditional and leverage Mathlib's infrastructure rather than rebuilding from scratch.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| infinitude-primes-4k1 | Source proof, uses one direction | Euler's criterion, ZMod, factorial construction |
| pythagorean-theorem | Sum of squares context | Inner product geometry |
| fundamental-theorem-arithmetic | Prime factorization | Nat.Prime, Unique factorization |
| quadratic-reciprocity (if exists) | Quadratic residues | Legendre symbol |

## Initial Thoughts

### Potential Approaches

1. **Direct Mathlib wrapper**: Check if `Mathlib.NumberTheory.SumTwoSquares` already contains `Nat.Prime.sq_add_sq` or equivalent, and write a clean pedagogical wrapper
   - Why it might work: Mathlib is comprehensive for classical number theory
   - Risk: The API may not expose the biconditional directly

2. **Gaussian integers path**: Factor p in ℤ[i]. If p ≡ 1 (mod 4), then p = (a + bi)(a - bi) = a² + b². Use `Mathlib.NumberTheory.Zsqrtd` or `GaussianInt`
   - Why it might work: Conceptually clean and connects to algebraic number theory
   - Risk: Gaussian integer infrastructure may have gaps

3. **Descent argument**: Fermat's original proof via infinite descent — if p ≡ 1 mod 4, find x with x² ≡ -1 mod p, then use the descent to reduce x² + 1 = mp to m = 1
   - Why it might work: Elementary, no heavy machinery
   - Risk: Descent proofs can be tricky in Lean

### Key Difficulties

- Identifying which Mathlib theorems give the biconditional most directly
- The "only if" direction (p = a² + b² implies p ≡ 1 mod 4) is easy: squares mod 4 are 0 or 1, so a² + b² mod 4 ∈ {0, 1, 2}
- The "if" direction (p ≡ 1 mod 4 implies p = a² + b²) is the deep part

### What Would a Proof Need?

- Key lemma 1: If p ≡ 3 (mod 4), then p cannot be a sum of two squares
- Key lemma 2: If p ≡ 1 (mod 4), then p is a sum of two squares (the hard direction)
- Technical: Navigate Mathlib's SumTwoSquares API, possibly GaussianInt

## Tractability Assessment

**Difficulty**: Low to Medium

**Justification**:
- Mathlib explicitly imports `NumberTheory.SumTwoSquares` in the existing proof
- The result is classical and well-known — Mathlib almost certainly has it
- The main work is finding the right API and writing clean wrappers
- The "if" direction may already be `Nat.Prime.sq_add_sq` or similar

**Estimated Effort**:
- Exploration: 1-2 hours (survey Mathlib's SumTwoSquares)
- If Mathlib has it: 2-4 hours (write clean formalization)
- If Mathlib gaps exist: 1-2 days (fill in supporting lemmas)

## References

### Papers
- Fermat, letter to Mersenne, 1640 — original claim (no proof published)
- Euler, 1749 — first published proof
- Zagier, "A one-sentence proof", American Mathematical Monthly, 1990 — famous elegant proof

### Mathlib
- `Mathlib.NumberTheory.SumTwoSquares` — key infrastructure
- `Mathlib.NumberTheory.Zsqrtd.GaussianInt` — Gaussian integers
- `Mathlib.Data.ZMod.Basic` — modular arithmetic
- `Mathlib.NumberTheory.LegendreSymbol` — quadratic residues

## Metadata

```yaml
tags:
  - number-theory
  - quadratic-residues
  - sums-of-squares
  - primes
related_proofs:
  - infinitude-primes-4k1
  - fundamental-theorem-arithmetic
  - pythagorean-theorem
difficulty: low-medium
source: gallery-gap
created: 2026-04-12T14:53:27-07:00
```

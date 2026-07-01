# Problem: Sum of Two Squares for All Naturals — the Prime-Factorization Criterion

**Slug**: fermat-two-squares-oq-08
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: fermat-two-squares

## Problem Statement

### Formal Statement

$$
n = x^2 + y^2 \ \text{ for some } x,y \in \mathbb{N}
\iff \forall\, q \mid n,\ q \equiv 3 \pmod 4 \Rightarrow 2 \mid \nu_q(n)
$$

### Plain Language

A natural number $n$ is a sum of two squares iff, in its prime factorization, every prime
$q \equiv 3 \pmod 4$ occurs to an even power. This promotes Fermat's prime-only theorem
($p$ is a sum of two squares iff $p \ne 3 \bmod 4$) to the full multiplicative
characterization for **every** natural number. Examples: $45 = 3^2\cdot 5 = 6^2 + 3^2$
is representable (the 3-mod-4 prime 3 has even exponent 2), while $21 = 3\cdot 7$ is not
(both 3 and 7 are $\equiv 3 \bmod 4$ with odd exponent 1).

### Why This Matters

This is exactly the parent's stated open question: the composite/all-naturals
characterization. No sibling states it — oq-05 proves only the necessary mod-4 obstruction
for a single residue, oq-04 counts representations via the Jacobi divisor-character sum,
and oq-06/oq-07 formalize the Brahmagupta multiplicativity identities but not the
factorization criterion. It rests on the multiplicativity of the norm form plus the prime
case, both already in the gallery/Mathlib.

## Known Results

### What's Already Proven

- Parent entry `fermat-two-squares` is verified (0-axiom).
- Mathlib contains the exact biconditional `Nat.eq_sq_add_sq_iff`, plus
  `Nat.Prime.sq_add_sq`, `Nat.sq_add_sq_mul` (Brahmagupta–Fibonacci), and a `Decidable`
  instance for `∃ x y, n = x^2 + y^2`.

### What's Still Open

- The headline below (currently `sorry`) and its worked corollaries.

### Our Goal

Prove the sketch below as a verified (0-axiom) child of `fermat-two-squares`.
Category: **generalization**.

## Target Lean Sketch

```lean
theorem sum_two_squares_iff_even_padicVal (n : ℕ) :
    (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔
      ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) := by
  sorry -- exact Nat.eq_sq_add_sq_iff (modulo namespace/statement shape)

-- worked corollaries, closed by `decide` via the Mathlib Decidable instance:
example : ∃ x y : ℕ, 45 = x ^ 2 + y ^ 2 := by decide   -- 6² + 3²
example : ¬ ∃ x y : ℕ, 21 = x ^ 2 + y ^ 2 := by decide  -- 3·7, both 3 mod 4
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `fermat-two-squares` | Parent: prime p ≡ 1 mod 4 ⇒ p = x²+y² | descent / ZMod |
| `fermat-two-squares-oq-05` | Sibling: mod-4 obstruction (necessity only) | ZMod 4 |
| `fermat-two-squares-oq-06` | Sibling: Brahmagupta multiplicativity | norm identity |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 7/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The headline is essentially `Nat.eq_sq_add_sq_iff`; the value of the
entry is in wrapping it with a pedagogical framing (prime case as a special case) and
concrete `decide`-checked worked examples using the Mathlib decidability instance.

### Suggested First Steps

1. Prove the headline via `Nat.eq_sq_add_sq_iff`, wrapping it with a docstring tying it to
   the parent prime case.
2. Add worked corollaries closed by `decide`: 45, 50 representable; 21, 33 not.
3. Optionally expose the squarefree-part form `Nat.eq_sq_add_sq_iff_eq_sq_mul` and connect
   $-1$'s squareness to `ZMod.exists_sq_eq_neg_one_iff` for a second proof route.

## References

### Mathlib

- `Nat.eq_sq_add_sq_iff` — NumberTheory/SumTwoSquares.lean (the exact biconditional)
- `Nat.eq_sq_add_sq_iff_eq_sq_mul` — NumberTheory/SumTwoSquares.lean
- `Nat.Prime.sq_add_sq` — NumberTheory/SumTwoSquares.lean (parent prime case)
- `Nat.sq_add_sq_mul` — NumberTheory/SumTwoSquares.lean (Brahmagupta–Fibonacci over ℕ)
- `ZMod.exists_sq_eq_neg_one_iff` — NumberTheory/LegendreSymbol/Basic.lean
- `Decidable (∃ x y, n = x ^ 2 + y ^ 2)` instance — NumberTheory/SumTwoSquares.lean

## Metadata

```yaml
tags:
  - number-theory
  - sum-of-two-squares
  - prime-factorization
  - fermat
  - gaussian-integers
related_proofs:
  - fermat-two-squares
  - fermat-two-squares-oq-05
  - fermat-two-squares-oq-06
difficulty: low
source: proof-suggestion
created: 2026-07-01
```

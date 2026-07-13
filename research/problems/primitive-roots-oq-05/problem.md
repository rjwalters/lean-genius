# Problem: Lifting a Primitive Root from p to p² (Hensel Step for the Multiplicative Group)

**Slug**: primitive-roots-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: primitive-roots

## Problem Statement

### Formal Statement

Let $p$ be an odd prime and let $g$ be a primitive root modulo $p$, i.e.
$\operatorname{ord}_p(g)=p-1$. Then either $g$ (lifted to $(\mathbb Z/p^2\mathbb Z)^\times$)
is a primitive root modulo $p^2$, or $g+p$ is; equivalently, at least one of $g,\,g+p$ has
multiplicative order $p(p-1)=\varphi(p^2)$ in $(\mathbb Z/p^2\mathbb Z)^\times$. Consequently
$(\mathbb Z/p^2\mathbb Z)^\times$ has a primitive root that reduces to $g$ mod $p$.

### Plain Language

The parent entry `primitive-roots` establishes that $(\mathbb Z/p\mathbb Z)^\times$ is
cyclic — a primitive root mod $p$ exists. This child takes the **first Hensel-style lifting
step**: given a primitive root $g$ mod $p$, it produces a primitive root mod $p^2$ explicitly
from $g$. The order of $g$ mod $p^2$ is a multiple of $p-1$ dividing $p(p-1)$, so it is either
$p-1$ or $p(p-1)$; if it is only $p-1$ (the "defective" case), replacing $g$ by $g+p$ bumps
the order up to $p(p-1)$. This is the inductive engine behind the classical theorem that
$(\mathbb Z/p^k\mathbb Z)^\times$ is cyclic for odd $p$.

### Why This Matters

Mathlib knows that $(\mathbb Z/p^k\mathbb Z)^\times$ is cyclic (`ZMod.isCyclic_units_...`), but
that existence statement is **non-constructive** about the generator: it does not tell you how
a chosen primitive root mod $p$ lifts, nor that `g` or `g+p` works. Making the lift explicit
is exactly the content of the standard proof and requires assembling order-divisibility facts
with the group-order count $\varphi(p^2)=p(p-1)$ — no single lemma delivers it.

## Known Results

### What's Already Proven

- Parent `primitive-roots` is verified (0-axiom): $(\mathbb Z/p\mathbb Z)^\times$ is cyclic.
- Mathlib: `ZMod.card_units_eq_totient` (order of the unit group is `φ n`),
  `Nat.totient_prime_pow` (`φ(p^2) = p*(p-1)` for odd prime `p`), `orderOf_dvd_card`,
  `orderOf_dvd_of_pow_eq_one`, `ZMod.unitsMap` (reduction `(ZMod p²)ˣ → (ZMod p)ˣ`).

### What's Still Open

- The lifting theorem below (currently `sorry`). Mathlib provides cyclicity but not the
  explicit `g`-or-`g+p` generator lift.

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**number theory / constructive completion**.

## Target Lean Sketch

```lean
open ZMod

/-- Order of a lift divides `φ(p²)=p(p-1)` and is a multiple of `p-1`. -/
theorem orderOf_lift_between (p : ℕ) [hp : Fact p.Prime] (hodd : p ≠ 2)
    (u : (ZMod (p^2))ˣ) (hg : orderOf (unitsMap (dvd_pow_self p (by norm_num)) u) = p - 1) :
    orderOf u = p - 1 ∨ orderOf u = p * (p - 1) := by
  sorry
  -- `orderOf u ∣ φ(p²) = p*(p-1)` (orderOf_dvd_card + card_units_eq_totient + totient_prime_pow);
  -- `(p-1) ∣ orderOf u` because the reduction has order `p-1` and reduction is a hom
  -- (orderOf_map_dvd / orderOf image divides preimage). The only divisors of p(p-1) that are
  -- multiples of (p-1) are (p-1) and p(p-1) since gcd(p, p-1)=1 and p is prime.

/-- Existence of a primitive root mod p² lifting a given primitive root mod p. -/
theorem exists_primitiveRoot_lift (p : ℕ) [hp : Fact p.Prime] (hodd : p ≠ 2)
    (g : (ZMod p)ˣ) (hg : orderOf g = p - 1) :
    ∃ u : (ZMod (p^2))ˣ, orderOf u = p * (p - 1)
      ∧ unitsMap (dvd_pow_self p (by norm_num)) u = g := by
  sorry
  -- Take any lift `u₀` of `g` (unitsMap is surjective). By the previous lemma its order is
  -- (p-1) or p(p-1). If p(p-1), done. If (p-1), show `u₀ * (1 + p)` (equivalently `g+p`)
  -- has order p(p-1): `(1+p)` has order exactly `p` in (ZMod p²)ˣ, and gcd(p, p-1)=1 makes
  -- the orders multiply (Commute.orderOf_mul_eq for coprime orders).
```

Add worked `example`s: `p = 5, g = 2` (order `4` mod 5; check `2` is a primitive root mod 25
since `2^4 = 16 ≠ 1 mod 25`); `p = 7, g = 3`; and the classic defective base `p = 3`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `primitive-roots` | Parent: `(ℤ/pℤ)ˣ` is cyclic | group theory, finite fields |
| `euler-totient` | `φ(p^k)` formula and multiplicativity | number theory |
| `wilsons-theorem` | Structure of `(ℤ/nℤ)ˣ` | modular arithmetic |

## Tractability Assessment

**Difficulty**: Medium

**Significance**: 7/10  |  **Tractability**: 7/10  |  **Tier**: B

**Justification**: Pure order arithmetic in a finite abelian group. The two nontrivial inputs
— `(1+p)` has order `p` mod `p²`, and coprime orders multiply — are both standard and present
in Mathlib. The divisor case-analysis is `omega`/`Nat.Coprime`-friendly.

### Suggested First Steps

1. Establish `φ(p²) = p(p-1)` via `Nat.totient_prime_pow` and `ZMod.card_units_eq_totient`.
2. Prove `orderOf_lift_between` from `orderOf_dvd_card` plus the reduction-hom order fact.
3. Prove `(1 + p : (ZMod p²)ˣ)` has order `p`; combine coprime orders with
   `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` (or the analogous Mathlib name).

## References

### Mathlib

- `ZMod.card_units_eq_totient` — Data/ZMod/Basic.lean
- `Nat.totient_prime_pow` — Data/Nat/Totient.lean
- `orderOf_dvd_card`, `orderOf_dvd_of_pow_eq_one` — GroupTheory/OrderOfElement.lean
- `ZMod.unitsMap` — Data/ZMod/Basic.lean

### Literature

- Ireland & Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 4 (primitive roots
  mod `p^k`); the `g`-or-`g+p` lifting dichotomy is the standard proof.

## Metadata

```yaml
tags:
  - number-theory
  - primitive-roots
  - group-theory
  - hensel-lifting
related_proofs:
  - primitive-roots
  - euler-totient
  - wilsons-theorem
difficulty: medium
source: proof-suggestion
created: 2026-07-01
```

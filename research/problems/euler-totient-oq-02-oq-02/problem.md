# Problem: Euler's Theorem via the Group (ℤ/nℤ)*

**Slug**: euler-totient-oq-02-oq-02
**Created**: 2026-07-01T08:49:18-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\gcd(a,n) = 1 \implies a^{\varphi(n)} \equiv 1 \pmod{n}
$$

where $\varphi$ is Euler's totient function and $\varphi(n) = |(\mathbb{Z}/n\mathbb{Z})^\times|$.

### Plain Language

For any modulus $n$ and any integer $a$ coprime to $n$, raising $a$ to the power $\varphi(n)$ leaves remainder $1$ upon division by $n$. This generalizes Fermat's little theorem (the case $n$ prime, where $\varphi(p) = p-1$).

### Why This Matters

Euler's theorem is the arithmetic backbone of RSA correctness: decryption works precisely because $m^{ed} \equiv m \pmod{n}$ follows from $ed \equiv 1 \pmod{\varphi(n)}$. It is the canonical bridge between elementary number theory and group theory, exhibiting a congruence identity as Lagrange's theorem applied to the unit group $(\mathbb{Z}/n\mathbb{Z})^\times$.

## Known Results

### What's Already Proven

- Fermat's little theorem — standard, related gallery entries exist.
- Lagrange's theorem (order of element divides group order) — Mathlib `orderOf_dvd_card`.
- Mathlib provides `ZMod.pow_totient` and `Nat.ModEq.pow_totient` directly stating this result.

### What's Still Open

- Present a self-contained gallery derivation of `a^φ(n) ≡ 1 (mod n)` from the group-order interpretation `φ(n) = |(ℤ/nℤ)*|`, rather than invoking the packaged Mathlib lemma as a black box.
- Connect the totient's multiplicativity (parent entry) to the group-cardinality reading via CRT.

### Our Goal

Formalize Euler's theorem for a general modulus, deriving it from Lagrange's theorem on `(ZMod n)ˣ` and exhibiting `φ(n) = |(ZMod n)ˣ|` as the structural fact that powers the congruence. Confirm the RSA-relevant corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-totient-oq-02 | Parent: multiplicativity of φ | CRT, multiplicative functions |
| lagrange-theorem | Order divides group cardinality | coset counting |
| wilsons-theorem | Structure of the unit group mod n | group theory in ZMod |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Work in `(ZMod n)ˣ`. Map `a` to a unit via `gcd(a,n)=1`, apply `pow_card_eq_one` / `orderOf_dvd_card`, then transport back to a congruence in `ℤ`.
   - Why it might work: Mathlib's unit-group API and `ZMod.card_units_eq_totient` give `φ(n) = |(ZMod n)ˣ|` outright.
   - Risk: bookkeeping in moving between `ℤ`, `ZMod n`, and `(ZMod n)ˣ`.

2. **Approach B**: Cite `ZMod.pow_totient` but wrap it with a demonstrated derivation of `card_units_eq_totient` from Lagrange, so the gallery entry shows the group-theoretic content.
   - Why it might work: minimal, robust against Mathlib drift.
   - Risk: reads as a thin wrapper unless the Lagrange step is made explicit.

### Key Difficulties

- Cleanly converting `gcd(a,n)=1` into membership in `(ZMod n)ˣ` and back.
- Presenting genuine mathematical content beyond a one-line Mathlib call.

### What Would a Proof Need?

- Key lemma 1: `φ(n) = |(ZMod n)ˣ|` (`ZMod.card_units_eq_totient`).
- Key lemma 2: Lagrange — every unit `u` satisfies `u ^ |(ZMod n)ˣ| = 1`.
- Technical requirements: `IsUnit` / `ZMod.unitOfCoprime`, `Nat.ModEq` transport.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Mathlib contains all the needed lemmas (`ZMod.pow_totient`, `ZMod.card_units_eq_totient`, `pow_card_eq_one`).
- Similar unit-group congruence entries (Wilson's theorem) are already in the gallery.
- The challenge is presentation, not mathematical obstruction.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 1–2 days
- If hard: n/a

## References

### Papers
- Euler, "Theoremata arithmetica nova methodo demonstrata" (1763) — original.

### Online Resources
- https://en.wikipedia.org/wiki/Euler%27s_theorem — statement and proofs.

### Mathlib
- `Mathlib.Data.ZMod.Basic` — `ZMod.pow_totient`, `ZMod.card_units_eq_totient`, `ZMod.unitOfCoprime`.

## Metadata

```yaml
tags:
  - number-theory
  - group-theory
  - modular-arithmetic
related_proofs:
  - euler-totient-oq-02
  - lagrange-theorem
difficulty: low
source: gallery-gap
created: 2026-07-01T08:49:18-07:00
```

**Significance**: 6/10
**Tractability**: 8/10

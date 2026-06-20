# Problem: Euler's Theorem — a^φ(n) ≡ 1 (mod n) for gcd(a,n)=1

**Slug**: euler-totient-oq-05
**Created**: 2026-06-19T22:27:34-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\gcd(a,n)=1 \;\Longrightarrow\; a^{\varphi(n)} \equiv 1 \pmod{n},
$$

with the exponent-reduction corollary
$$
\gcd(a,n)=1 \;\Longrightarrow\; a^{k} \equiv a^{\,k \bmod \varphi(n)} \pmod{n}.
$$

### Plain Language

Euler's theorem says that whenever $a$ and $n$ are coprime, raising $a$ to the
power $\varphi(n)$ (Euler's totient — the count of integers in $[1,n]$ coprime
to $n$) gives $1$ modulo $n$. It generalizes Fermat's little theorem
($a^{p-1} \equiv 1 \pmod p$ for prime $p$, where $\varphi(p) = p-1$) to arbitrary
moduli. A direct consequence is that exponents of coprime bases can be reduced
modulo $\varphi(n)$ when computing powers mod $n$.

### Why This Matters

- It is the engine behind RSA decryption and a cornerstone of computational
  number theory and modular exponentiation.
- It is distinct from the existing gallery entry oq-01, which formalizes the
  finer **Carmichael function** statement $a^{\lambda(n)} \equiv 1$; the present
  problem targets the classical $\varphi$-exponent theorem and its
  exponent-reduction corollary, which the gallery does not yet state directly.
- It sits structurally between Lagrange's theorem ($g^{|G|}=1$ in the unit group
  $(\mathbb{Z}/n)^\times$, of order $\varphi(n)$) and Fermat's little theorem.

## Known Results

### What's Already Proven

- Euler's theorem (ModEq form): `Nat.ModEq.pow_totient (h : a.Coprime n) : a ^ n.totient ≡ 1 [MOD n]` — Mathlib `Mathlib/NumberTheory/PowModTotient.lean` / `Mathlib/FieldTheory/Finite/Basic.lean`.
- Exponent reduction: `Nat.pow_totient_mod_eq_one`, `Nat.pow_add_totient_mod_eq`, `Nat.pow_totient_mod` — `Mathlib/NumberTheory/PowModTotient.lean`.
- Group-of-units route: `pow_card_eq_one` on `(ZMod n)ˣ` (order `φ(n)`, via `ZMod.card_units_eq_totient`).

### What's Still Open

- Nothing mathematically open; this is a formalization-coverage gap.
- Optional: phrase both the ℕ `ModEq` version and the `(ZMod n)ˣ` group version and show they agree.

### Our Goal

A self-contained, axiom-free Lean entry proving `a^φ(n) ≡ 1 (mod n)` for coprime
`a`, plus the exponent-reduction corollary, framed via `φ` (not `λ`) to remain
distinct from the Carmichael entry oq-01.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-totient-oq-01 | Carmichael-λ refinement of this result | `ZMod`, group order |
| lagrange-theorem-oq-07 | g^\|G\|=1 specializes to units group of order φ(n) | `pow_card_eq_one` |
| wilsons-theorem-oq-05 | Companion `ZMod` modular-arithmetic result | `ZMod`, units |

## Initial Thoughts

### Potential Approaches

1. **Direct ModEq**: close the main goal with `Nat.ModEq.pow_totient` and the
   corollary with `Nat.pow_add_totient_mod_eq`.
   - Why it might work: exact named lemmas exist.
   - Risk: minimal; mind `Nat.Coprime` orientation `a.Coprime n`.

2. **Units-group derivation**: work in `(ZMod n)ˣ`, apply `pow_card_eq_one`
   (order = `ZMod.card_units_eq_totient`), then transport back to `ℕ` ModEq.
   - Why it might work: exposes the Lagrange-corollary structure.
   - Risk: cast/transport bookkeeping between `ℕ`, `ZMod n`, and `(ZMod n)ˣ`.

### Key Difficulties

- Coprimality orientation and the `1 < n` side condition for the `% n` form.
- Keeping the statement clearly distinct from the Carmichael-λ entry.

### What Would a Proof Need?

- Key lemma 1: `Nat.ModEq.pow_totient`.
- Key lemma 2: `Nat.pow_add_totient_mod_eq` (exponent reduction).
- Technical requirements: `import Mathlib`, `Nat.Coprime`, `Nat.totient`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Euler's theorem and its reduction corollaries are named Mathlib lemmas.
- Comparable one/two-lemma gallery entries ship axiom-free verified.
- All infrastructure (`Nat.totient`, `ZMod`, units group) is in Mathlib.

**Estimated Effort**:
- Exploration: ~1 hour
- If tractable: under a day
- If hard: n/a

## References

### Papers
- L. Euler (1763), *Theoremata arithmetica nova methodo demonstrata*.

### Online Resources
- https://en.wikipedia.org/wiki/Euler%27s_theorem — statement, proof, RSA application.

### Mathlib
- `Mathlib/NumberTheory/PowModTotient.lean` — `pow_totient_mod_eq_one`, `pow_add_totient_mod_eq`.
- `Mathlib/FieldTheory/Finite/Basic.lean` — `Nat.ModEq.pow_totient`.

## Metadata

```yaml
tags:
  - number-theory
  - euler-totient
  - modular-arithmetic
  - fermat-little-theorem
related_proofs:
  - euler-totient-oq-01
  - lagrange-theorem-oq-07
difficulty: low
source: gallery-gap
created: 2026-06-19T22:27:34-07:00
```

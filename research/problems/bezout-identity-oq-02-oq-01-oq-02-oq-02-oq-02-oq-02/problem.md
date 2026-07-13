# Problem: p = a² + n·b² for imaginary quadratic fields via ZMod decidability

**Slug**: bezout-identity-oq-02-oq-01-oq-02-oq-02-oq-02-oq-02
**Created**: 2026-07-01
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For a prime } p \nmid 2n,\quad p = a^2 + n\,b^2 \text{ for some } a,b \in \mathbb{Z}
\iff \left(\tfrac{-n}{p}\right) = 1 \ \wedge\ p \text{ splits with a principal ideal in } \mathbb{Z}[\sqrt{-n}].
$$

Concretely, prove the classical cases: $p = a^2 + 2b^2 \iff p \equiv 1,3 \pmod 8$ and $p = a^2 + 3b^2 \iff p = 3 \text{ or } p \equiv 1 \pmod 3$.

### Plain Language

The parent line proved Fermat's two-squares theorem ($p = a^2 + b^2 \iff p \equiv 1 \pmod 4$) using a `ZMod`-decidability technique to certify the residue condition. This problem asks whether the same technique generalizes to $p = a^2 + n b^2$ for other small $n$, corresponding to the imaginary quadratic rings $\mathbb{Z}[\sqrt{-n}]$ that are still norm-Euclidean / class number one ($n = 1, 2, 3, 4, 7$).

### Why This Matters

The $a^2 + n b^2$ representability problem (subject of Cox's book of the same name) is the gateway from Fermat's theorem to class field theory. Formalizing the class-number-one cases with a uniform, decidable residue certificate is a natural and self-contained extension of the two-squares result already in the gallery.

### What's Already Proven

- Fermat two squares $p = a^2 + b^2 \iff p \equiv 1 \pmod 4$ (parent), via `ZMod p` decidability.
- The descent / Thue-lemma machinery for the $n = 1$ case (parent line).

### What's Still Open

- The $n = 2$ and $n = 3$ representability characterizations by the same ZMod certificate.
- A uniform statement over the finite list of class-number-one discriminants.

### Our Goal

Prove $p = a^2 + 2b^2 \iff p \equiv 1,3 \pmod 8$ (and, as a stretch, $n = 3$), reusing the parent's `ZMod`-based residue-decidability step and a norm-form descent in $\mathbb{Z}[\sqrt{-n}]$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bezout-identity two-squares (parent) | direct template | ZMod decidability, Thue descent |
| gaussian-integers norm forms | norm-multiplicativity | ring norm, unique factorization |

## Initial Thoughts

### Potential Approaches

1. **Norm-form descent in ℤ[√-n]**: mirror the parent's Thue-lemma / descent, replacing the Gaussian norm $a^2+b^2$ by $a^2 + n b^2$.
   - Why it might work: for $n \in \{2,3\}$ the ring is a PID, so the descent closes.
   - Risk: Mathlib's `Zsqrtd` API is thinner for $\sqrt{-n}$ than for Gaussian integers.

2. **Legendre-symbol + decidable residue check** for the "only if" direction via `ZMod p`.
   - Why it might work: `decide` handles the finite residue condition, as in the parent.
   - Risk: the "if" direction still needs the descent lemma.

### Key Difficulties

- Availability of `Zsqrtd (-2)`, `Zsqrtd (-3)` norm and factorization lemmas in Mathlib.
- Ramified primes $p \mid 2n$ and the prime $p = n$ boundary cases.

### What Would a Proof Need?

- Key lemma 1: quadratic-reciprocity / Legendre value of $(-n/p)$.
- Key lemma 2: norm-form descent (a solution mod $p$ lifts to $a^2 + n b^2 = p$).
- Technical requirements: `Zsqrtd`, `ZMod`, `legendreSym`, `Nat.Prime`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The $n = 2$ case is norm-Euclidean, so the parent's descent structure transfers.
- The decidable residue certificate is a proven, reusable pattern from the parent.
- Risk concentrated in Mathlib `Zsqrtd (-2)` coverage; may need a hand-rolled norm.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable (n = 2): 4–6 days
- If hard (uniform n): unknown

## References

### Papers
- D. A. Cox, Primes of the form x² + n y² (1989).

### Online Resources
- https://en.wikipedia.org/wiki/Fermat%27s_theorem_on_sums_of_two_squares — and its x²+2y², x²+3y² analogues.

### Mathlib
- `Mathlib.NumberTheory.Zsqrtd.Basic` — quadratic-integer norms.
- `Mathlib.NumberTheory.LegendreSymbol.Basic` — Legendre symbol and reciprocity.

## Metadata

```yaml
tags:
  - number-theory
  - gaussian-integers
  - sum-of-two-squares
  - modular-arithmetic
  - prime-classification
related_proofs:
  - bezout-identity
  - gaussian-integers
difficulty: medium
source: gallery-gap
created: 2026-07-01
```

**Significance**: 6/10
**Tractability**: 6/10

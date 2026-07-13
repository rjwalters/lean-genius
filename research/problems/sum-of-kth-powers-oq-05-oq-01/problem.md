# Problem: Nat-Congruence Power-Sum Dichotomy mod p

**Slug**: sum-of-kth-powers-oq-05-oq-01
**Created**: 2026-06-23
**Status**: Active
**Source**: gallery-gap <!-- open question of verified parent sum-of-kth-powers-oq-05 (ZMod p power-sum dichotomy) -->

## Problem Statement

### Formal Statement

For a prime $p$ and an exponent $k \in \mathbb{N}$:

$$
\sum_{i=0}^{p-1} i^{\,k} \;\equiv\;
\begin{cases}
p - 1 \pmod{p}, & k \neq 0 \ \text{and}\ (p-1) \mid k,\\[2pt]
0 \pmod{p}, & \text{otherwise,}
\end{cases}
$$

as a congruence of **natural numbers** (`Nat.ModEq`). The parent entry `sum-of-kth-powers-oq-05` establishes the corresponding equality in $\mathbb{Z}/p\mathbb{Z}$:
$$
\sum_{i \in \mathbb{Z}/p\mathbb{Z}} i^{k} = \begin{cases} -1 & (p-1)\mid k,\ k\ne 0\\ 0 & \text{otherwise.}\end{cases}
$$
This open question asks to **cast that `ZMod p` dichotomy back to a congruence over $\mathbb{N}$** via `Nat.ModEq`, giving the elementary "sum of $k$-th powers mod $p$" statement (with $-1$ becoming $p-1$).

### Plain Language

Add up $0^k + 1^k + 2^k + \cdots + (p-1)^k$ and reduce mod a prime $p$. The result is almost always $0$ — *except* in the special case where the exponent $k$ is a nonzero multiple of $p-1$, when it is $-1 \equiv p-1$. (This is exactly why Fermat's little theorem makes $i^{p-1}\equiv 1$, so the sum becomes $p-1$ copies of $1$.) The parent proves this inside the finite field $\mathbb{Z}/p\mathbb{Z}$; here we want the same fact stated as an ordinary congruence about natural-number sums, which is the form most textbooks and applications use.

### Why This Matters

The $\mathbb{N}$-congruence form is the directly usable one for elementary number theory: it underlies the von Staudt–Clausen theorem (the $p$-integral part of Bernoulli numbers), Carlitz-style power-sum arguments, and the standard "$\sum i^{p-1} \equiv -1$" lemma used in primality and Wilson-type results. The translation from a `ZMod p` field identity to a `Nat.ModEq` statement is a recurring formalization pattern (cast the sum, push the field equality through `ZMod.natCast_self_eq_zero` / `ZMod.natCast_zmod_eq_zero_iff_dvd`), so doing it cleanly here yields a template reusable across the gallery's modular-arithmetic corpus.

### Why This Matters (cont.)

It also closes the loop on the parent: a field-level dichotomy is mathematically complete but pedagogically incomplete until it is expressed in the elementary language of integer congruences, which is where most readers and downstream proofs operate.

## Known Results

### What's Already Proven

- The `ZMod p` power-sum dichotomy $\sum_{i:\mathbb{Z}/p} i^k \in \{0,-1\}$ — gallery parent `sum-of-kth-powers-oq-05`.
- Fermat's little theorem / `ZMod.pow_card_sub_one_eq_one`, and the multiplicative-group structure of $(\mathbb{Z}/p)^\times$ — Mathlib.
- Bridges between `Nat`/`Int` sums and `ZMod p`: `ZMod.natCast_self_eq_zero`, `ZMod.natCast_zmod_eq_zero_iff_dvd`, `Nat.cast_sum`, `ZMod.natCast_val` — Mathlib.
- `Nat.ModEq` API (`Nat.modEq_iff_dvd'`, `Nat.ModEq.sub`, cast lemmas) — Mathlib.

### What's Still Open (here)

- The natural-number congruence statement $\sum_{i<p} i^k \equiv (\text{if } k\ne0 \wedge (p-1)\mid k \text{ then } p-1 \text{ else } 0) \pmod p$.
- The careful handling of $-1 \mapsto p-1$ under the cast (and the $k=0$ edge case, where the sum is $p \equiv 0$).

### Our Goal

Ship the `Nat.ModEq` corollary as a verified theorem, derived from the parent's `ZMod p` equality by mapping the finite sum $\sum_{i<p} i^k$ over $\mathbb{N}$ into $\mathbb{Z}/p\mathbb{Z}$ (using the bijection `Finset.range p ↔ ZMod p`), invoking the parent dichotomy, and translating $-1$ and $0$ back to $p-1$ and $0$ in $\mathbb{N}$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sum-of-kth-powers-oq-05 | direct parent (ZMod p dichotomy) | `ZMod`, Fermat's little theorem, character sums |
| sum-of-kth-powers | base Faulhaber/power-sum API | `Finset.sum`, induction |
| wilsons-theorem-oq-05 | sibling ℕ-congruence-from-ZMod casting pattern | `ZMod.natCast_zmod_eq_zero_iff_dvd`, `Nat.ModEq` |

## Initial Thoughts

### Potential Approaches

1. **Cast-and-transport** (primary): Show $\big(\sum_{i<p} i^k : \mathbb{Z}/p\big) = \sum_{x:\mathbb{Z}/p} x^k$ by reindexing `Finset.range p` along the canonical bijection with `ZMod p` (`ZMod.natCast` is a bijection on residues), then substitute the parent equality. Finally convert "$=0$ in `ZMod p`" to "$p \mid \cdot$" via `ZMod.natCast_zmod_eq_zero_iff_dvd`, and "$=-1$" to "$\equiv p-1$" via `Nat.modEq_iff_dvd'`.
   - Why it might work: it is a direct application of the parent plus standard cast lemmas.
   - Risk: the reindexing bijection bookkeeping (`Finset.sum_bij` / `ZMod.sum_univ` style) and the $-1 \mapsto p-1$ congruence step need care.

2. **Independent ℕ proof via Fermat** (fallback): split $i=0$ off, use $i^{p-1}\equiv1$ for $i\ne0$ when $(p-1)\mid k$, else pair terms via a primitive root to show cancellation — re-deriving rather than transporting.
   - Why it might work: avoids the bijection plumbing.
   - Risk: duplicates the parent's work; the non-divisible case needs the primitive-root cancellation argument.

### Key Difficulties

- The residue bijection `Finset.range p ≃ ZMod p` and matching the two sums.
- Translating the field value $-1$ to the natural number $p-1$ as a `Nat.ModEq`.
- $k=0$ edge case ($\sum_{i<p} 1 = p \equiv 0$, consistent with "otherwise" branch since the guard requires $k\ne0$).

### What Would a Proof Need?

- Key lemma 1: $\sum_{i<p}(i:\mathbb{Z}/p)^k = \sum_{x:\mathbb{Z}/p} x^k$ (sum reindex over the residue bijection).
- Key lemma 2: parent dichotomy on $\sum_{x:\mathbb{Z}/p} x^k$.
- Technical requirements: `ZMod.natCast_zmod_eq_zero_iff_dvd`, `Nat.modEq_iff_dvd'`, `Nat.cast_sum`, `Fact p.Prime`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is fully supplied by the parent; the work is a casting/transport exercise.
- The `ZMod p` ↔ `Nat.ModEq` translation is a well-trodden pattern in sibling gallery entries (Wilson-family proofs).
- The only nontrivial step is the residue-bijection reindexing of the sum.

**Estimated Effort**:
- Exploration: 2–3 hours
- If tractable: one to two days

## References

### Papers
- Ireland & Rosen, *A Classical Introduction to Modern Number Theory*, Ch. 4 — power sums mod p and Bernoulli congruences.
- von Staudt–Clausen theorem (classical) — the $p$-integral part of Bernoulli numbers.

### Online Resources
- Standard "sum of k-th powers modulo a prime" lemma in elementary number theory notes.

### Mathlib
- `Mathlib.FieldTheory.Finite.Basic` — `ZMod.pow_card_sub_one_eq_one`, finite-field power-sum facts.
- `Mathlib.Data.ZMod.Basic` — `ZMod.natCast_zmod_eq_zero_iff_dvd`, residue casts.
- `Mathlib.Data.Nat.ModEq` — `Nat.ModEq`, `Nat.modEq_iff_dvd'`.

## Metadata

```yaml
tags:
  - number-theory
  - finite-fields
  - power-sums
  - modular-arithmetic
  - zmod
related_proofs:
  - sum-of-kth-powers-oq-05
  - sum-of-kth-powers
difficulty: medium
source: gallery-gap
created: 2026-06-23
```

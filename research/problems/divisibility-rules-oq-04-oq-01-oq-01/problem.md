# Problem: Uniform parametric divisibility criterion for base-groupings b′ ≡ ±1 (mod m)

**Slug**: divisibility-rules-oq-04-oq-01-oq-01
**Created**: 2026-07-04T23:13:04-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $b = 10$ (or an arbitrary base), fix a block width $k \ge 1$, and write $b' = b^k$.
Every natural number $N$ has a base-$b'$ digit expansion $N = \sum_{i=0}^{L} d_i\, (b')^i$
with $0 \le d_i < b'$ (the digits $d_i$ are the $k$-digit blocks of $N$ in base $b$).
For a modulus $m$ with $\gcd(m, b) = 1$:

$$
\text{if } b' \equiv 1 \pmod m: \qquad m \mid N \iff m \mid \sum_i d_i \quad(\text{plain block sum})
$$
$$
\text{if } b' \equiv -1 \pmod m: \qquad m \mid N \iff m \mid \sum_i (-1)^i d_i \quad(\text{alternating block sum})
$$

**Goal:** prove a *single* parametric lemma, quantified over the sign $\varepsilon \in \{+1,-1\}$
and the block width $k$, from which the classical rules for $3, 9$ ($b'=10$, $\varepsilon=+1$),
$11$ ($b'=10$, $\varepsilon=-1$), $99$/$101$ ($b'=100$), $999$/$1001$ ($b'=1000$, giving the
$7\mid$, $11\mid$, $13\mid$ rules), … all follow as instances.

### Plain Language

The familiar "casting out nines" rule (a number is divisible by 9 iff its digit sum is) and
the alternating-digit rule for 11 are two faces of one fact: when you group the base-10 digits
into blocks of $k$ and the block-base $10^k$ is $\equiv \pm 1$ modulo $m$, divisibility by $m$
is decided by a signed sum of the blocks. We want to state and prove this once, in full
generality, so that every member of the $9/11/99/101/999/1001/\dots$ family is a corollary
obtained by choosing $k$, the sign, and $m$.

### Why This Matters

The gallery already contains the individual rules and the parent's $b' \equiv \pm 1$ observation.
Consolidating them into one reusable, parametrized theorem (a) removes duplication, (b) exposes
the true content — a congruence $(b')^i \equiv \varepsilon^i \pmod m$ pushed through the digit
expansion — and (c) gives a clean building block for future base-conversion / divisibility work.
It is a self-contained modular-arithmetic result with strong Mathlib support.

## Known Results

### What's Already Proven

- **divisibility-rules-oq-04-oq-01** (verified, `mathlib` badge) — parent establishing the
  block-grouping scheme and the $b' \equiv \pm 1 \pmod m$ dichotomy for specific cases.
- **divisibility-rules** and its `oq-01…`, `oq-02…` descendants — the base-10 rules for
  $3, 9, 11$ and base-changing variants.
- Mathlib: `Nat.ModEq`, `Int.ModEq`, `Nat.ofDigits`, `Nat.ofDigits_modEq`,
  `Nat.modEq_digits_sum`, `Nat.modEq_three_digits_sum`, `Nat.modEq_nine_digits_sum`,
  `Nat.modEq_eleven_digits_sum`, `Finset.sum`, `Finset.geom_sum` machinery.

### What's Still Open

- No single Lean lemma currently unifies both signs and arbitrary block widths $k$.
- The block-digit (base-$b^k$) reindexing of the base-$b$ expansion is not packaged as a reusable
  bridge in this gallery line.

### Our Goal

Prove one theorem of roughly the shape:

```
theorem modEq_block_signed_sum
    (b k m : ℕ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hbk : (b ^ k : ℤ) ≡ ε [ZMOD m]) (digits : List ℕ) :
    (Nat.ofDigits (b ^ k) digits : ℤ)
      ≡ ∑ i, ε ^ i * (digits.get i : ℤ) [ZMOD m]
```

and then derive the $9$, $11$, $99$, $101$, $7/11/13$ (via $1001$) rules as `example`s.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| divisibility-rules-oq-04-oq-01 | direct parent; block-grouping dichotomy | `Nat.ModEq`, digit sums |
| divisibility-rules | base rules for 3/9/11 | `Nat.ofDigits_modEq` |
| divisibility-rules-oq-02 | base-change variants | modular arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Approach A — `ofDigits` + termwise congruence**: work in `ℤ` with `Int.ModEq`. From
   `(b^k) ≡ ε [ZMOD m]` get `(b^k)^i ≡ ε^i [ZMOD m]` by `Int.ModEq.pow`, then push through
   `Nat.ofDigits (b^k) digits = ∑ digitsᵢ · (b^k)^i` termwise via `Finset.sum_congr` /
   `List.sum` `ModEq` lemmas. Mirrors Mathlib's own proofs of `modEq_digits_sum`.
   - Why it might work: this is exactly how Mathlib proves the 3/9/11 rules; we only
     abstract the base to `b^k` and the residue to `ε`.
   - Risk: index bookkeeping between `List`/`Finset.range` forms of `ofDigits`.

2. **Approach B — reduce to Mathlib's `Nat.modEq_digits_sum` after base change**: express the
   base-$b^k$ digits as blocks of base-$b$ digits and reuse `Nat.ofDigits_append` /
   `Nat.ofDigits_digits`.
   - Why it might work: leverages existing lemmas directly.
   - Risk: the block-reindexing of digits may be fiddlier than proving termwise from scratch.

### Key Difficulties

- Choosing `ℤ`/`ZMOD` vs `ℕ`/`Nat.ModEq` so the alternating ($\varepsilon = -1$) case is clean
  (signs force `ℤ`).
- Relating `Nat.ofDigits` (list form) to `∑ i in Finset.range n` (indexed form).

### What Would a Proof Need?

- Key lemma 1: `(b^k : ℤ) ≡ ε [ZMOD m] → (b^k)^i ≡ ε^i [ZMOD m]` (immediate from `Int.ModEq.pow`).
- Key lemma 2: termwise `ModEq` for `Nat.ofDigits`/`List.sum` (Mathlib has the ℕ analogue).
- Corollary instantiations for $m \in \{3,9,11,99,101,7,13\}$ with explicit $k, \varepsilon$.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The result is a direct abstraction of proofs already in Mathlib (`modEq_nine_digits_sum`,
  `modEq_eleven_digits_sum`); the mathematical content is a one-line congruence pushed through
  a finite sum.
- Strong Mathlib support: `Nat.ofDigits`, `Int.ModEq`, `Int.ModEq.pow`, `Finset.sum` congruence.
- Main effort is API plumbing (list vs indexed digit forms), not new mathematics.

**Estimated Effort**:
- Exploration: a few hours (locate the right `ofDigits`/`ModEq` lemmas).
- If tractable: 1–3 days for the parametric theorem plus the corollary family.

## References

### Mathlib
- `Mathlib.Data.Nat.Digits` — `Nat.ofDigits`, `Nat.ofDigits_modEq`, `Nat.modEq_digits_sum`,
  `Nat.modEq_nine_digits_sum`, `Nat.modEq_eleven_digits_sum`.
- `Mathlib.Data.Int.ModCast` / `Mathlib.Data.Int.GCD` — `Int.ModEq`, `Int.ModEq.pow`.

### Online Resources
- Standard number-theory texts on divisibility tests (casting out nines, the 1001 = 7·11·13 rule).

## Metadata

```yaml
tags:
  - number-theory
  - divisibility
  - modular-arithmetic
  - base-representation
related_proofs:
  - divisibility-rules-oq-04-oq-01
  - divisibility-rules
difficulty: low
source: gallery-gap
created: 2026-07-04T23:13:04-07:00
```

**Significance**: 5/10
**Tractability**: 7/10

# Problem: Automorphic Numbers and the Four Idempotents mod 10^k

**Slug**: automorphic-number-oq-01
**Created**: 2026-06-16
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

A residue $n$ with $1 \le n < 10^k$ is *$k$-automorphic* if
$$
n^2 \equiv n \pmod{10^k}.
$$
Equivalently $n$ is an idempotent of the ring $\mathbb{Z}/10^k\mathbb{Z}$. Since
$10^k = 2^k\cdot 5^k$ with $\gcd(2^k,5^k)=1$, the CRT isomorphism
$$
\mathbb{Z}/10^k\mathbb{Z} \;\cong\; \mathbb{Z}/2^k\mathbb{Z} \times \mathbb{Z}/5^k\mathbb{Z}
$$
shows the idempotents are exactly the four elements $(e_2, e_5)$ with
$e_2 \in \{0,1\}$, $e_5 \in \{0,1\}$. Hence for every $k \ge 1$ there are exactly
four solutions mod $10^k$: $0$, $1$, and two nontrivial ones (the $k$-digit
automorphic numbers, ending in $5$ and $6$ respectively).

### Plain Language

$5^2 = 25$, $6^2 = 36$, $25^2 = 625$, $76^2 = 5776$, $376^2 = 141376$: each
square ends in the original number. We want a machine-checked proof that, modulo
$10^k$, exactly four numbers square to themselves, via the Chinese Remainder
Theorem, and that this characterizes the automorphic numbers.

### Why This Matters

A clean application of CRT and idempotent theory in $\mathbb{Z}/n\mathbb{Z}$. The
count of idempotents equals $2^{\omega(n)}$ ($\omega$ = number of distinct
primes); here $\omega(10^k)=2$ gives exactly four. Nice bridge from recreational
"automorphic numbers" to ring theory.

## Known Results

### What's Already Proven

- In any commutative ring, idempotents of a product split componentwise.
- $\mathbb{Z}/p^k\mathbb{Z}$ (prime power) is local, so its only idempotents are
  $0$ and $1$.
- CRT: `ZMod (m*n) ≃+* ZMod m × ZMod n` for coprime $m,n$ is in Mathlib
  (`ZMod.chineseRemainder`).

### What's Still Open (engineering)

- No gallery/Lean statement assembling these into "exactly four automorphic
  residues mod 10^k".

### Our Goal

Prove `{n : ZMod (10^k) | n^2 = n}` has cardinality exactly $4$ for $k \ge 1$,
using `ZMod.chineseRemainder` (split $10^k = 2^k \cdot 5^k$) and the fact that
$\mathbb{Z}/p^k\mathbb{Z}$ has exactly two idempotents. Optionally exhibit the two
nontrivial sequences ($\dots625$ and $\dots376$) via Hensel lifting.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| kaprekar-constant-oq-01 | digit-based decidable number theory | digits, finite reasoning |
| perfect-numbers | divisor/structure characterization | number theory |

## Initial Thoughts

### Potential Approaches

1. **CRT + local-ring idempotents**: transport `x^2 = x` across
   `ZMod.chineseRemainder`; reduce to counting idempotents in `ZMod (2^k)` and
   `ZMod (5^k)`, each exactly $\{0,1\}$.
   - Why it might work: all pieces exist in Mathlib.
   - Risk: showing `ZMod (p^k)` has only two idempotents may need the local-ring
     /nilpotent characterization.

2. **Hensel lifting** to construct the nontrivial idempotent explicitly mod $5^k$
   (the $\dots625$ family) and mod $2^k$.

### Key Difficulties

- Proving `ZMod (p^k)` has exactly two idempotents (no nontrivial ones): use that
  $x(x-1)=0$ with $x, x-1$ in a local ring forces $x \in \{0,1\}$.
- Bookkeeping the bijection between idempotents of a product and pairs.

### What Would a Proof Need?

- `idempotents (ZMod (p^k)) = {0, 1}` for prime $p$.
- `ZMod.chineseRemainder` transport of the idempotent equation.
- Cardinality `= 2 * 2 = 4`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Core tools (`ZMod.chineseRemainder`, local rings, idempotents) are in Mathlib.
- The two-idempotents-in-`ZMod (p^k)` lemma is the main piece of real work.

**Estimated Effort**:
- Exploration: hours–1 day
- If tractable: 3–5 days

## References

### Online Resources
- OEIS A003226 (automorphic numbers) — context.

### Mathlib
- `Mathlib.Data.ZMod.Basic`, `ZMod.chineseRemainder` — CRT isomorphism.
- `IsIdempotentElem`, local ring / nilpotent lemmas — idempotent counting.

## Metadata

```yaml
tags:
  - number-theory
  - digits
  - automorphic
  - idempotent
  - crt
  - p-adic
related_proofs:
  - kaprekar-constant-oq-01
  - perfect-numbers
difficulty: medium
source: gallery-gap
created: 2026-06-16
```

# Problem: p-adic Valuation of Binomial Coefficients via Kummer's Theorem

**Slug**: kummer-theorem-oq-01-oq-01
**Created**: 2026-04-21T21:54:10+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
v_p\!\left(\binom{m+n}{m}\right) = c_p(m, n)
$$

where $v_p$ is the p-adic valuation and $c_p(m, n)$ is the number of carries when adding $m$ and $n$ in base $p$.

Equivalently:

$$
v_p\!\left(\binom{m+n}{m}\right) = \frac{s_p(m) + s_p(n) - s_p(m+n)}{p-1}
$$

where $s_p(k)$ is the digit sum of $k$ in base $p$.

### Plain Language

Kummer's theorem (1852) states that the exact power of a prime p dividing the binomial coefficient C(m+n, m) equals the number of carries when adding m and n in base p. Formalize this in Lean 4 using Mathlib's `padicValNat` and `Nat.digits`.

### Why This Matters

- Fundamental result connecting p-adic valuations to combinatorics
- Key ingredient in Granville's proof of ABC conjecture implications
- Used in proofs of Lucas' theorem for prime powers (Granville's generalization)
- The digit-sum formulation connects to information theory

## Known Results

### What's Already Proven

- `Nat.Prime.dvd_choose_iff`: divisibility of binomials by primes — in Mathlib
- `padicValNat`: p-adic valuation for naturals — in Mathlib
- `Nat.digits`: base-p digit representation — in Mathlib
- `kummer-theorem`: Kummer's theorem in gallery (axiomatized)
- `kummer-theorem-oq-01`: Multinomial analog in gallery

### What's Still Open

- Full Lean formalization: `padicValNat p (Nat.choose (m+n) m) = numCarriesBaseP p m n`
- A formal definition of "number of carries when adding in base p"

### Our Goal

Formalize: `padicValNat p (n.choose k) = numCarriesBaseP p k (n-k)` where `numCarriesBaseP` is defined via digit arithmetic, and provide a complete Lean 4 proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| kummer-theorem | Direct parent: Kummer's theorem stated | padicValNat, Nat.digits |
| kummer-theorem-oq-01 | Multinomial analog | Nat.multinomial |
| lucas-theorem | Related: Lucas' theorem for C(n,k) mod p | ZMod, Nat.digits |
| pascals-hexagon | Related combinatorial identity | Finset, choose |

## Initial Thoughts

### Potential Approaches

1. **Digit-sum approach via Legendre's formula**:
   - Legendre: v_p(n!) = (n - s_p(n)) / (p-1)
   - Then v_p(C(m+n,m)) = [s_p(m) + s_p(n) - s_p(m+n)] / (p-1)
   - Why it might work: Legendre's formula may be in Mathlib
   - Risk: Connecting digit sums to carry count

2. **Direct induction on carries**:
   - Define carry sequence; induct on number of digits
   - Risk: Requires careful base-p arithmetic formalism

3. **Via existing Mathlib lemmas**:
   - Search for `padicValNat` + `choose` lemmas in Mathlib
   - May find partial results to compose

### Key Difficulties

- No Lean formalization of "number of base-p carries" exists yet in Mathlib
- Proving carry count equals digit sum difference requires careful induction
- Edge cases: p=2, m=0, n=0

### What Would a Proof Need?

- Key definition: `def numCarries (p m n : ℕ) : ℕ` counting carries in base-p addition
- Key lemma 1: `numCarries p m n = (digitSum p m + digitSum p n - digitSum p (m+n)) / (p-1)`
- Key lemma 2: `padicValNat p (n.factorial) = (n - digitSum p n) / (p-1)` (Legendre)
- Key lemma 3: Combine Legendre for v_p(C(m+n,m))

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Legendre's formula may not be directly in Mathlib (worth searching)
- The carry definition requires a non-trivial auxiliary definition
- All arithmetic is elementary but bookkeeping is careful
- Mathlib has `Nat.digits` infrastructure that helps

**Estimated Effort**:
- Exploration: 4-8 hours
- If tractable: 3-5 days for complete proof

## References

### Papers
- Kummer, E.E. "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen" (1852)
- Granville, A. "Binomial coefficients modulo prime powers" (1997)

### Mathlib
- `Mathlib.Data.Nat.Digits` — `Nat.digits`, digit sums
- `Mathlib.NumberTheory.Padics.PadicVal` — `padicValNat`
- `Mathlib.Data.Nat.Choose.Basic` — binomial coefficient lemmas

## Metadata

```yaml
tags:
  - number-theory
  - p-adic
  - combinatorics
  - kummer-theorem
  - binomial-coefficients
related_proofs:
  - kummer-theorem
  - kummer-theorem-oq-01
  - lucas-theorem
difficulty: medium
source: gallery-gap
created: 2026-04-21T21:54:10+02:00
```

**Significance**: 7/10
**Tractability**: 7/10
